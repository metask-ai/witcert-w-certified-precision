# -*- coding: utf-8 -*-
"""产物 provenance 的**单一入口**:一个 stamp() 决定所有产物怎么记来源。

## 为什么需要它(2026-08-06 评审 A1/A2/A3)

此前仓里并存两套互不相交的 schema:
  · env/PROVENANCE.md 规定的顶层 `machine`/`stack` —— 33/525 个产物遵守;
  · launcher 各自手拼的 `manifest.code` —— 222/525 个产物遵守。
两者交集**只有 1 个文件**,271 个产物两套都没有。四个 launcher 各写一遍
`os.environ.get("WC_CODE_HASH", "unset")`,字段集合互不相同(ruler_ab 有 seed,
p111 没有;hisparse 把 machine 写在顶层,别人写在 manifest 里)。

更重的一条:`code` 记的是 `git rev-parse HEAD`,而 run_remote.sh 同步的是
**工作树**。仓内有 6 个活跃 worktree、CLAUDE.md §6 明载并行会话 —— 脏树发射时
那个 hash 描述的是一个**并没有跑过的 commit**。指纹必须是测量,不能是声明,
所以本模块除 `code`(HEAD)外还记 `tree`(实际同步内容的摘要)与 `dirty`。

## 设计:stamp() 永不抛异常

不对称代价决定的(CLAUDE.md 调查期纪律 9):stamp 在 launcher 尾部调用,此时
GPU 已经跑了几十分钟。抛异常 = 拿不到产物且损失全部机时;记 "unset" = 产物照落,
本地秒级守卫 tests/test_provenance.py 当场判红,只需重跑**盖章**而非重跑实验。
所以:**仪器如实记录它测到的,判红由守卫承担**(与 flagship_gate 三态同构)。

## 用法

launcher 内联 python 里:

    import os, sys
    sys.path.insert(0, os.environ.get("WC_EXP_DIR", "experiments"))
    from provenance import stamp

    manifest = stamp(run_id="$RUN_ID", seed=42, arm="$ARM",
                     stack="sglang 0.5.13.post1, tp8+ep8, ctx 65536")
    manifest.update({"model": MODEL, "tp": 8})       # 实验特有字段照旧自己加
    json.dump({"docs": res, "manifest": manifest}, open(dst, "w"))

机器侧字段(machine / code / tree / dirty)由 tools/run_remote.sh 发射时经
WC_* 环境变量注入 —— 远端副本按仓规**没有 .git**,在那 `git rev-parse` 只会
得到宿主机上另一个仓的答案,比 "unset" 更坏。

    python3 experiments/provenance.py --tree-digest   # run_remote.sh 调用
    python3 experiments/provenance.py --show          # 自查当前环境能盖出什么章
"""
import datetime
import hashlib
import os
import sys

#: schema 版本。字段语义变更时 +1,守卫据此区分"旧 schema"与"漏字段"。
SCHEMA = "wc-prov/1"

#: 核心字段:每个运行产物都必须有。守卫按这张表查,不按 launcher 各自的习惯查。
CORE = ("schema", "machine", "stack", "code", "tree", "dirty",
        "run_id", "seed", "started_at")

#: 参与代码指纹的子树 —— 必须与 run_remote.sh 的 rsync 范围一致,
#: 否则指纹会声称覆盖了没同步过去的东西。
SYNCED = ("src", "experiments")

#: 指纹排除项:out*/data 是产物与语料(不是代码,且体量大),
#: __pycache__ 是字节码(rsync 前已清,算进来只会让指纹随机跳动)。
EXCLUDE_DIRS = {"out", "out_siteB", "data", "__pycache__", "launchers/logs"}


def _iter_files(root):
    """按 rsync 的实际范围枚举参与指纹的文件,顺序与平台无关。"""
    for sub in SYNCED:
        base = os.path.join(root, sub)
        if not os.path.isdir(base):
            continue
        for dirpath, dirnames, filenames in os.walk(base):
            dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
            for fn in sorted(filenames):
                if fn.endswith((".pyc", ".pyo")) or fn == ".DS_Store":
                    continue
                yield os.path.join(dirpath, fn)


def tree_digest(root=None):
    """实际会被同步到远端的那份代码的内容摘要(12 hex)。

    这是 provenance 里唯一**测量**性质的字段:git sha 描述的是 HEAD,
    而跑的是工作树;两者在脏树下不是一回事。摘要覆盖路径与内容,
    因此两次脏树发射只要内容不同,指纹就不同 —— 事后可以判别。
    """
    root = root or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    h = hashlib.sha256()
    for path in _iter_files(root):
        try:
            with open(path, "rb") as f:
                body = f.read()
        except OSError:
            continue                      # 读不到就不算,不让指纹计算本身失败
        rel = os.path.relpath(path, root).replace(os.sep, "/")
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(hashlib.sha256(body).hexdigest().encode("ascii"))
        h.update(b"\n")
    return h.hexdigest()[:12]


def _env(name, default=None):
    v = os.environ.get(name)
    return v if v not in (None, "") else default


def _int_or_none(v):
    try:
        return int(v)
    except (TypeError, ValueError):
        return None


def _witcert_env():
    return {k: v for k, v in sorted(os.environ.items())
            if k.startswith("WITCERT_")}


def stamp(run_id=None, seed=None, stack=None, arm=None, adapters=None,
          **extra):
    """盖一枚 provenance 章。**不抛异常** —— 测不到的如实记 unset/None。

    机器侧字段优先取 WC_* 注入值(run_remote.sh 发射时算好);本地直跑时
    退化到就地计算(本机有 .git,算得准)。远端**不**就地算 git ——
    远端副本按仓规无 .git,那里的 rev-parse 答的是别的仓。
    """
    code = _env("WC_CODE_HASH")
    tree = _env("WC_TREE")
    dirty_env = _env("WC_DIRTY")

    if code is None and tree is None:
        # 本机直跑(无 run_remote 注入):就地测,别记 unset
        local = _local_git()
        code, tree, dirty_env = local["code"], local["tree"], local["dirty"]

    st = {
        "schema": SCHEMA,
        "machine": _env("WC_MACHINE", "unset"),
        "stack": stack or _env("WC_STACK", "unset"),
        "code": code or "unset",
        "tree": tree or "unset",
        # 三态:True 脏 / False 干净 / None 不知道。不知道**不当干净**
        # (装饰性的 False 会让守卫误以为这次发射可信)。
        "dirty": {"1": True, "0": False}.get(dirty_env),
        "run_id": run_id or _env("RUN_ID", "unset"),
        "seed": seed if seed is not None else _int_or_none(_env("SEED")),
        "started_at": datetime.datetime.now(
            datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "witcert_env": _witcert_env(),
        "adapters": adapters if adapters is not None
        else _env("WC_APPLIED_ADAPTERS", ""),
    }
    if arm is not None:
        st["arm"] = arm
    st.update(extra)
    return st


def _local_git():
    """本机就地测 code/tree/dirty。仅在无 WC_* 注入时使用。"""
    import subprocess
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    out = {"code": None, "tree": None, "dirty": None}
    try:
        # `git -C <无 .git 的目录>` **会沿祖先目录继续找**(实测:在 rsc/experiments
        # 下问 HEAD 会答 rsc 的 HEAD)。远端副本按仓规无 .git,若 /data 或 /
        # 恰是某个仓,这里就会答出一个像模像样但完全无关的 sha —— 比 unset 更坏,
        # 因为它看不出错。故先确认找到的仓就是本仓,不是则整个放弃 git 侧字段。
        top = subprocess.check_output(
            ["git", "-C", root, "rev-parse", "--show-toplevel"],
            stderr=subprocess.DEVNULL).decode().strip()
        if os.path.realpath(top) == os.path.realpath(root):
            out["code"] = subprocess.check_output(
                ["git", "-C", root, "rev-parse", "--short", "HEAD"],
                stderr=subprocess.DEVNULL).decode().strip()
            # dirty = **生成代码**是否未提交,不含输出产物:experiments/out/ 的产物
            # 变化不影响生成代码的可复现性。排除它根治"重生产物反复把 stamp 盖脏"
            # (2026-08-08 复发+历史累积 4 个脏 canon 源;canon-source-restamped-dirty)。
            # 代码改动(src/、experiments/*.py)仍在 scope,照常 flag。
            porcelain = subprocess.check_output(
                ["git", "-C", root, "status", "--porcelain", "--"]
                + list(SYNCED) + [":(exclude)experiments/out"],
                stderr=subprocess.DEVNULL).decode().strip()
            out["dirty"] = "1" if porcelain else "0"
            if porcelain:
                out["code"] += "-dirty"
        # 找到的是别的仓:git 侧字段全部留 None(记 unset),但 tree 照算 ——
        # 内容摘要不依赖 git,是这种情形下唯一还能测准的指纹
    except (OSError, subprocess.CalledProcessError):
        pass                              # 不是 git 工作区:字段留 None
    try:
        out["tree"] = tree_digest(root)
    except OSError:
        pass
    return out


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--tree-digest" in argv:
        print(tree_digest())
        return 0
    if "--show" in argv:
        import json
        print(json.dumps(stamp(), ensure_ascii=False, indent=1))
        return 0
    print(__doc__.strip().splitlines()[0])
    print("用法: provenance.py --tree-digest | --show")
    return 2


if __name__ == "__main__":
    sys.exit(main())

# witcert-w-certified-precision

Artifacts, guards, and machine-checked proofs for the paper
**"Pricing the Risk of Runtime Compression: Anytime-Valid Admission and a
Served-Output Law for Compressed Serving State"** (Fanzhe Wei, Li Liu),
arXiv:2608.15810 — <https://arxiv.org/abs/2608.15810>.

The paper is an account of what a serving system can *spend*: a risk budget
that survives free-running decoding, a law that converts a certified witness
into a served-output target, and the measured cost of every layer between a
compression decision and a served token.

## What this repository verifies, and what it does not

```bash
python3 tests/test_paper_claims.py   # stdlib only, seconds, no GPU
python3 tools/p3_figs.py             # regenerate every figure from raw captures
```

The second command needs `matplotlib` (see `requirements.txt`); the first
needs nothing but the Python standard library.

This checks that **every number in `main.tex` traces to the frozen evidence
ledger** (`papers/p1-kv-certificates/canon.json` — a project-wide file whose
name is historical), that no retracted value reappears, that the figure data
is drawn from the same source as the prose, and that every theorem name cited
in the text exists in the Lean export.

It does **not** re-derive the ledger from raw captures. Doing that needs the
full monorepo, including the other papers' runs; a single-paper artifact
repository is the wrong place for it. What ships here instead is the frozen
ledger *with each entry's source artifact path*, plus those artifacts
(`experiments/out/`, list mechanically derived in
`papers/p3-witcert-v/artifacts.list`) — so any entry can be checked by hand
against the run it came from.

## The Lean development

```bash
cd formal && bash check_standalone.sh   # seconds, no Mathlib
cd formal && bash check_all.sh          # full, needs `lake exe cache get`
```

228 exported theorems, no `sorry`. `papers/p3-witcert-v/theorems.json` is
**compiled** from the development by `tools/lean_extract.py`, not transcribed
— a statement that is not proved cannot appear in it. The paper's proof chain
(per-step moment bound → served-output TV → Bernoulli domination → Ville) is
the solid part of Figure 6; the dotted boxes there are measured or open, and
the paper says which is which.

## Scope, stated plainly

The model-side propagation constants a tensorized proof would need are
**measured and falsified**, not bounded — the first-order surrogate does not
hold (Figure 2). The conformal population is a pool we constructed, not
runtime traffic. Both limits are in the paper's Limitations section, and
neither is repaired here.

Which object deserves this machinery at all is settled empirically in the
companion paper, *What to Protect When You Quantize a Mixture of Experts*,
which adjudicates — and rejects — the natural alternative of certifying
expert routing.

## Citing

See `CITATION.cff`. Licensed Apache-2.0; see `LICENSE` and `NOTICE`.

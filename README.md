# Factoring Trust

**A Machine-Checked Characterization of Where Verification Must End**

Trust is the complement of verifiability — and above a floor, that complement
*factors*. Verification fails for exactly three reasons: the fact is not
determined by the record, it is not certifiable from the record at the
verifier's power, or it does not stay true as the record grows. Each failure
names whom you must trust and what the cure costs, and the "exactly" is a
machine-checked biconditional, not a taxonomy.

This repository is the canonical, self-contained home of that result: the Lean
artifact and the paper, built to be reviewed as one small whole.

> Status: **under construction.** The `rc1` tag freezes the **Lean model**
> (the mechanization); `docs/paper/` is a **work-in-progress draft**, not
> part of that freeze. See `AGENTS.md` for the project boundary.

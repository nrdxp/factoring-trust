# Factoring Trust — project boundary

## Goal
The canonical, self-contained, machine-checked Lean artifact and paper for
**Factoring Trust: A Machine-Checked Characterization of Where Verification Must
End**. The result: trust is the complement of verifiability, and above a floor
that complement FACTORS — verification fails for exactly three reasons
(determination, certifiability, monotonicity), each failure naming whom you must
trust and what the cure costs, with the "exactly" carried by a machine-checked
biconditional.

This repository is the CANONICAL home of that contribution — a stand-alone
result, independent of any product — built for a reviewer: one small repository
that is exactly the artifact plus the paper.

## The prime directive — MINIMAL REPRESENTATION, not preservation
The mathematics is already proven true elsewhere; this repository exists to
present it MINIMALLY, for an elegant, exhaustive, reviewer-legible exposition.
**Optimize on minimality and reviewer clarity alone. Never preserve structure
for its own sake.** The question is always "what is the minimal, most legible
form" — never "what already exists." This is the single most important
instruction here: the default pull is to preserve prior code, and that default
is wrong for this artifact.

## Scope — the flagship
- The one theorem: `TT-snap` / `TT-end` across the strata oracle ⊃ computable ⊃
  polynomial (the polynomial stratum stays open, and the statement says so).
- Corollaries: EON and EALM, as clean specializations of the one theorem.
- Companion theorem: the general **verification ceiling** — the trust residue is
  minimal and bounded.
- Two witnesses of generality over ONE neutral core: an identity instance and a
  deliberately light surety instance (the surety instance is not fully exposited;
  its empirical treatment is a follow-up paper, cited not included).
- The floor: two residuals (binding, fidelity), scoped as prose where
  unmechanized (and said so).

NOT in this artifact — cited, never vendored, to keep the reviewer's trusted base
minimal: the full surety/build model, the deployment (eml) bridge, and any
empirical demonstration. Those are follow-up work.

## Structure — target
A single self-contained Lean workspace:
- `Core/` — no Mathlib: model, axes, scheme, the biconditional, corollaries,
  the feeding lemmas for the factorization display.
- `Effective/` — Mathlib: the computable stratum, the factorization display
  (`factorization_COMP`).
- `Transport/` — the record-transport law.
- `Ceiling/` — the general (domain-neutral) verification ceiling.
- `Witness/` — the forced generator and the cell table.
- `Instance/` — the identity and light-surety witnesses.
- `docs/` — the paper.

## Toolchain, build, acceptance
Lean `leanprover/lean4:v4.29.1` (pinned in `lean-toolchain`); build with
`lake build`. Acceptance bar for any change: `lake build` clean, and
`#print axioms` on the flagship theorems shows only the declared axioms — never
`sorryAx`.

## Names
"Trichotomy" is the theorem; "Factoring Trust" is the work; "verification
ceiling" is the general companion; "surety ceiling" is its build-domain
specialization (the follow-up paper).

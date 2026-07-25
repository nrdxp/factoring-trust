import Core.Model
import Core.Axes
import Core.Commitment
import Core.Schemes
import Core.Snapshot
import Core.Endurance
import Core.CollisionExtraction
import Core.Corollaries
import Core.Factorization

/-!
# Core — the trichotomy's logical model, Mathlib-free

Three axioms beyond Lean's built-ins (`propext`, `Classical.choice`, `Quot.sound`):
`EonEalm.Entry` (the abstract entry alphabet), `EonEalm.Context` and
`EonEalm.Context.inhabited` (the ambient-context type and its non-vacuity).
`EonEalm.Context.nontrivial` (`|Ξ| ≥ 2`) is consumed by `Core.Axes.exists_undetermined_claim`,
which witnesses that `Determined` is a genuine restriction rather than vacuous truth, and —
by design — by the cell table's two `¬D` rows (`Witness.Cells.exists_undetermined_monotone`,
`Witness.Cells.authoredAbsentClaim_not_determined`), which are that same witness shape
carried into the table; it appears nowhere else.

## Module map
* `Core.Model` — records, the extension order `⊑`, worlds, claims.
* `Core.Axes` — record-determined, monotone, and the non-vacuity of `Determined`.
* `Core.Commitment` — the abstract commitment scheme, its non-vacuity witnesses, and
  its incompressibility (`no_commitment_over_bool`).
* `Core.Schemes` — the verification scheme, snapshot/enduring soundness.
* `Core.Snapshot` — the snapshot characterization (`snapshot_characterization`).
* `Core.Endurance` — EALM (`endurance_iff_monotone`).
* `Core.CollisionExtraction` — the collision-extraction reduction, which
  `Core.Snapshot` proves snapshot soundness through, the commitment it constructs from
  a collision-resistance hypothesis, and the compressing digest that shows what the
  reduction reaches and `Commitment` cannot.
* `Core.Corollaries` — the determination gate, oracle-stratum packagings, and the EON
  trilemma (`eon_trilemma_impossibility`).
* `Core.Factorization` — the record-side forms `determined_iff_factors` and
  `monotone_iff_projUpClosed` the factorization display assembles.
-/

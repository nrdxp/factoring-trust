import Effective.Trichotomy

/-!
# Effective.Cells — certifiability annotations for the cell table's fibered rows

The one new Mathlib addition the cell table needs (`Witness.Cells` itself
stays Core-only): rows 3 and 5's record-only part, `e ∉ w`, is
`ComputablePred` — the negation of `TrichotomyComp.entryMemComputable`'s
membership predicate, closed under `ComputablePred.not`. Row 1 cites
`TrichotomyComp.inclusionClaim_computableMembership` (already landed, not
reproduced here); rows 2 and 5's C column is n.a. (fibered — see
`Witness.Cells`'s module doc); rows 4 and 6's degeneracy reading stays
cited (Rice/Rice–Shapiro), and their cells are inhabited by
`Effective.NonCertifiable`'s divergence claims, whose failure of
`ComputableMembership` is proved from Mathlib's halting problem.
-/

namespace Effective.Cells

open EonEalm TrichotomyComp

variable [Primcodable Entry]

/-- Row 3's record part, `ComputablePred`: `absenceClaim`'s projection
    `e ∉ w` is the negation of `entryMemComputable`'s membership
    predicate. -/
theorem absenceClaim_computableMembership (e : Entry) :
    ComputableMembership (fun w : Record => e ∉ w) :=
  ⟨Unit, inferInstance, fun w _ => e ∉ w, ComputablePred.not (entryMemComputable e),
    fun _ => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩⟩

/-- Row 5's record part shares the identical `e ∉ w` shape once `ξ` is
    fixed to the row's own `ξ₁` — the same annotation. -/
theorem authoredAbsentClaim_computableMembership (e : Entry) :
    ComputableMembership (fun w : Record => e ∉ w) :=
  absenceClaim_computableMembership e

end Effective.Cells

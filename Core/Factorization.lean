import Core.Axes

/-!
# Factorization — the record-side form of the two axes

The two algebraic facts the factorization display (`Effective.factorization_COMP`)
assembles: determination is membership in the image of the context-forgetting
pullback, and monotonicity of a determined claim is exactly up-closure of its
projection along `⊑`.
-/

namespace EonEalm

/-- A determined claim equals its own record-only projection, restated as
    ambient-context-blind. The `Eq` (not just `Iff`) form `determined_iff_factors`
    packages existentially. -/
theorem determined_eq_proj {φ : Claim} (hd : Determined φ) :
    φ = fun w _ => determinedProj φ hd w :=
  funext fun w => funext fun ξ => propext (determinedProj_iff hd w ξ).symm

/-- Determination, restated: `φ` is record-determined iff it factors through some
    record-only predicate `ψ`, i.e. is in the image of the pullback along
    `World → Record`. -/
theorem determined_iff_factors (φ : Claim) :
    Determined φ ↔ ∃ ψ : Record → Prop, φ = fun w _ => ψ w := by
  constructor
  · intro hd
    exact ⟨determinedProj φ hd, determined_eq_proj hd⟩
  · rintro ⟨ψ, rfl⟩
    exact fun _ _ _ => Iff.rfl

/-- Up-closure along `⊑`: the record-only analogue of `Monotone`. -/
def UpClosed (ψ : Record → Prop) : Prop := ∀ w w', w ⊑ w' → ψ w → ψ w'

/-- For a determined `φ`, monotonicity is exactly up-closure of its projection.
    The forward direction is `determinedProj_monotone`; the reverse transports
    up-closure back across the projection at a fixed witness context. -/
theorem monotone_iff_projUpClosed {φ : Claim} (hd : Determined φ) :
    Monotone φ ↔ UpClosed (determinedProj φ hd) := by
  constructor
  · intro hm w w' hext h
    exact determinedProj_monotone hd hm w w' h hext
  · intro hup w w' ξ hφ hext
    have h1 : determinedProj φ hd w := (determinedProj_iff hd w ξ).mpr hφ
    exact (determinedProj_iff hd w' ξ).mp (hup w w' hext h1)

end EonEalm

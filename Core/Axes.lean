import Core.Model

/-!
# Axes — determination and monotonicity

The two orthogonal axes the biconditional is built from. `Monotone` lifts `φ(w,ξ)` to
`φ(w',ξ)` along `w ⊑ w'`, holding the **same** `ξ` on both sides — an `∀ ξ'` version
would collapse the two axes together at `w' = w`.
-/

namespace EonEalm

/-- Record-determined: `φ`'s truth does not depend on which ambient context `ξ`
    witnesses it. -/
def Determined (φ : Claim) : Prop := ∀ w ξ ξ', φ w ξ ↔ φ w ξ'

/-- The unique record-only projection `φ̂` of a determined claim (Ξ inhabited licenses
    picking any witness context). -/
noncomputable def determinedProj (φ : Claim) (_hd : Determined φ) : Record → Prop :=
  fun w => φ w default

theorem determinedProj_iff {φ : Claim} (hd : Determined φ) (w : Record) (ξ : Context) :
    determinedProj φ hd w ↔ φ w ξ :=
  hd w default ξ

/-- Monotone (same context): a determined-projection witness survives extension. -/
def Monotone (φ : Claim) : Prop := ∀ w w' ξ, φ w ξ → w ⊑ w' → φ w' ξ

/-- For a determined `φ`, monotonicity lifts along `⊑` on the record-only projection
    `φ̂`. -/
theorem determinedProj_monotone {φ : Claim} (hd : Determined φ) (hm : Monotone φ)
    (w w' : Record) (h : determinedProj φ hd w) (hext : w ⊑ w') :
    determinedProj φ hd w' :=
  (determinedProj_iff hd w' default).mpr
    (hm w w' default ((determinedProj_iff hd w default).mp h) hext)

/-- `Determined` is a genuine restriction, not vacuous: some claim fails it.
    Witness: `φ := fun _ ξ => ξ = ξ₁` for a `Context.nontrivial` pair
    `ξ₁ ≠ ξ₂` — determination at `(ξ₁, ξ₂)` would force `ξ₂ = ξ₁`, contradicting
    the pair. This is the theorem that consumes `Context.nontrivial`. -/
theorem exists_undetermined_claim : ∃ φ : Claim, ¬ Determined φ := by
  obtain ⟨ξ₁, ξ₂, hne⟩ := Context.nontrivial
  refine ⟨fun _ ξ => ξ = ξ₁, fun hdet => hne ?_⟩
  exact ((hdet [] ξ₁ ξ₂).mp rfl).symm

/-- The collapse direction, making `Context.nontrivial`'s role legible: a
    subsingleton `Context` would trivialize `Determined` for every claim. -/
theorem subsingleton_context_trivializes (hsub : ∀ ξ ξ' : Context, ξ = ξ') :
    ∀ φ : Claim, Determined φ :=
  fun _ _ ξ ξ' => by rw [hsub ξ ξ']

end EonEalm

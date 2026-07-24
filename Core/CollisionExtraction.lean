import Core.Snapshot

/-!
# Collision extraction — the effective-stratum soundness pattern

The general `accepts → φ ∨ ∃ collision` shape: replay the snapshot verifier against an
**arbitrary** commitment function `Cw` — not assumed binding — and show acceptance
forces either a genuine witness at exactly the claimed record, or a `Cw`-collision.
This is the pattern a concrete effective-stratum instantiation discharges instead of
assuming an unconditional binding axiom the way `Core.Commitment`'s idealized
`Commitment.binding` does.
-/

namespace EonEalm

/-- `Cw` has no collision: it is genuinely injective. The hypothesis a concrete
    effective-stratum construction discharges instead of assuming outright. -/
def NoCollision {Comm : Type} (Cw : Record → Comm) : Prop := ∀ w w', Cw w = Cw w' → w = w'

/-- The collision-extraction reduction: replaying the snapshot `(w, t)` witness/checker
    verifier against an arbitrary (not-assumed-binding) `Cw`, an accepting `(w', t)`
    against target `target` either exhibits a genuine oracle witness for `target`
    itself (`w' = target`) or a `Cw`-collision between `w'` and `target`. No
    cryptographic hypothesis is needed for *this* general shape; `NoCollision` only
    becomes load-bearing once this is composed with a scheme's soundness obligation. -/
theorem collision_extraction_reduction {Comm : Type} (Cw : Record → Comm)
    (Witness : Type) (Chk : Record → Witness → Prop) (φ' : Record → Prop)
    (hφ' : ∀ w, φ' w ↔ ∃ t, Chk w t) (target : Record) (c : Record × Witness)
    (hacc : Cw c.1 = Cw target ∧ Chk c.1 c.2) :
    φ' target ∨ (c.1 ≠ target ∧ Cw c.1 = Cw target) := by
  obtain ⟨heq, hchk⟩ := hacc
  by_cases hc : c.1 = target
  · left
    rw [hφ']
    exact ⟨c.2, hc ▸ hchk⟩
  · right
    exact ⟨hc, heq⟩

/-- Under `NoCollision Cw`, the reduction's right disjunct is impossible, so
    acceptance forces the genuine witness — "no forgery without a collision." -/
theorem collision_extraction_reduction_of_noCollision {Comm : Type} (Cw : Record → Comm)
    (Witness : Type) (Chk : Record → Witness → Prop) (φ' : Record → Prop)
    (hφ' : ∀ w, φ' w ↔ ∃ t, Chk w t) (hnc : NoCollision Cw) (target : Record)
    (c : Record × Witness) (hacc : Cw c.1 = Cw target ∧ Chk c.1 c.2) : φ' target := by
  rcases collision_extraction_reduction Cw Witness Chk φ' hφ' target c hacc with h | ⟨hne, heq⟩
  · exact h
  · exact absurd (hnc c.1 target heq) hne

end EonEalm

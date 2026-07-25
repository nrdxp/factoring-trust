import Core.Schemes
import Core.CollisionExtraction

/-!
# Snapshot — the snapshot characterization

`φ` admits a snapshot-sound scheme iff record-determined ∧ `φ̂` is oracle-certifiable.

The verifier `V h c := C(c.w) = h ∧ Chk(c.w, c.t)` is exactly the shape
`Core.CollisionExtraction`'s reduction is stated over, so `snapshotScheme`'s soundness
is proved *through* that reduction with `Γ.binding` supplying `NoCollision Γ.C`. The
idealized stratum is thereby the collision stratum's `NoCollision` instance rather
than a parallel argument, and the one step this characterization takes on faith is
named where it is taken.
-/

namespace EonEalm

/-- The witness/checker construction: `c := (w, t)`, `t` an oracle witness for `φ̂(w)`;
    `V` checks `C(w) = h ∧ Chk(w, t)`. Includes non-monotone determined claims (e.g.
    sparse-Merkle non-membership). Completeness exhibits `c` directly from the oracle
    witness — no prover function is bundled. -/
def snapshotScheme {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hd : Determined φ) (Witness : Type) (Chk : Record → Witness → Prop)
    (hnp : ∀ w, determinedProj φ hd w ↔ ∃ t, Chk w t) : Scheme Γ φ where
  Proof := Record × Witness
  V := fun h c => Γ.C c.1 = h ∧ Chk c.1 c.2
  completeness := fun w ξ hφ => by
    have hφ' : determinedProj φ hd w := (determinedProj_iff hd w ξ).mpr hφ
    obtain ⟨t, ht⟩ := (hnp w).mp hφ'
    exact ⟨(w, t), rfl, ht⟩

theorem snapshotScheme_snapshotSound {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hd : Determined φ) (Witness : Type) (Chk : Record → Witness → Prop)
    (hnp : ∀ w, determinedProj φ hd w ↔ ∃ t, Chk w t) :
    SnapshotSound (snapshotScheme Γ φ hd Witness Chk hnp) := by
  intro w c hacc ξ
  have hφ' : determinedProj φ hd w :=
    collision_extraction_reduction_of_noCollision Γ.C Witness Chk (determinedProj φ hd)
      hnp Γ.binding w c hacc
  exact (determinedProj_iff hd w ξ).mp hφ'

/-- Snapshot characterization, backward direction. -/
theorem snapshot_characterization_backward {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hd : Determined φ) (hnp : NPMembership (determinedProj φ hd)) :
    ∃ S : Scheme Γ φ, SnapshotSound S := by
  obtain ⟨Witness, Chk, hchk⟩ := hnp
  exact ⟨snapshotScheme Γ φ hd Witness Chk hchk,
    snapshotScheme_snapshotSound Γ φ hd Witness Chk hchk⟩

/-- Any scheme's snapshot-soundness forces `φ` to be record-determined: completeness
    gives an accepting `c` at `(w, ξ)`; snapshot soundness forces `φ(w, ξ′)` for every
    `ξ′`. -/
theorem snapshot_characterization_determined {Comm : Type} {Γ : Commitment Comm} {φ : Claim}
    (S : Scheme Γ φ) (hsound : SnapshotSound S) : Determined φ := by
  intro w ξ ξ'
  constructor
  · intro h
    obtain ⟨c, hc⟩ := S.completeness w ξ h
    exact hsound w c hc ξ'
  · intro h
    obtain ⟨c, hc⟩ := S.completeness w ξ' h
    exact hsound w c hc ξ

/-- Oracle-certifiability is forced by any scheme existing (via completeness's
    certificate existence, not an efficient prover), not an added scope condition. -/
theorem snapshot_characterization_np {Comm : Type} {Γ : Commitment Comm} {φ : Claim}
    (hd : Determined φ) (S : Scheme Γ φ) (hsound : SnapshotSound S) :
    NPMembership (determinedProj φ hd) := by
  refine ⟨S.Proof, fun w t => S.V (Γ.C w) t, fun w => ⟨?_, ?_⟩⟩
  · intro hφproj
    have hφ : φ w default := (determinedProj_iff hd w default).mp hφproj
    exact S.completeness w default hφ
  · rintro ⟨t, ht⟩
    exact (determinedProj_iff hd w default).mpr (hsound w t ht default)

/-- Snapshot characterization, packaged as a single iff (both directions). -/
theorem snapshot_characterization {Comm : Type} (Γ : Commitment Comm) (φ : Claim) :
    (∃ S : Scheme Γ φ, SnapshotSound S) ↔
      ∃ hd : Determined φ, NPMembership (determinedProj φ hd) := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨snapshot_characterization_determined S hS,
      snapshot_characterization_np (snapshot_characterization_determined S hS) S hS⟩
  · rintro ⟨hd, hnp⟩
    exact snapshot_characterization_backward Γ φ hd hnp

end EonEalm

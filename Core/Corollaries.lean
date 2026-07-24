import Core.Endurance

/-!
# Corollaries — the determination gate, EON, and the oracle-stratum packagings

Four displays scoped inside the snapshot/endurance characterizations of `Core.Snapshot`
and `Core.Endurance`:

* the **determination gate** — a claim that is not record-determined admits no scheme
  at any stratum, since the underlying fact (`snapshot_characterization_determined`)
  does not depend on the verifier's certifiability at all;
* **`npMembership_trivial`** — oracle-certifiability (`NPMembership`) is vacuously
  satisfiable for *any* predicate, so the results above sit at the oracle stratum until
  a genuinely certifiable witness replaces the checker;
* **`snapshot_iff_determined_ALL`** — folding `npMembership_trivial` into the snapshot
  characterization collapses it to a plain iff with `Determined`, since the
  oracle-certifiability conjunct is never a genuine restriction at this stratum;
* **`trichotomy_ALL_iff`** — the unfibered oracle-stratum packaging of endurance: no
  external `hd`/`hnp` hypotheses, existentially quantified instead;
* **the EON trilemma's impossibility corner** — no scheme for a record-determined,
  oracle-certifiable, **non-monotone** claim is both offline and eternal. Offline is
  not a separate hypothesis: `Scheme.V`'s type already excludes record/oracle/clock/`ξ`
  access, so every `Scheme` in this model is offline by construction — what remains to
  state is the impossibility content itself, a direct two-line consequence of
  `endurance_iff_monotone`'s forward direction.
-/

namespace EonEalm

/-- A claim that is not record-determined admits no snapshot-sound scheme over any
    commitment — the contrapositive of `snapshot_characterization_determined`, and
    hence a fortiori no enduring-sound scheme either (via
    `enduringSound_snapshotSound`). -/
theorem determination_gate {Comm : Type} {Γ : Commitment Comm} {φ : Claim}
    (hnd : ¬ Determined φ) : ¬ ∃ S : Scheme Γ φ, SnapshotSound S :=
  fun ⟨S, hsound⟩ => hnd (snapshot_characterization_determined S hsound)

/-- Oracle-certifiability is trivial: every predicate satisfies `NPMembership`,
    witnessed by `Unit` and `Chk w _ := ψ w`. The results built on `NPMembership`
    (`snapshot_characterization`, `endurance_iff_monotone`, `eon_trilemma_impossibility`)
    sit at the oracle stratum until a non-vacuous witness replaces this checker. -/
theorem npMembership_trivial (ψ : Record → Prop) : NPMembership ψ :=
  ⟨Unit, fun w _ => ψ w, fun _w => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩⟩

/-- The snapshot characterization at the oracle stratum, folding in
    `npMembership_trivial`: `φ` admits a snapshot-sound scheme iff `φ` is
    `Determined` — no separate certifiability conjunct, since it never restricts
    anything at this stratum. -/
theorem snapshot_iff_determined_ALL {Comm : Type} (Γ : Commitment Comm) (φ : Claim) :
    (∃ S : Scheme Γ φ, SnapshotSound S) ↔ Determined φ := by
  constructor
  · rintro ⟨S, hsound⟩
    exact snapshot_characterization_determined S hsound
  · intro hd
    exact snapshot_characterization_backward Γ φ hd (npMembership_trivial (determinedProj φ hd))

/-- The unfibered oracle-stratum packaging of endurance: `φ` admits an enduring-sound
    scheme iff `φ` is `Determined`, oracle-certifiable at its determined projection,
    and `Monotone` — assembled from `snapshot_characterization_determined`/`_np`,
    `endurance_forces_monotone`, and `endurance_construction`, with no external `hd`
    hypothesis threaded in from outside the statement. -/
theorem trichotomy_ALL_iff {Comm : Type} (Γ : Commitment Comm) (φ : Claim) :
    (∃ S : Scheme Γ φ, EnduringSound S) ↔
      ∃ hd : Determined φ, NPMembership (determinedProj φ hd) ∧ Monotone φ := by
  constructor
  · rintro ⟨S, hsound⟩
    have hssound : SnapshotSound S := enduringSound_snapshotSound hsound
    have hd : Determined φ := snapshot_characterization_determined S hssound
    have hnp : NPMembership (determinedProj φ hd) :=
      snapshot_characterization_np hd S hssound
    exact ⟨hd, hnp, endurance_forces_monotone hd hnp hsound⟩
  · rintro ⟨hd, hnp, hm⟩
    exact endurance_construction Γ φ hd hm hnp

/-- The EON trilemma's impossibility corner: offline, unexpiring, non-monotone — pick
    two. A direct two-line consequence of `endurance_iff_monotone`'s forward
    direction. -/
theorem eon_trilemma_impossibility {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hd : Determined φ) (hnp : NPMembership (determinedProj φ hd)) (hnm : ¬ Monotone φ) :
    ¬ ∃ S : Scheme Γ φ, EnduringSound S := by
  intro hex
  exact hnm ((endurance_iff_monotone Γ φ hd hnp).mp hex)

end EonEalm

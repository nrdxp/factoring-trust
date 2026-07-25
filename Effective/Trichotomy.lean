import Core
import Mathlib.Computability.Halting

/-!
# Trichotomy at the computable stratum

The Turing-computability analogue of `Core`'s oracle-stratum results: every
`Decidable` hypothesis a Lean-internal decidability waypoint would carry is replaced
by an independently-**posited** `Computable`/`ComputablePred` hypothesis. `Core` stays
Mathlib-free; this package is the one bridge that takes the dependency.

## `Decidable` and `ComputablePred` are logically independent

`Classical.propDecidable` gives *every* predicate a `Decidable` instance, including
the halting predicate, yet Mathlib proves that exact predicate is not `ComputablePred`
(`ComputablePred.halting_problem`). No closure lemma repairs this, so every
`Computable`/`ComputablePred` hypothesis below is posited as a bare argument — never
derived from a `Decidable` instance, `Classical.propDecidable`, or any
classical/noncomputable source.

## Why `Γ.C` computability is needed on both the forward and backward legs

The enduring verifier `V h c := Chk c.1 c.2.1 ∧ Γ.VC (Γ.C c.1) h c.2.2` composes `Γ.C`
inside the `VC` check on *both* legs, and `ComputablePred`-composition (unlike
`Decidable`, which is checked pointwise and does not care how its argument was
produced) requires every function feeding a computable predicate to itself be
`Computable` — so `hCComp : Computable Γ.C` is threaded through the enduring
biconditional's both directions, not only the forward one.

## Two closure lemmas absent from Mathlib under this name

`ComputablePred` is closed under composition and under `∧` — present in Mathlib for
negation (`ComputablePred.not`) but not for `∧`; `ComputablePred.and` below is the
closure lemma, built from `Primrec.and` (`Bool.and` is primitive recursive) and core's
`decide_and`. `ComputablePred.comp` is the companion composition lemma (composing a
`ComputablePred` with a `Computable` map), needed at every projection site.

The certificate type of any scheme witnessing a computable-stratum existential must
itself carry a `[Primcodable _]` instance for `ComputablePred` over it to even be
stated — a requirement `Decidable` never had. `comp_P1`, `comp_snap_P1`, and
`comp_COMP_iff` bundle this instance as data inside the witnessing existential.

## The snapshot-only leg: raw `Comm` equality, not `VC`

The enduring construction's verifier checks `Γ.VC`; the snapshot-only construction
(`Core.snapshotScheme`) instead checks `Γ.C c.1 = h` by **raw equality**, since a
snapshot verifier commits to *this* record, not one reached from an earlier one via
monotonicity. At the decidable-Lean waypoint that equality needs its own hypothesis
(`Decidable (a = b)` on `Comm`, unrelated to `Chk` or `Γ.VC`'s decidability). At the
computable stratum that hypothesis **dissolves**: equality on any `[Primcodable Comm]`
type is `PrimrecRel` via Mathlib's encode-then-compare construction (`Primrec.eq`),
needing no case analysis on `Comm` itself — so `comp_snap_P1` below needs no
`Comm`-equality hypothesis at all, a genuinely cheaper antecedent than the
decidable-waypoint analogue.
-/

namespace TrichotomyComp

open EonEalm

/-! ## Closure lemmas for `ComputablePred`, absent from Mathlib under this name -/

/-- `ComputablePred` composed with a `Computable` map is `ComputablePred`. -/
theorem ComputablePred.comp {α β} [Primcodable α] [Primcodable β] {p : β → Prop} {f : α → β}
    (hp : ComputablePred p) (hf : Computable f) : ComputablePred (fun a => p (f a)) := by
  obtain ⟨hpd, hpc⟩ := hp
  exact ⟨fun a => hpd (f a), hpc.comp hf⟩

/-- `ComputablePred` closed under `∧`. -/
theorem ComputablePred.and {α} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => p a ∧ q a) := by
  obtain ⟨hpd, hpc⟩ := hp
  obtain ⟨hqd, hqc⟩ := hq
  -- Built explicitly (not via `haveI`/`inferInstance`): `haveI` erases the witness's
  -- transparency, which would make the `Decidable` instance this proof supplies
  -- non-defeq to the one `Bool.decide_and` needs to line up against `hpd`/`hqd` below.
  refine ⟨fun a => @instDecidableAnd (p a) (q a) (hpd a) (hqd a), ?_⟩
  have hcomp : Computable (fun a => decide (p a) && decide (q a)) :=
    Computable₂.comp Primrec.and.to_comp hpc hqc
  refine Computable.of_eq hcomp (fun a => ?_)
  exact (@Bool.decide_and (p a) (q a)
    (@instDecidableAnd (p a) (q a) (hpd a) (hqd a)) (hpd a) (hqd a)).symm

variable [Primcodable Entry]

/-- The computable-stratum analogue of `NPMembership`: a Σ₁-witness checker whose ↔ is
    the same shape, with the checker itself `ComputablePred` — Turing-computable, not
    merely Lean-`Decidable`. -/
def ComputableMembership (ψ : Record → Prop) : Prop :=
  ∃ (Witness : Type) (_ : Primcodable Witness) (Chk : Record → Witness → Prop),
    ComputablePred (fun p : Record × Witness => Chk p.1 p.2) ∧ ∀ w, ψ w ↔ ∃ t, Chk w t

/-- The enduring construction at the computable stratum (⟸ direction). The
    construction itself (`enduringScheme`) is untouched; only the verifier's
    computability proof is new. -/
theorem comp_P1
    {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm) [Primcodable Γ.VCProof]
    (φ : Claim) (hd : Determined φ)
    (Witness : Type) [Primcodable Witness] (Chk : Record → Witness → Prop)
    (hnp : ∀ w, determinedProj φ hd w ↔ ∃ t, Chk w t)
    (hm : Monotone φ)
    (hChkComp : ComputablePred (fun p : Record × Witness => Chk p.1 p.2))
    (hCComp : Computable Γ.C)
    (hVCComp : ComputablePred (fun p : Comm × Comm × Γ.VCProof => Γ.VC p.1 p.2.1 p.2.2)) :
    ∃ (S : Scheme Γ φ) (_ : Primcodable S.Proof), EnduringSound S ∧
      ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2) := by
  refine ⟨enduringScheme Γ φ hd Witness Chk hnp,
    (inferInstance : Primcodable (Record × Witness × Γ.VCProof)),
    enduringScheme_enduringSound Γ φ hd hm Witness Chk hnp, ?_⟩
  -- `enduringScheme`'s `V h c := Chk c.1 c.2.1 ∧ Γ.VC (Γ.C c.1) h c.2.2` (certificate
  -- type `Record × Witness × Γ.VCProof`); `show` unfolds the `def`-hidden `V`/`Proof`
  -- to this defeq form.
  show ComputablePred (fun p : Comm × (Record × Witness × Γ.VCProof) =>
    Chk p.2.1 p.2.2.1 ∧ Γ.VC (Γ.C p.2.1) p.1 p.2.2.2)
  apply ComputablePred.and
  · -- `Chk p.2.1 p.2.2.1`: `hChkComp` composed with the computable projection
    -- `p ↦ (p.2.1, p.2.2.1)`. (`ComputablePred.comp` called by full name, not dot
    -- notation: `ComputablePred` unfolds to `Exists` during dot-notation head
    -- resolution, which would otherwise send `.comp` looking for a nonexistent
    -- `Exists.comp`.)
    exact ComputablePred.comp hChkComp (Computable.pair
      (Computable.fst.comp Computable.snd)
      (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  · -- `Γ.VC (Γ.C p.2.1) p.1 p.2.2.2`: `hVCComp` composed with the computable map
    -- `p ↦ (Γ.C p.2.1, p.1, p.2.2.2)` — `Γ.C`'s own computability (`hCComp`) is
    -- exactly the extra ingredient this composition needs.
    exact ComputablePred.comp hVCComp (Computable.pair
      (Computable.comp hCComp (Computable.fst.comp Computable.snd))
      (Computable.pair Computable.fst
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))

/-- The enduring construction at the computable stratum (⟹ direction). `Γ.C` must
    independently be `Computable`, needed to show `fun (w, t) => S.V (Γ.C w) t` is
    itself `ComputablePred` (composing `hVComp` with `Γ.C`). `[Primcodable S.Proof]`
    is a bare hypothesis here (unlike `comp_P1`, `S` is an abstract input, not a
    concrete construction whose `Proof` field unfolds). -/
theorem comp_P1_forward
    {Comm : Type} [Primcodable Comm] {Γ : Commitment Comm} {φ : Claim}
    (S : Scheme Γ φ) [Primcodable S.Proof] (hsound : EnduringSound S)
    (hCComp : Computable Γ.C)
    (hVComp : ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2)) :
    ∃ hd : Determined φ, ComputableMembership (determinedProj φ hd) ∧ Monotone φ := by
  have hssound : SnapshotSound S := enduringSound_snapshotSound hsound
  have hd : Determined φ := snapshot_characterization_determined S hssound
  have hiff : ∀ w, determinedProj φ hd w ↔ ∃ t, S.V (Γ.C w) t := by
    intro w
    constructor
    · intro hφproj
      have hφ : φ w default := (determinedProj_iff hd w default).mp hφproj
      exact S.completeness w default hφ
    · rintro ⟨t, ht⟩
      exact (determinedProj_iff hd w default).mpr (hssound w t ht default)
  have hmono : Monotone φ := by
    intro w w' ξ hφ hww'
    obtain ⟨c, hc⟩ := S.completeness w ξ hφ
    exact hsound w c hc w' ξ hww'
  have hChkComp : ComputablePred (fun p : Record × S.Proof => S.V (Γ.C p.1) p.2) :=
    ComputablePred.comp hVComp
      (Computable.pair (Computable.comp hCComp Computable.fst) Computable.snd)
  exact ⟨hd, ⟨S.Proof, inferInstance, fun w t => S.V (Γ.C w) t, hChkComp, hiff⟩, hmono⟩

/-- The computable biconditional: fixing a commitment `Γ` whose commitment function
    is `Computable` and whose `VC` is `ComputablePred`, `φ` admits an enduring-sound
    scheme with a `ComputablePred` verifier (over some `Primcodable` certificate type)
    iff `φ` is `Determined`, `ComputableMembership` at its determined projection, and
    `Monotone`. -/
theorem comp_COMP_iff
    {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm) [Primcodable Γ.VCProof] (φ : Claim)
    (hCComp : Computable Γ.C)
    (hVCComp : ComputablePred (fun p : Comm × Comm × Γ.VCProof => Γ.VC p.1 p.2.1 p.2.2)) :
    (∃ (S : Scheme Γ φ) (_ : Primcodable S.Proof), EnduringSound S ∧
        ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2)) ↔
      ∃ hd : Determined φ, ComputableMembership (determinedProj φ hd) ∧ Monotone φ := by
  constructor
  · rintro ⟨S, hSPC, hsound, hVComp⟩
    -- `letI`, not `haveI`: transparency matters here, since `hVComp`'s type already
    -- carries the `Primcodable S.Proof` instance obtained from destructuring the same
    -- existential (`hSPC`) — `haveI` would erase that and the two would fail to line
    -- up as defeq.
    letI := hSPC
    exact comp_P1_forward S hsound hCComp hVComp
  · rintro ⟨hd, hcomp, hm⟩
    obtain ⟨Witness, hWPC, Chk, hChkComp, hnp⟩ := hcomp
    letI := hWPC
    exact comp_P1 Γ φ hd Witness Chk hnp hm hChkComp hCComp hVCComp

/-! ## The snapshot-only leg at the computable stratum (M2b) -/

/-- The snapshot-only construction at the computable stratum (⟸ direction):
    `Core.snapshotScheme` verbatim; no `Monotone` hypothesis anywhere, and no
    `Comm`-equality hypothesis either, since equality on a `[Primcodable Comm]`
    type is `ComputablePred` for free via `Primrec.eq`. -/
theorem comp_snap_P1
    {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm)
    (φ : Claim) (hd : Determined φ)
    (Witness : Type) [Primcodable Witness] (Chk : Record → Witness → Prop)
    (hnp : ∀ w, determinedProj φ hd w ↔ ∃ t, Chk w t)
    (hChkComp : ComputablePred (fun p : Record × Witness => Chk p.1 p.2))
    (hCComp : Computable Γ.C) :
    ∃ (S : Scheme Γ φ) (_ : Primcodable S.Proof), SnapshotSound S ∧
      ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2) := by
  refine ⟨snapshotScheme Γ φ hd Witness Chk hnp,
    (inferInstance : Primcodable (Record × Witness)),
    snapshotScheme_snapshotSound Γ φ hd Witness Chk hnp, ?_⟩
  -- `snapshotScheme`'s `V h c := Γ.C c.1 = h ∧ Chk c.1 c.2` (certificate type
  -- `Record × Witness`).
  show ComputablePred (fun p : Comm × (Record × Witness) => Γ.C p.2.1 = p.1 ∧ Chk p.2.1 p.2.2)
  apply ComputablePred.and
  · have hEqComp : ComputablePred (fun q : Comm × Comm => q.1 = q.2) :=
      PrimrecPred.computablePred (Primrec.eq : PrimrecRel (@Eq Comm))
    exact ComputablePred.comp hEqComp (Computable.pair
      (Computable.comp hCComp (Computable.fst.comp Computable.snd)) Computable.fst)
  · exact ComputablePred.comp hChkComp Computable.snd

/-- The snapshot-only construction at the computable stratum (⟹ direction). -/
theorem comp_snap_P1_forward
    {Comm : Type} [Primcodable Comm] {Γ : Commitment Comm} {φ : Claim}
    (S : Scheme Γ φ) [Primcodable S.Proof] (hssound : SnapshotSound S)
    (hCComp : Computable Γ.C)
    (hVComp : ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2)) :
    ∃ hd : Determined φ, ComputableMembership (determinedProj φ hd) := by
  have hd : Determined φ := snapshot_characterization_determined S hssound
  have hiff : ∀ w, determinedProj φ hd w ↔ ∃ t, S.V (Γ.C w) t := by
    intro w
    constructor
    · intro hφproj
      have hφ : φ w default := (determinedProj_iff hd w default).mp hφproj
      exact S.completeness w default hφ
    · rintro ⟨t, ht⟩
      exact (determinedProj_iff hd w default).mpr (hssound w t ht default)
  have hChkComp : ComputablePred (fun p : Record × S.Proof => S.V (Γ.C p.1) p.2) :=
    ComputablePred.comp hVComp
      (Computable.pair (Computable.comp hCComp Computable.fst) Computable.snd)
  exact ⟨hd, ⟨S.Proof, inferInstance, fun w t => S.V (Γ.C w) t, hChkComp, hiff⟩⟩

/-- The snapshot-only biconditional at the computable stratum: fixing a commitment
    `Γ` whose commitment function is `Computable`, `φ` admits a snapshot-sound scheme
    with a `ComputablePred` verifier iff `φ` is `Determined` and `ComputableMembership`
    at its determined projection — no `Monotone` conjunct on either side, and no
    `Comm`-equality hypothesis (it dissolves, see the module doc-comment). -/
theorem trichotomy_snap_COMP_iff
    {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm) (φ : Claim)
    (hCComp : Computable Γ.C) :
    (∃ (S : Scheme Γ φ) (_ : Primcodable S.Proof), SnapshotSound S ∧
        ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2)) ↔
      ∃ hd : Determined φ, ComputableMembership (determinedProj φ hd) := by
  constructor
  · rintro ⟨S, hSPC, hssound, hVComp⟩
    letI := hSPC
    exact comp_snap_P1_forward S hssound hCComp hVComp
  · rintro ⟨hd, hcomp⟩
    obtain ⟨Witness, hWPC, Chk, hChkComp, hnp⟩ := hcomp
    letI := hWPC
    exact comp_snap_P1 Γ φ hd Witness Chk hnp hChkComp hCComp

/-! ## The factorization display, at the computable stratum (M1c)

`Core.Factorization`'s two record-side facts assemble `comp_COMP_iff` into the
factorization display: `φ` admits enduring, offline, computable evidence iff `φ`
factors through a computably-membership, up-closed record predicate. -/

/-- The factorization display: `φ ∈ π*(Σ₁ ∩ Up(⊑))` at the computable stratum. -/
theorem factorization_COMP
    {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm) [Primcodable Γ.VCProof] (φ : Claim)
    (hCComp : Computable Γ.C)
    (hVCComp : ComputablePred (fun p : Comm × Comm × Γ.VCProof => Γ.VC p.1 p.2.1 p.2.2)) :
    (∃ (S : Scheme Γ φ) (_ : Primcodable S.Proof), EnduringSound S ∧
        ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2)) ↔
      ∃ ψ : Record → Prop, ComputableMembership ψ ∧ UpClosed ψ ∧ φ = fun w _ => ψ w := by
  rw [comp_COMP_iff Γ φ hCComp hVCComp]
  constructor
  · rintro ⟨hd, hcomp, hm⟩
    exact ⟨determinedProj φ hd, hcomp, (monotone_iff_projUpClosed hd).mp hm,
      determined_eq_proj hd⟩
  · rintro ⟨ψ, hcomp, hup, rfl⟩
    have hd : Determined (fun w _ => ψ w) := fun _ _ _ => Iff.rfl
    exact ⟨hd, hcomp, (monotone_iff_projUpClosed hd).mpr hup⟩

/-! ## Non-vacuity — a contentful computable-stratum witness -/

/-- Equality on any `Primcodable` type is `PrimrecRel` via Mathlib's encode-then-
    compare construction (`Primrec.eq`), genuinely weaker than `[DecidableEq Entry]`
    since it needs no case analysis on `Entry` itself, only `[Primcodable Entry]`.
    Composed with `PrimrecRel.exists_mem_list` and reindexed to a fixed `e`, this
    gives list membership as `ComputablePred` without ever invoking `Decidable`. -/
theorem entryMemComputable (e : Entry) :
    ComputablePred (fun p : Record × Unit => e ∈ p.1) := by
  have hMem : PrimrecRel (fun (L : List Entry) (b : Entry) => ∃ a ∈ L, a = b) :=
    PrimrecRel.exists_mem_list Primrec.eq
  have hMemComp : ComputablePred (fun q : List Entry × Entry => ∃ a ∈ q.1, a = q.2) :=
    PrimrecPred.computablePred hMem
  -- `hf`'s type is ascribed explicitly, fixing `α`/`f` before `.comp` runs. `hComp`
  -- is deliberately left *unascribed*: ascribing its result type here (even with
  -- `hf` already pinned) lets elaboration's expected-type pass on
  -- `ComputablePred.comp`'s conclusion `fun a => ?p (?f a)` unify `?p := Exists`
  -- directly against `∃ a ∈ p.1, a = e` before `hMemComp`'s own type is consulted.
  have hf : Computable (fun p : Record × Unit => (p.1, e)) :=
    Computable.pair Computable.fst (Computable.const e)
  have hComp := ComputablePred.comp hMemComp hf
  -- `hComp`'s predicate is the un-beta-reduced `(fun q => ∃ x ∈ q.1, x = q.2) (p.1,
  -- e)`; `dsimp only` reduces the `Prod.fst`/`.snd` projections before `rintro`'s
  -- `rfl` pattern substitutes — `▸` fails here since it rewrites syntactically and
  -- the un-dsimp'd goal never literally displays `e`.
  refine hComp.of_eq (fun p => ?_)
  dsimp only
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro h
    exact ⟨e, h, rfl⟩

omit [Primcodable Entry] in
/-- `w ⊑ w'` restated as a single list equality, unconditionally: if `w ⊑ w'` then
    `w'.take w.length = w` is `List.take_left`; conversely, given `w'.take w.length =
    w`, `List.take_append_drop` exhibits `w'.drop w.length` as the extension witness
    once `w'.take w.length` is rewritten to `w`. This reformulation — not `⊑`'s own
    `∃`-shaped definition — is what `extComputable` below shows `ComputablePred`. -/
theorem ext_iff_take (w w' : Record) : w ⊑ w' ↔ w'.take w.length = w := by
  constructor
  · rintro ⟨u, rfl⟩
    exact List.take_left
  · intro h
    -- `rw [← h]` on the raw goal `w' = w ++ w'.drop w.length` would rewrite *both*
    -- occurrences of `w` (including the one inside `w.length` on the RHS),
    -- corrupting the drop-index; routing through `calc` rewrites only the isolated
    -- `w'.take w.length` subterm `h` names.
    refine ⟨w'.drop w.length, ?_⟩
    calc w' = w'.take w.length ++ w'.drop w.length := (List.take_append_drop _ _).symm
      _ = w ++ w'.drop w.length := by rw [h]

/-- `EonEalm.idCommitmentComp`'s `VC`, restated at the computable stratum:
    `ComputablePred` via `ext_iff_take` and `Primrec.list_take`/`Primrec.list_length`/
    `Primrec.eq` — all `[Primcodable Entry]`-only, no `[DecidableEq Entry]`. -/
theorem extComputable :
    ComputablePred (fun p : Record × Record × Unit => p.1 ⊑ p.2.1) := by
  have htake : Computable (fun p : Record × Record × Unit => p.2.1.take p.1.length) :=
    Computable₂.comp Primrec.list_take.to_comp
      (Primrec.list_length.to_comp.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  have hEqComp : ComputablePred (fun q : Record × Record => q.1 = q.2) :=
    PrimrecPred.computablePred (Primrec.eq : PrimrecRel (@Eq Record))
  have hf : Computable (fun p : Record × Record × Unit => (p.2.1.take p.1.length, p.1)) :=
    Computable.pair htake Computable.fst
  -- `hComp` left unascribed — see `entryMemComputable`'s identical note.
  have hComp := ComputablePred.comp hEqComp hf
  exact hComp.of_eq (fun p => (ext_iff_take p.1 p.2.1).symm)

/-- Non-vacuity's commitment. Same `C := id`, no-compression shape as
    `EonEalm.idCommitment`/`idCommitmentComp`, but built here rather than reused: its
    `VC`-decidability proof is `[DecidableEq Entry]`-sourced; `binding`/`soundness`/
    `completeness` are copied verbatim since they carry no computability content. -/
def idCommitmentPC : Commitment Record where
  VCProof := Unit
  C := id
  binding := fun _ _ h => h
  VC := fun h₀ h _ => h₀ ⊑ h
  soundness := fun _w₀ _w _h₀ _h _π hvc h₀eq heq => by
    simp only [id] at h₀eq heq; rw [h₀eq, heq] at hvc; exact hvc
  completeness := fun w₀ w hext => ⟨(), by simpa using hext⟩

-- Registered explicitly rather than left to instance search: synthesizing
-- `Primcodable idCommitmentPC.VCProof` on demand does not reliably unfold the
-- `def`-hidden `VCProof` field to `Unit`; naming the instance up front sidesteps
-- that.
instance : Primcodable idCommitmentPC.VCProof := inferInstanceAs (Primcodable Unit)

theorem idCommitmentPC_C_computable : Computable idCommitmentPC.C := by
  show Computable (@id Record)
  exact Computable.id

theorem idCommitmentPC_VC_computablePred :
    ComputablePred (fun p : Record × Record × Unit => idCommitmentPC.VC p.1 p.2.1 p.2.2) := by
  show ComputablePred (fun p : Record × Record × Unit => p.1 ⊑ p.2.1)
  exact extComputable

/-- The computable-stratum mirror of the inclusion claim: the identical claim,
    reproved here since `Determined`/`Monotone` are cheap and the payload this file
    needs is `ComputableMembership`, not the oracle stratum's trivial witness. -/
def inclusionClaim (e : Entry) : Claim := fun w _ => e ∈ w

omit [Primcodable Entry] in
theorem inclusionClaim_determined (e : Entry) : Determined (inclusionClaim e) :=
  fun _ _ _ => Iff.rfl

omit [Primcodable Entry] in
/-- List-append can only add entries, so a membership witness for `w` survives to any
    `w'` extending it. -/
theorem inclusionClaim_monotone (e : Entry) : Monotone (inclusionClaim e) := by
  intro w w' _ hmem hext
  obtain ⟨u, hu⟩ := hext
  rw [hu]
  exact List.mem_append_left u hmem

omit [Primcodable Entry] in
theorem inclusionClaim_hnp (e : Entry) :
    ∀ w, determinedProj (inclusionClaim e) (inclusionClaim_determined e) w ↔
      ∃ _ : Unit, e ∈ w :=
  fun _ => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩

theorem inclusionClaim_computableMembership (e : Entry) :
    ComputableMembership (determinedProj (inclusionClaim e) (inclusionClaim_determined e)) :=
  ⟨Unit, inferInstance, fun w _ => e ∈ w, entryMemComputable e, inclusionClaim_hnp e⟩

/-- The computable-stratum contentful non-vacuity witness: the inclusion claim
    admits an enduring-sound scheme with a `ComputablePred` verifier over
    `idCommitmentPC` — via `comp_COMP_iff`'s ⟸ direction, so `comp_COMP_iff` genuinely
    bites on a claim with real content, not just a vacuous one. -/
theorem comp_COMP_nonvacuous (e : Entry) :
    ∃ (S : Scheme idCommitmentPC (inclusionClaim e)) (_ : Primcodable S.Proof),
      EnduringSound S ∧ ComputablePred (fun p : Record × S.Proof => S.V p.1 p.2) :=
  (comp_COMP_iff idCommitmentPC (inclusionClaim e)
      idCommitmentPC_C_computable idCommitmentPC_VC_computablePred).mpr
    ⟨inclusionClaim_determined e, inclusionClaim_computableMembership e,
      inclusionClaim_monotone e⟩

end TrichotomyComp

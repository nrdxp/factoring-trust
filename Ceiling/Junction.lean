import Core
import Ceiling.Gate

/-!
# Ceiling — Junction: the gate's scheme-world result forces the accounting-world
# trust surface to contain the seeds, for every scheme

`Ceiling.Gate`'s old `ceiling` bundled three facts sharing the argument names
`φ_bind : Claim` and `a : Node Payload` without ever relating them. This file
builds the missing junction. **It has already been through one failed
attempt, and the failure is recorded here because the fix depends on it.**

## Round 1 (rejected) — a conjunction is not a relation

The first `Discharges` here was `m.seed? = true ∧ SnapshotSound S`. The
lead-maintainer's objection, verified against the file and conceded:
**every consumer projected exactly one component.** L1's proof
(`fun h => binding_admits_no_scheme φ_bind hfiber Γ ⟨S, h.2⟩`) discards `m`
entirely; the seed-only non-vacuity check discards `S`. A conjunction whose
every use projects one side is two independent facts riding in a pair, not a
relation — the SAME defect §1.6(iii)'s bundle had, with more syntax around
it. `discharges_requires_seed` (that both conjuncts were individually
non-trivial) answered the wrong question: non-vacuity of each half is not
evidence the two interact.

## Round 2 — why it couldn't be fixed in place

`Scheme Γ φ_bind`'s only surface is `Comm`/`Proof` (`V : Comm → Proof →
Prop`); nothing in `Node Payload` — abstract, carrying no `Record` — can
reach it without a map. `EonEalm.Entry` is `axiom Entry : Type`, opaque by
construction, so the neutral core cannot manufacture one: domain-neutrality
working as designed, not a gap (`.ledger/trichotomy/STATEMENT-rc-v0.7.md`,
v0.8 AMENDMENT, ratified 2026-07-24). The fix is `RecordRealization` below:
the junction is now PARAMETERIZED on a domain-supplied record map, exactly
the shape `Ceiling.Commitment`-style structures already take (see
`Core.Commitment`) — a function bundled with the properties it must satisfy,
supplied per domain, never manufactured in the neutral core.

## `RecordRealization` — the missing embedding, named and required

A **record realization** `ρ : RecordRealization Payload` is `recordOf : Node
Payload → Record` satisfying:
- **(R1) faithful** — dependency-order faithfulness: `m ∈ depclosure n →
  recordOf m ⊑ recordOf n`, so building atop an artifact EXTENDS its record.
- **(R2) seedBoundary** — a node is a seed exactly when its record commits no
  prior entries: `m.seed? = true ↔ recordOf m = []`. This is the conjunct
  round 1's `Discharges` was missing: it ties the accounting-side seed flag
  to a scheme-side FACT ABOUT THE RECORD, not to a bare Boolean sitting next
  to an unrelated one.

`demoRealization` below (parametric in one `Entry`, since the axiom carries
no inhabitedness) proves R1+R2 jointly satisfiable — the structure itself is
non-vacuous before anything is built on it.

## `Discharges`, round 2 — a genuine relation

`Discharges Γ φ_bind ρ S m := SnapshotSound S ∧ ∃ c, S.V (Γ.C (ρ.recordOf m))
c` — "S certifies m's establishment from `ρ.recordOf m` alone." **The
acceptance test round 1 failed: does any proof consume both components in
one step?** `discharges_forces_binding` does:
`hsound (ρ.recordOf m) c hc` applies the FIRST component (a function) to
witnesses extracted from the SECOND — neither half is discardable there.
Honesty about what did NOT change: L1 (`no_seed_discharged`) still proves
its conclusion from `SnapshotSound S` alone, because that fact — `hfiber`
kills every `SnapshotSound` scheme for `φ_bind`, full stop — is genuinely
`m`-independent; no amount of definitional cleverness makes it otherwise, and
claiming L1 itself was the joint witness would repeat round 1's mistake in a
different sentence. The joint content lives in `discharges_forces_binding`
and `discharges_seed_iff_certifies_empty`, not in L1.

Neither `Instance.Identity` nor `Instance.SuretyLite` discharges (R1)/(R2)
here: their real records (the eml chain, the atom DAG) live outside this
repository's TCB (cited, never vendored, per `AGENTS.md`). Both thread `ρ` as
an explicit, unconstructed hypothesis — the same discipline `hfiber` already
uses.
-/

namespace Ceiling

open EonEalm

variable {Payload : Type}

-- ===========================================================================
-- RecordRealization — the missing embedding
-- ===========================================================================

/-- **A record realization**: the domain-supplied map from the accounting
    world into the scheme world, subject to (R1) dependency-order
    faithfulness and (R2) the seed boundary. Bundled as a structure —
    function plus the properties it must satisfy — mirroring
    `EonEalm.Commitment`'s own shape; never constructed in the neutral core,
    always supplied (or, short of that, taken as an explicit hypothesis) by
    the instance whose record it is. -/
structure RecordRealization (Payload : Type) where
  /-- The embedding itself. -/
  recordOf : Node Payload → Record
  /-- (R1) Dependency-order faithfulness: growing the accounting closure
      grows the record. -/
  faithful : ∀ m n : Node Payload, m ∈ depclosure n → recordOf m ⊑ recordOf n
  /-- (R2) The seed boundary: a seed is exactly a node whose record commits
      no prior entries. -/
  seedBoundary : ∀ m : Node Payload, m.seed? = true ↔ recordOf m = []

section RecordRealizationNonvacuity

/-- The demo realization's range: every ground node not flagged a seed, and
    every derived node, gets the one given entry; every seed gets `[]`. The
    only total function on `Node Unit` that could possibly satisfy (R2)
    without more information than "one entry, if any exist" — and it does,
    unconditionally (`demoRecordOf_faithful`/`demoRecordOf_seedBoundary`
    below), for every closure shape, not just one example. -/
def demoRecordOf (e : Entry) : Node Unit → Record
  | .ground _ true => []
  | .ground _ false => [e]
  | .derived _ _ _ => [e]

theorem demoRecordOf_mem (e : Entry) (m : Node Unit) :
    demoRecordOf e m = [] ∨ demoRecordOf e m = [e] := by
  cases m with
  | ground _ s => cases s <;> simp [demoRecordOf]
  | derived _ _ _ => simp [demoRecordOf]

/-- (R1) for `demoRecordOf`: the only two values it ever takes, `[]` and
    `[e]`, are related `⊑` in every direction that can actually arise — a
    `.ground` node's `depclosure` is only ever itself, so the sole
    nontrivial case is a `.derived` node's own record (always `[e]`)
    against one of its inputs (`[]` or `[e]`, both `⊑ [e]`). -/
theorem demoRecordOf_faithful (e : Entry) :
    ∀ m n : Node Unit, m ∈ depclosure n → demoRecordOf e m ⊑ demoRecordOf e n := by
  intro m n hmem
  cases n with
  | ground i s =>
      simp only [depclosure, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact ext_refl _
  | derived i payload inputs =>
      have hn : demoRecordOf e (Node.derived i payload inputs) = [e] := by simp [demoRecordOf]
      rw [hn]
      rcases demoRecordOf_mem e m with hm | hm
      · rw [hm]; exact ⟨[e], by simp⟩
      · rw [hm]; exact ext_refl _

/-- (R2) for `demoRecordOf`: seed exactly when flagged `true`, by
    definition; the derived case's `[e] ≠ []` closes the other direction. -/
theorem demoRecordOf_seedBoundary (e : Entry) :
    ∀ m : Node Unit, m.seed? = true ↔ demoRecordOf e m = [] := by
  intro m
  cases m with
  | ground i s => cases s <;> simp [demoRecordOf, Node.seed?]
  | derived i p inputs => simp [demoRecordOf, Node.seed?]

/-- **Non-vacuity of `RecordRealization` itself**: R1 and R2 are jointly
    satisfiable, not merely individually statable. Parametric in one
    `Entry` — `Core.Model.Entry` carries no inhabitedness axiom, so this
    (like every entry-parametric witness in the corpus, e.g.
    `Witness.Cells.inclusionClaim`) takes one as a hypothesis rather than
    manufacturing it. -/
def demoRealization (e : Entry) : RecordRealization Unit where
  recordOf := demoRecordOf e
  faithful := demoRecordOf_faithful e
  seedBoundary := demoRecordOf_seedBoundary e

end RecordRealizationNonvacuity

-- ===========================================================================
-- Discharges, round 2 — a genuine relation
-- ===========================================================================

/-- **`Discharges`**: `S : Scheme Γ φ_bind` discharges `m`'s establishment
    without admission — `S` is snapshot-sound for the domain's binding
    claim, AND `S`'s verifier accepts a certificate for `m`'s OWN record
    under the realization `ρ`. Both conjuncts are consumed together in
    `discharges_forces_binding` below — the test round 1 failed. -/
def Discharges {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (ρ : RecordRealization Payload) (S : Scheme Γ φ_bind) (m : Node Payload) : Prop :=
  SnapshotSound S ∧ ∃ c, S.V (Γ.C (ρ.recordOf m)) c

/-- **The joint-consumption witness.** `hsound` (from the FIRST conjunct) is
    a function `∀ w c, S.V (Γ.C w) c → ∀ ξ, φ_bind w ξ`; applying it to `c`
    and `hc` (from the SECOND conjunct, at `w := ρ.recordOf m` specifically
    — `m`'s own record under `ρ`, nothing else) is the one proof step that
    genuinely needs both halves of `Discharges` — the first half alone is a
    function with nothing to apply it to, the second alone is an
    unauthenticated acceptance with no guarantee it means anything. -/
theorem discharges_forces_binding {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (ρ : RecordRealization Payload) (S : Scheme Γ φ_bind) (m : Node Payload)
    (h : Discharges Γ φ_bind ρ S m) : ∀ ξ, φ_bind (ρ.recordOf m) ξ := by
  obtain ⟨hsound, c, hc⟩ := h
  exact hsound (ρ.recordOf m) c hc

/-- **The seed-specific content R2 buys.** For a seed, `Discharges` reduces
    to "S certifies at the EMPTY record" — a fact genuinely different from
    discharging any other node (which would certify at that node's own,
    generally nonempty, record). Uses R2 (`ρ.seedBoundary`) to rewrite
    `ρ.recordOf m` to `[]` under the seed hypothesis — the accounting-side
    flag and the realization's own law combining to produce a scheme-world
    fact, not decoration. -/
theorem discharges_seed_iff_certifies_empty {Comm : Type} (Γ : Commitment Comm)
    (φ_bind : Claim) (ρ : RecordRealization Payload) (S : Scheme Γ φ_bind) (m : Node Payload)
    (hseed : m.seed? = true) :
    Discharges Γ φ_bind ρ S m ↔ SnapshotSound S ∧ ∃ c, S.V (Γ.C []) c := by
  have hrec : ρ.recordOf m = [] := (ρ.seedBoundary m).mp hseed
  rw [Discharges, hrec]

-- ===========================================================================
-- L1 — gate ⇒ nothing is discharged
-- ===========================================================================

/-- **L1.** Under the domain's own `hfiber`, no scheme discharges `m` —
    genuinely `m`-independent: `Discharges` demands `SnapshotSound S`, and
    `hfiber`, via `binding_admits_no_scheme`, rules out every
    `SnapshotSound` scheme for `φ_bind` outright, regardless of which record
    it would have certified. This is exactly the half of `Discharges` that
    does NOT need `ρ` — the half that does is
    `discharges_forces_binding`/`discharges_seed_iff_certifies_empty`. -/
theorem no_seed_discharged {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind) (ρ : RecordRealization Payload)
    (S : Scheme Γ φ_bind) (m : Node Payload) :
    ¬ Discharges Γ φ_bind ρ S m :=
  fun h => binding_admits_no_scheme φ_bind hfiber Γ ⟨S, h.1⟩

-- ===========================================================================
-- Discharges — non-vacuity (positively inhabited, for any realization)
-- ===========================================================================

section DischargesNonvacuity

/-- The trivial binding claim: holds everywhere, hence `Determined` for
    free — used only to witness that `Discharges` is genuinely SATISFIABLE
    in general (contrast `ceiling_nonvacuous` below, where `hfiber` makes it
    never hold): a `Determined` claim admits a snapshot-sound scheme
    (`snapshot_characterization_backward`, `npMembership_trivial`). -/
def trivialClaim : Claim := fun _ _ => True

theorem trivialClaim_determined : Determined trivialClaim := fun _ _ _ => Iff.rfl

theorem trivialClaim_scheme_exists {Comm : Type} (Γ : Commitment Comm) :
    ∃ S : Scheme Γ trivialClaim, SnapshotSound S :=
  snapshot_characterization_backward Γ trivialClaim trivialClaim_determined
    (npMembership_trivial (determinedProj trivialClaim trivialClaim_determined))

/-- `Discharges` is inhabited FOR ANY node `m` and ANY realization `ρ` — not
    just seeds: `trivialClaim`'s scheme accepts a certificate at every
    record (its completeness is unconditional), so applying `S.completeness`
    AT `ρ.recordOf m` specifically produces the second conjunct. This is the
    design's falsification signpost — were `Discharges` identically `False`
    (or the two conjuncts unreachable together), neither L1 nor this witness
    would say anything. -/
theorem discharges_nonvacuous {Comm : Type} (Γ : Commitment Comm)
    (ρ : RecordRealization Payload) (m : Node Payload) :
    ∃ S : Scheme Γ trivialClaim, Discharges Γ trivialClaim ρ S m := by
  obtain ⟨S, hS⟩ := trivialClaim_scheme_exists Γ
  obtain ⟨c, hc⟩ := S.completeness (ρ.recordOf m) default trivial
  exact ⟨S, hS, c, hc⟩

end DischargesNonvacuity

-- ===========================================================================
-- L2 — surface lower bound, genuinely joint
-- ===========================================================================

variable {Tag Signer : Type} [DecidableEq Tag]

/-- **L2 — the quantified-over-schemes claim §1.6(iii) asserts.** For EVERY
    scheme `S : Scheme Γ φ_bind`, every seed `m` in `a`'s closure is
    simultaneously (a) undischargeable by `S` (L1, the scheme-world side)
    and (b) forced into `a`'s trust surface regardless (`seeds_always_
    residual`, the accounting-world side) — the SAME `m`, in the SAME
    theorem, under the SAME hypothesis. Honest about (a): its own proof does
    not need `ρ` (L1 is `m`-independent, see `no_seed_discharged`'s
    docstring) — `ρ` enters L2 only to give `Discharges` a well-typed
    statement to negate. The genuine node/scheme interaction lives in
    `discharges_forces_binding`, not here; what IS new here is `φ_bind` and
    `a` co-occurring in one theorem's conclusion for the first time. -/
theorem seeds_undischargeable_and_residual {Comm : Type} (Γ : Commitment Comm)
    (φ_bind : Claim) (hfiber : ¬ Determined φ_bind) (ρ : RecordRealization Payload)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    ∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind ρ S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a :=
  fun S m hmem hseed =>
    ⟨no_seed_discharged Γ φ_bind hfiber ρ S m,
     seeds_always_residual gate tagOf closureOk P σ a m hmem hseed⟩

-- ===========================================================================
-- L3 — ceiling: minimality attained, not merely bounded
-- ===========================================================================

/-- **L3.** Under `Total a`, the trust surface is EXACTLY the seed members of
    the closure — not merely bounded below by them (`seeds_always_residual`
    gives that unconditionally) but equal, the "minimality attained" reading
    of §1.6(iii)/`.ledger/trichotomy/STATEMENT-rc-v0.7.md` item 4. Promotes
    `total_iff_every_nonseed_closed` (`Ceiling/Accounting.lean:72`, today
    accounting-internal) to the companion theorem's own vocabulary
    (`trustSurface`/seed-filter over `depclosure`). -/
theorem ceiling_minimality (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) :
    Total gate tagOf closureOk P σ a ↔
      trustSurface gate tagOf closureOk P σ a = (depclosure a).filter (fun m => m.seed?) := by
  constructor
  · intro hTotal
    have hnonseed := (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal
    show (depclosure a).filter (fun m => !decide (classify gate tagOf closureOk P σ m = .closed)) =
        (depclosure a).filter (fun m => m.seed?)
    apply List.filter_congr
    intro m hmem
    by_cases hseed : m.seed? = true
    · simp [hseed, seeds_are_imports gate tagOf closureOk P σ m hseed]
    · have hnotseed : m.seed? = false := by simpa using hseed
      simp [hnotseed, hnonseed m hmem hnotseed]
  · intro heq
    apply (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mpr
    intro m hmem hnotseed
    by_cases hnc : classify gate tagOf closureOk P σ m = .closed
    · exact hnc
    · exfalso
      have hmemSurface : m ∈ trustSurface gate tagOf closureOk P σ a := by
        simp only [trustSurface, List.mem_filter]
        exact ⟨hmem, by simp [hnc]⟩
      rw [heq] at hmemSurface
      simp only [List.mem_filter] at hmemSurface
      rw [hmemSurface.2] at hnotseed
      exact absurd hnotseed (by simp)

-- ===========================================================================
-- Growth alignment (item 5) — resolved in two halves
-- ===========================================================================

/-- Evidence-snapshot extension: `σ` grows into `σ'` when every entry of `σ`
    is also present in `σ'` — a SET-growth order (evidence accumulates; a
    later corroboration or vouch never displaces one already admitted), not
    the record-world's sequential PREFIX order `⊑`. Stated as a plain
    quantifier, not `List.Subset`/`⊆`, so this file adds no dependency on
    which `List` API surface happens to carry that notation. -/
def SnapshotExt (σ σ' : Snapshot Signer Tag) : Prop := ∀ e ∈ σ, e ∈ σ'

omit [DecidableEq Tag] in
theorem corroborated_mono_snapshot {σ σ' : Snapshot Signer Tag} (hext : SnapshotExt σ σ')
    (P : Policy Signer) (m : Node Payload) (h : corroborated P σ m = true) :
    corroborated P σ' m = true := by
  simp only [corroborated, List.any_eq_true] at h ⊢
  obtain ⟨e, he, hmatch⟩ := h
  exact ⟨e, hext e he, hmatch⟩

theorem established_mono_snapshot {σ σ' : Snapshot Signer Tag} (hext : SnapshotExt σ σ')
    (gate : Payload → Bool) (tagOf : Payload → Tag) (P : Policy Signer)
    (id : Nat) (payload : Payload) (h : established gate tagOf P σ id payload = true) :
    established gate tagOf P σ' id payload = true := by
  simp only [established, Bool.and_eq_true_iff, List.any_eq_true] at h ⊢
  obtain ⟨hgate, e, he, hmatch⟩ := h
  exact ⟨hgate, e, hext e he, hmatch⟩

/-- **Growth alignment, accounting-internal half — aligns for free.**
    `classify`'s admission predicates only ever test "does σ contain a
    matching admitted entry," never its absence, so growing σ can only turn
    `.closed` into `.closed` again, never undo it — proved by the SAME
    well-founded recursion `classify` itself uses. -/
theorem classify_closed_mono_snapshot (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) :
    ∀ {σ σ' : Snapshot Signer Tag}, SnapshotExt σ σ' → ∀ m : Node Payload,
      classify gate tagOf closureOk P σ m = .closed →
      classify gate tagOf closureOk P σ' m = .closed
  | σ, σ', _, .ground i _, h => by simp [classify] at h
  | σ, σ', hext, .derived i payload inputs, h => by
      have hpieces :
          established gate tagOf P σ i payload = true ∧
          closureOk payload = true ∧
          corroborated P σ (Node.derived i payload inputs) = true ∧
          (inputs.attach.all fun p =>
            p.1.seed? || decide (classify gate tagOf closureOk P σ p.1 = .closed)) = true := by
        simp only [classify] at h
        by_cases he : established gate tagOf P σ i payload = true
        · simp only [he, Bool.not_true, if_neg (by simp : ¬ ((false : Bool) = true))] at h
          by_cases hc :
              (closureOk payload && corroborated P σ (Node.derived i payload inputs) &&
                inputs.attach.all fun p =>
                  p.1.seed? || decide (classify gate tagOf closureOk P σ p.1 = .closed)) = true
          · simp only [Bool.and_eq_true_iff] at hc
            exact ⟨he, hc.1.1, hc.1.2, hc.2⟩
          · simp [hc] at h
        · simp [he] at h
      obtain ⟨hest, hco, hcorr, hrec⟩ := hpieces
      have hest' := established_mono_snapshot hext gate tagOf P i payload hest
      have hcorr' := corroborated_mono_snapshot hext P (Node.derived i payload inputs) hcorr
      have hrec' :
          (inputs.attach.all fun p =>
            p.1.seed? || decide (classify gate tagOf closureOk P σ' p.1 = .closed)) = true := by
        rw [List.all_eq_true] at hrec ⊢
        intro x hx
        have hx' := hrec x hx
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hx' ⊢
        rcases hx' with hseed | hc2
        · exact Or.inl hseed
        · exact Or.inr (classify_closed_mono_snapshot gate tagOf closureOk P hext x.1 hc2)
      show classify gate tagOf closureOk P σ' (Node.derived i payload inputs) = .closed
      simp [classify, hest', hco, hcorr', hrec']
termination_by σ σ' _hext m _h => sizeOf m
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem x.2
  omega

/-- The `Total` corollary: totality, once achieved, survives every further
    extension of the evidence snapshot. -/
theorem total_mono_snapshot (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) {σ σ' : Snapshot Signer Tag}
    (hext : SnapshotExt σ σ') (a : Node Payload) (hTotal : Total gate tagOf closureOk P σ a) :
    Total gate tagOf closureOk P σ' a := by
  rw [total_iff_every_nonseed_closed] at hTotal ⊢
  intro m hmem hnotseed
  exact classify_closed_mono_snapshot gate tagOf closureOk P hext m (hTotal m hmem hnotseed)

/-! **Growth alignment, cross-domain half — resolved by `RecordRealization`
above.** "Record extension `⊑`" is an order on `EonEalm.Record`;
`SnapshotExt` above is an order on `Ceiling.Snapshot Signer Tag` — the two
stay genuinely disjoint (this section's `SnapshotExt` facts are unconditional
and never need a realization at all). What was previously reported as "no
hypothesis in this package can make it align" is now specified precisely:
`RecordRealization`'s own (R1) IS the growth-alignment hypothesis —
`ρ.faithful` is literally "`depclosure`-membership transports to `⊑`."
`growth_alignment` below is the `Monotone` consequence of R1, stated
directly in `depclosure`'s own vocabulary rather than a bare `⊑` hypothesis.
Whether any GIVEN domain's realization exists is instance work
(`Instance.Identity`/`Instance.SuretyLite` thread `ρ` unconstructed, same
discipline as `hfiber`) — not further mathematics owed by the neutral core. -/

/-- **Growth alignment.** Given a realization `ρ` and `φ_bind` `Monotone`:
    `φ_bind` holding at `m`'s record transports to any `n` with `m` in its
    dependency closure — accounting-world growth (`depclosure` membership)
    forces scheme-world growth (`⊑`) via (R1), and `Monotone` does the rest. -/
theorem growth_alignment {Payload : Type} (φ_bind : Claim) (hmono : Monotone φ_bind)
    (ρ : RecordRealization Payload) (m n : Node Payload) (hmem : m ∈ depclosure n)
    (ξ : Context) (h : φ_bind (ρ.recordOf m) ξ) :
    φ_bind (ρ.recordOf n) ξ :=
  hmono (ρ.recordOf m) (ρ.recordOf n) ξ h (ρ.faithful m n hmem)

-- ===========================================================================
-- `ceiling`, restated — φ_bind and a genuinely linked
-- ===========================================================================

/-- **`ceiling`, superseding `Ceiling.Gate.ceiling`.** The companion display:
    the gate (i); the quantified-over-schemes seed junction (L2); the
    ceiling's minimality equality (L3); and completeness (ii, unchanged from
    the old bundle, `total_carries_both_species`). `ρ` is threaded through
    for `Discharges` to be well-typed — supplied by the caller (an instance)
    or, absent one, taken as an explicit hypothesis exactly like `hfiber`. -/
theorem ceiling {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind) (ρ : RecordRealization Payload)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    (¬ ∃ S : Scheme Γ φ_bind, SnapshotSound S) ∧
    (∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind ρ S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a) ∧
    (Total gate tagOf closureOk P σ a →
      trustSurface gate tagOf closureOk P σ a = (depclosure a).filter (fun m => m.seed?)) ∧
    (Total gate tagOf closureOk P σ a →
      ∀ m ∈ depclosure a, m.seed? = false →
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t, e = .corroboration s t) ∧
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t tag, e = .vouch s t tag)) :=
  ⟨binding_admits_no_scheme φ_bind hfiber Γ,
   seeds_undischargeable_and_residual Γ φ_bind hfiber ρ gate tagOf closureOk P σ a,
   fun hTotal => (ceiling_minimality gate tagOf closureOk P σ a).mp hTotal,
   fun hTotal m hmem hnotSeed =>
     total_carries_both_species gate tagOf closureOk P σ a hTotal m hmem hnotSeed⟩

-- ===========================================================================
-- Non-vacuity for the junction itself
-- ===========================================================================

section Nonvacuity

/-- The witness closure: a single derived node closing directly onto the
    genesis seed — the neutral core's own instance of the `SuretyLite`/
    `Identity` W2 shape, reused here so the junction's non-vacuity does not
    depend on either instance package. -/
def wNode : Node Unit := .derived 1 () [Node.ground 0 true]

def wPolicy : Policy Unit := ⟨fun _ => true, fun _ => true⟩
def wSnap : Snapshot Unit Unit := [.vouch () 1 (), .corroboration () 1]
def wGate : Unit → Bool := fun _ => true
def wTagOf : Unit → Unit := fun _ => ()
def wClosureOk : Unit → Bool := fun _ => true

theorem wNode_total : Total wGate wTagOf wClosureOk wPolicy wSnap wNode := by
  apply (total_iff_every_nonseed_closed wGate wTagOf wClosureOk wPolicy wSnap wNode).mpr
  intro m hmem hnotseed
  have hlist : depclosure wNode = [Node.derived 1 () [Node.ground 0 true], Node.ground 0 true] := by
    show depclosure (Node.derived 1 () [Node.ground 0 true]) = _
    rw [depclosure]; simp [depclosure]
  rw [hlist] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · simp [Ceiling.classify, established, corroborated, wGate, wTagOf, wClosureOk,
      wPolicy, wSnap, Node.id, Node.seed?]
  · simp [Node.seed?] at hnotseed

/-- **Non-vacuity for `ceiling` itself**, in the corpus's own style
    (`comp_COMP_nonvacuous`, `Effective/Trichotomy.lean:410`; the axios
    `SuretyCeiling/Nonvacuity.lean` pattern): a genuinely undetermined
    `φ_bind` — `Core.Axes.exists_undetermined_claim`'s witness, reused
    rather than re-extracted, so this file adds no new consumption site for
    `Context.nontrivial` (`Core.lean`'s three-site accounting stays
    accurate) — over a genuine `Total` closure (`wNode_total`) and a genuine
    `RecordRealization` (`demoRealization e`, parametric in one `Entry`),
    with every conjunct of the restated `ceiling` firing on real data. -/
theorem ceiling_nonvacuous (e : Entry) :
    ∃ (φ_bind : Claim), ¬ Determined φ_bind ∧
      (¬ ∃ S : Scheme idCommitment φ_bind, SnapshotSound S) ∧
      (∀ S : Scheme idCommitment φ_bind, ∀ m ∈ depclosure wNode, m.seed? = true →
        ¬ Discharges idCommitment φ_bind (demoRealization e) S m ∧
          m ∈ trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode) ∧
      trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode =
        (depclosure wNode).filter (fun m => m.seed?) := by
  obtain ⟨φ_bind, hnd⟩ := exists_undetermined_claim
  exact ⟨φ_bind, hnd, binding_admits_no_scheme φ_bind hnd idCommitment,
    seeds_undischargeable_and_residual idCommitment φ_bind hnd (demoRealization e) wGate wTagOf
      wClosureOk wPolicy wSnap wNode,
    (ceiling_minimality wGate wTagOf wClosureOk wPolicy wSnap wNode).mp wNode_total⟩

end Nonvacuity

end Ceiling

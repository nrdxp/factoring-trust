import Core
import Ceiling.Gate

/-!
# Ceiling — Junction: the gate's scheme-world result forces the accounting-world
# trust surface to contain the seeds, for every scheme

`Ceiling.Gate`'s old `ceiling` bundled three facts sharing the argument names
`φ_bind : Claim` and `a : Node Payload` without ever relating them: the gate
(`binding_admits_no_scheme`, entirely about `φ_bind`) sat next to
`seeds_always_residual`/`total_carries_both_species` (entirely about `a`), a
conjunction, not a theorem. `.ledger/trichotomy/STATEMENT-rc-v0.7.md`
v0.7 AMENDMENT 1 names this the unmechanized "therefore" of §1.6(iii): the
trust surface `T(a)` contains the seed set for EVERY scheme. This file builds
the missing junction and supersedes `Ceiling.Gate.ceiling` with the version
that actually proves it.

## `Discharges` — the one genuine design decision

**What it means for `S` to discharge `m`'s establishment without admission.**
A seed (`Ceiling.Node.ground`) carries no payload and hence no
`established`/vouch machinery at all (`Ceiling.Classify.classify`'s `.ground`
case is unconditional `.import` — there is nothing there to bypass). The
ONLY conceivable admission-free path for a seed is a scheme that certifies
the domain's binding claim `φ_bind` directly from the committed record, with
no testimony: `Discharges` says exactly this — `S` is snapshot-sound for
`φ_bind`, AND `m` is a node whose establishment currently rests on admission
alone. `m` is not decoration: `discharges_requires_seed` below proves,
UNCONDITIONALLY (no `hfiber` needed), that `Discharges` is false at every
non-seed `m` — the predicate genuinely discriminates by node shape, the
exact thing a vacuous "`Discharges S m := SnapshotSound S`" (ignoring `m`)
would fail to do. `discharges_nonvacuous` below shows the OTHER half: for a
`Determined` claim (no `hfiber`), `Discharges` is genuinely SATISFIABLE — so
L1's "no seed is discharged" is a real consequence of `hfiber`, not a
tautology of the definition.

Rejected alternative (the axios `SuretyEonEalm` pattern, explicitly ruled
out by the statement): identifying `φ_bind` with a domain predicate via a
bare `def` and citing the gate contrapositively. That pattern never
introduces a relation between `Scheme Γ φ_bind` and `Node Payload` at
all — it restates `binding_admits_no_scheme` under a new name. `Discharges`
is a genuinely new cross-domain type (`Scheme Γ φ_bind → Node Payload →
Prop`) with its own non-vacuity story on both sides.
-/

namespace Ceiling

open EonEalm

variable {Payload : Type}

/-- **`Discharges`**: `S : Scheme Γ φ_bind` discharges `m`'s establishment
    without admission — `S` is snapshot-sound for the domain's binding claim,
    and `m` is exactly the kind of node (a seed) whose establishment is
    otherwise carried by admission alone, with no evidence machinery of its
    own to bypass. -/
def Discharges {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (S : Scheme Γ φ_bind) (m : Node Payload) : Prop :=
  m.seed? = true ∧ SnapshotSound S

/-- `m` is not decoration in `Discharges`: a non-seed is never discharged,
    UNCONDITIONALLY — no `hfiber`, no fact about `S` at all. This is the
    complementary half to `binding_admits_no_scheme`'s route (which kills
    `Discharges` via the scheme side): here the accounting side alone
    already rules out every non-seed, showing the seed-restriction is a
    real discriminator and not an unused conjunct. -/
theorem discharges_requires_seed {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (S : Scheme Γ φ_bind) (m : Node Payload) (hnotseed : m.seed? = false) :
    ¬ Discharges Γ φ_bind S m :=
  fun h => absurd h.1 (by simp [hnotseed])

-- ===========================================================================
-- L1 — gate ⇒ seeds undischargeable
-- ===========================================================================

/-- **L1.** Under the domain's own `hfiber`, no scheme discharges `m` — in
    fact this holds regardless of `m`'s seed status, since `Discharges`
    always demands `SnapshotSound S` and `hfiber`, via
    `binding_admits_no_scheme`, rules out every `SnapshotSound` scheme for
    `φ_bind` outright. Named at seed `m` because that is where (i) finally
    does work on the accounting side (a seed's establishment has no other
    conceivable admission-free path to close off) — the general form is
    strictly stronger and specializes there. -/
theorem no_seed_discharged {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind) (S : Scheme Γ φ_bind) (m : Node Payload) :
    ¬ Discharges Γ φ_bind S m :=
  fun h => binding_admits_no_scheme φ_bind hfiber Γ ⟨S, h.2⟩

-- ===========================================================================
-- Discharges — non-vacuity (both directions)
-- ===========================================================================

section DischargesNonvacuity

/-- The trivial binding claim: holds everywhere, hence `Determined` for
    free — used only to witness that `Discharges` is genuinely SATISFIABLE
    in general (contrast `ceiling_nonvacuous` below, where `hfiber` makes it
    never hold): a `Determined` claim admits a snapshot-sound scheme
    (`snapshot_characterization_backward`, `npMembership_trivial`), and
    pairing that scheme with any seed genuinely discharges it. -/
def trivialClaim : Claim := fun _ _ => True

theorem trivialClaim_determined : Determined trivialClaim := fun _ _ _ => Iff.rfl

theorem trivialClaim_scheme_exists {Comm : Type} (Γ : Commitment Comm) :
    ∃ S : Scheme Γ trivialClaim, SnapshotSound S :=
  snapshot_characterization_backward Γ trivialClaim trivialClaim_determined
    (npMembership_trivial (determinedProj trivialClaim trivialClaim_determined))

/-- `Discharges` is inhabited: a `Determined` claim's snapshot-sound scheme
    discharges any seed. This is the design's falsification signpost — were
    `Discharges` identically `False` (or identically `True`), neither L1 nor
    this witness would say anything; both directions are load-bearing. -/
theorem discharges_nonvacuous {Comm : Type} (Γ : Commitment Comm) :
    ∃ S : Scheme Γ trivialClaim,
      Discharges Γ trivialClaim S (Node.ground (Payload := Payload) 0 true) := by
  obtain ⟨S, hS⟩ := trivialClaim_scheme_exists Γ
  exact ⟨S, rfl, hS⟩

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
    theorem, under the SAME hypothesis. This is `φ_bind` and `a` genuinely
    linked: the old `ceiling`'s three unrelated facts, fused. -/
theorem seeds_undischargeable_and_residual {Comm : Type} (Γ : Commitment Comm)
    (φ_bind : Claim) (hfiber : ¬ Determined φ_bind)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    ∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a :=
  fun S m hmem hseed =>
    ⟨no_seed_discharged Γ φ_bind hfiber S m,
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

/-! **Growth alignment, cross-domain half — does NOT align, and no
hypothesis in this package can make it.** "Record extension `⊑`" is an
order on `EonEalm.Record`; `SnapshotExt` above is an order on
`Ceiling.Snapshot Signer Tag` — two disjoint types with no map between them
anywhere in the neutral core (`Ceiling.Node` carries no `Record` field;
`φ_bind` is evaluated at a `Record` the accounting side never produces). A
correspondence claim between them does not even TYPECHECK without first
supplying an embedding — exactly the M9/M10-scale domain-neutral-core work
the statement's §3 flags as future work, out of this dispatch's surface.
`growth_alignment_conditional` below states the missing hypothesis
EXPLICITLY (an embedding, `recordOf`) rather than smuggling it into a
definition or introducing an axiom: GIVEN such an embedding, alignment is
immediate (`Monotone` transports through any map) — the open content is
purely the embedding's existence and its own growth-preservation law, not
any further mathematical work. -/

/-- **Growth alignment, conditional on a domain-supplied embedding.** If a
    `recordOf : Node Payload → Record` carries the accounting world's own
    growth notion (whatever the domain's `hgrows : recordOf m ⊑ recordOf m'`
    turns out to mean — this file does not construct one) into `⊑`, and
    `φ_bind` is `Monotone`, then `φ_bind` holding at `recordOf m` transports
    to `recordOf m'`. No such `recordOf` is constructed here — the theorem
    exists to name exactly what is missing, not to discharge it. -/
theorem growth_alignment_conditional {Payload : Type} (φ_bind : Claim)
    (hmono : Monotone φ_bind) (recordOf : Node Payload → Record) (m m' : Node Payload)
    (hgrows : recordOf m ⊑ recordOf m') (ξ : Context) (h : φ_bind (recordOf m) ξ) :
    φ_bind (recordOf m') ξ :=
  hmono (recordOf m) (recordOf m') ξ h hgrows

-- ===========================================================================
-- `ceiling`, restated — φ_bind and a genuinely linked
-- ===========================================================================

/-- **`ceiling`, superseding `Ceiling.Gate.ceiling`.** The companion display,
    now with the "therefore" proved: the gate (i); the quantified-over-
    schemes seed junction (L2, the new content — `φ_bind`'s scheme-world
    non-existence forces `a`'s accounting-world trust surface to hold every
    seed, for every `S`); the ceiling's minimality equality (L3); and
    completeness (ii, unchanged from the old bundle,
    `total_carries_both_species`). No conjunct here is independent of the
    others' vocabulary the way the old bundle's were: L2's own statement
    mentions both `Scheme Γ φ_bind` and `trustSurface … a` together. -/
theorem ceiling {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    (¬ ∃ S : Scheme Γ φ_bind, SnapshotSound S) ∧
    (∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a) ∧
    (Total gate tagOf closureOk P σ a →
      trustSurface gate tagOf closureOk P σ a = (depclosure a).filter (fun m => m.seed?)) ∧
    (Total gate tagOf closureOk P σ a →
      ∀ m ∈ depclosure a, m.seed? = false →
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t, e = .corroboration s t) ∧
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t tag, e = .vouch s t tag)) :=
  ⟨binding_admits_no_scheme φ_bind hfiber Γ,
   seeds_undischargeable_and_residual Γ φ_bind hfiber gate tagOf closureOk P σ a,
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
    accurate) — over a genuine `Total` closure (`wNode_total`), with every
    conjunct of the restated `ceiling` firing on real data: the gate
    excludes every scheme; the seed is named, undischargeable, and resident;
    the minimality equality actually holds, not just typechecks. -/
theorem ceiling_nonvacuous :
    ∃ (φ_bind : Claim), ¬ Determined φ_bind ∧
      (¬ ∃ S : Scheme idCommitment φ_bind, SnapshotSound S) ∧
      (∀ S : Scheme idCommitment φ_bind, ∀ m ∈ depclosure wNode, m.seed? = true →
        ¬ Discharges idCommitment φ_bind S m ∧
          m ∈ trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode) ∧
      trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode =
        (depclosure wNode).filter (fun m => m.seed?) := by
  obtain ⟨φ_bind, hnd⟩ := exists_undetermined_claim
  exact ⟨φ_bind, hnd, binding_admits_no_scheme φ_bind hnd idCommitment,
    seeds_undischargeable_and_residual idCommitment φ_bind hnd wGate wTagOf wClosureOk wPolicy
      wSnap wNode,
    (ceiling_minimality wGate wTagOf wClosureOk wPolicy wSnap wNode).mp wNode_total⟩

end Nonvacuity

end Ceiling

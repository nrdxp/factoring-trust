import Ceiling.Classify

/-!
# Ceiling — Accounting: the trust surface, the assumption basis, and `Total`

Mirrors the axios `docs/models/lean-surety/SuretyCeiling/Ceiling.lean`'s
accounting layer over `Ceiling.Classify`'s inductive `classify`, generalized off the
domain-specific field list onto the abstract `Payload`/`gate`/`tagOf`/
`closureOk` parametrization.
-/

namespace Ceiling

variable {Payload Tag Signer : Type} [DecidableEq Tag]

/-- **The trust surface `T(a)`**: the closure minus its `closed` members —
    every node that classifies into one of the three residue buckets. -/
def trustSurface (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    List (Node Payload) :=
  (depclosure a).filter fun m => !decide (classify gate tagOf closureOk P σ m = .closed)

/-- **The assumption basis `B(a)`**: the policy-admitted evidence the walk's
    non-residue classifications rest on — a counted corroboration for each
    `closed` member of `depclosure a`, and a counted vouch for each
    established member of `depclosure a`. (The genesis-seed identities
    themselves are a set of *nodes*, not evidence — read directly off
    `depclosure a` filtered by `Node.seed?`, not folded into this list.) -/
def basis (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    Snapshot Signer Tag :=
  σ.filter fun e => match e with
    | .corroboration s t =>
        P.admittedCorroborator s &&
          (depclosure a).any fun m =>
            decide (m.id = t) && decide (classify gate tagOf closureOk P σ m = .closed)
    | .vouch s t tag =>
        P.admittedVoucher s &&
          (depclosure a).any fun m =>
            decide (m.id = t) &&
              match m with
              | .derived _ payload _ =>
                  decide (tag = tagOf payload) && established gate tagOf P σ m.id payload
              | .ground .. => false

/-- **`Total(a)`**: the trust surface contains nothing but genesis seeds —
    every non-seed closure member is `closed`. -/
def Total (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) : Prop :=
  ∀ m ∈ trustSurface gate tagOf closureOk P σ a, m.seed? = true

-- ===========================================================================
-- Completeness
-- ===========================================================================

/-- A seed anywhere in `a`'s closure sits in `a`'s trust surface regardless of
    `σ` and `P` — structural: seeds classify `import`, never `closed`. -/
theorem seeds_always_residual (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a m : Node Payload) (hmem : m ∈ depclosure a) (hseed : m.seed? = true) :
    m ∈ trustSurface gate tagOf closureOk P σ a := by
  simp only [trustSurface, List.mem_filter]
  refine ⟨hmem, ?_⟩
  have : classify gate tagOf closureOk P σ m = .import :=
    seeds_are_imports gate tagOf closureOk P σ m hseed
  simp [this]

/-- **`total_iff_every_nonseed_closed`**: `Total a` holds iff every non-seed
    member of `a`'s closure classifies `closed` — the direct unfolding of
    "the trust surface contains nothing but seeds," bypassing the
    `trustSurface` filter at call sites. -/
theorem total_iff_every_nonseed_closed (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) :
    Total gate tagOf closureOk P σ a ↔
      ∀ m ∈ depclosure a, m.seed? = false → classify gate tagOf closureOk P σ m = .closed := by
  constructor
  · intro hTotal m hmem hnotseed
    by_cases hnc : classify gate tagOf closureOk P σ m = .closed
    · exact hnc
    · exact absurd (hTotal m (by simp only [trustSurface, List.mem_filter]; exact ⟨hmem, by simp [hnc]⟩))
        (by simp [hnotseed])
  · intro h m hmemSurface
    simp only [trustSurface, List.mem_filter] at hmemSurface
    obtain ⟨hmem, hnc⟩ := hmemSurface
    by_cases hnotseed : m.seed? = true
    · exact hnotseed
    · exact absurd (h m hmem (by simpa using hnotseed)) (by simpa using hnc)

/-- One unclosed non-seed member anywhere in the closure defeats `Total` —
    the safety display (the reference's `laundered_never_total`,
    neutralized): a node whose verification did not close cannot be hidden
    by any policy or snapshot; it sits in the trust surface and `Total`
    fails. The contrapositive of `total_iff_every_nonseed_closed`'s forward
    direction, named because it is the sentence instances quote against
    their defeated-`Total` witnesses. -/
theorem unclosed_member_defeats_total (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a m : Node Payload) (hmem : m ∈ depclosure a) (hnotSeed : m.seed? = false)
    (hnc : classify gate tagOf closureOk P σ m ≠ .closed) :
    ¬ Total gate tagOf closureOk P σ a :=
  fun hTotal =>
    hnc ((total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal m hmem hnotSeed)

/-- Every `closed` member of `a`'s closure carries a policy-admitted
    corroboration **targeting that member** enumerated in `basis a` — the
    derived-species half of the two-species story (surety's reference proved
    only the vouch half). The conclusion is pinned to `m` through `m.id`,
    which is what `Evidence` targets (`Ceiling.Node.id`): an unrelated
    corroboration sitting elsewhere in the basis does not discharge it. -/
theorem closed_carries_corroboration_in_basis (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a m : Node Payload) (hmem : m ∈ depclosure a)
    (hclosed : classify gate tagOf closureOk P σ m = .closed) :
    ∃ s, Evidence.corroboration (Tag := Tag) s m.id ∈ basis gate tagOf closureOk P σ a := by
  have hcorr : corroborated P σ m = true := by
    cases m with
    | ground i isSeed => simp [classify] at hclosed
    | derived i payload inputs =>
        exact (declaration_alone_never_closes gate tagOf closureOk P σ i payload inputs hclosed).2
  simp only [corroborated, List.any_eq_true] at hcorr
  obtain ⟨e, heσ, hematch⟩ := hcorr
  cases e with
  | corroboration s t =>
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hematch
      obtain ⟨hadm, ht⟩ := hematch
      subst ht
      refine ⟨s, ?_⟩
      simp only [basis, List.mem_filter]
      refine ⟨heσ, ?_⟩
      simp only [hadm, Bool.true_and, List.any_eq_true]
      exact ⟨m, hmem, by simp [hclosed]⟩
  | vouch s t tag => simp at hematch

/-- Every `closed` member of `a`'s closure carries a policy-admitted vouch
    **for that member's own `id` at that member's own tag** enumerated in
    `basis a` — the asserted-species half. Stated on the `derived`
    constructor, like `declaration_alone_never_closes`, because the vouched
    tag is `tagOf` the member's OWN payload and only that constructor has
    one; `ground` nodes never classify `closed` (`ground_forced_import`), so
    nothing is lost. -/
theorem closed_carries_vouch_in_basis (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) (i : Nat) (payload : Payload) (inputs : List (Node Payload))
    (hmem : Node.derived i payload inputs ∈ depclosure a)
    (hclosed : classify gate tagOf closureOk P σ (Node.derived i payload inputs) = .closed) :
    ∃ s, Evidence.vouch s i (tagOf payload) ∈ basis gate tagOf closureOk P σ a := by
  have hest :=
    (declaration_alone_never_closes gate tagOf closureOk P σ i payload inputs hclosed).1
  have hunfold := hest
  simp only [established] at hunfold
  obtain ⟨_, hv⟩ := Bool.and_eq_true_iff.mp hunfold
  simp only [List.any_eq_true] at hv
  obtain ⟨e, heσ, hematch⟩ := hv
  cases e with
  | vouch s t tag =>
      simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at hematch
      obtain ⟨⟨hsv, htv⟩, htagv⟩ := hematch
      subst htv
      subst htagv
      refine ⟨s, ?_⟩
      simp only [basis, List.mem_filter]
      refine ⟨heσ, ?_⟩
      simp only [hsv, Bool.true_and, List.any_eq_true]
      exact ⟨_, hmem, by simp [Node.id, hest]⟩
  | corroboration s t => simp at hematch

/-- Packaged enumeration: under `Total a`, EVERY non-seed member of `a`'s
    closure is `derived` and carries both evidence species in `basis a`,
    each pinned to THAT member — a corroboration targeting its own `id`, and
    a vouch for its own `id` at `tagOf` its own payload. `Total` forces each
    non-seed member `closed` (`total_iff_every_nonseed_closed`) and a
    `closed` member is never `ground` (`ground_forced_import`), from which
    both per-member halves above apply. This is the "nothing is silently
    trusted at the ceiling" display: the enumeration ranges over the whole
    closure, not just the root, and a counted item can stand in for another
    member only where the two share an `id` — i.e. are the same principal
    under the model's identity notion, which is exactly what `Evidence`
    targets (`Ceiling.Node.id`); the vouch half pins the member's `tagOf`
    payload besides. It needs `Total` nontrivially (an unclosed member has
    no counted evidence to enumerate). The root-only reading follows at
    `m := a` via `self_mem_depclosure`. -/
theorem total_carries_both_species (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) (hTotal : Total gate tagOf closureOk P σ a)
    (m : Node Payload) (hmem : m ∈ depclosure a) (hnotSeed : m.seed? = false) :
    ∃ i payload inputs, m = .derived i payload inputs ∧
      (∃ s, Evidence.corroboration (Tag := Tag) s i ∈ basis gate tagOf closureOk P σ a) ∧
      (∃ s, Evidence.vouch s i (tagOf payload) ∈ basis gate tagOf closureOk P σ a) := by
  have hclosed : classify gate tagOf closureOk P σ m = .closed :=
    (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal m hmem hnotSeed
  cases m with
  | ground i isSeed =>
      rw [ground_forced_import] at hclosed
      exact absurd hclosed (by decide)
  | derived i payload inputs =>
      refine ⟨i, payload, inputs, rfl, ?_,
        closed_carries_vouch_in_basis gate tagOf closureOk P σ a i payload inputs hmem hclosed⟩
      simpa [Node.id] using
        closed_carries_corroboration_in_basis gate tagOf closureOk P σ a _ hmem hclosed

-- ===========================================================================
-- Non-vacuity (the generic satisfiability-sense pattern)
-- ===========================================================================

/-- A policy admitting no vouchers at all forbids every non-seed `Total`:
    establishment always requires an admitted vouch, so no non-seed node can
    classify `closed`, and `total_iff_every_nonseed_closed` then forces every
    non-seed `a` out of `Total`. -/
theorem no_vouchers_no_total (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (hempty : ∀ s, P.admittedVoucher s = false)
    (a : Node Payload) (hnotSeed : a.seed? = false) :
    ¬ Total gate tagOf closureOk P σ a := by
  intro hTotal
  have hclosed : classify gate tagOf closureOk P σ a = .closed :=
    (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal a
      (self_mem_depclosure a) hnotSeed
  cases a with
  | ground i isSeed =>
      have himport := ground_forced_import gate tagOf closureOk P σ i isSeed
      rw [himport] at hclosed
      exact absurd hclosed (by decide)
  | derived i payload inputs =>
      have hest :=
        (declaration_alone_never_closes gate tagOf closureOk P σ i payload inputs hclosed).1
      simp only [established, Bool.and_eq_true_iff] at hest
      obtain ⟨_, hv⟩ := hest
      simp only [List.any_eq_true] at hv
      obtain ⟨e, _heσ, hematch⟩ := hv
      cases e with
      | vouch s t tag =>
          simp only [Bool.and_eq_true_iff] at hematch
          exact absurd hematch.1.1 (by simp [hempty s])
      | corroboration s t => simp at hematch

end Ceiling

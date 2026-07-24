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
    corroboration enumerated in `basis a` — the derived-species half of the
    two-species story (surety's reference proved only the vouch half). -/
theorem closed_carries_corroboration_in_basis (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a m : Node Payload) (hmem : m ∈ depclosure a)
    (hclosed : classify gate tagOf closureOk P σ m = .closed) :
    ∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t, e = .corroboration s t := by
  have hcorr : corroborated P σ m = true := by
    cases m with
    | ground i isSeed => simp [classify] at hclosed
    | derived i payload inputs =>
        exact (declaration_alone_never_closes gate tagOf closureOk P σ i payload inputs hclosed).2
  simp only [corroborated, List.any_eq_true] at hcorr
  obtain ⟨e, heσ, hematch⟩ := hcorr
  cases e with
  | corroboration s t =>
      refine ⟨.corroboration s t, ?_, s, t, rfl⟩
      simp only [basis, List.mem_filter]
      refine ⟨heσ, ?_⟩
      simp only [Bool.and_eq_true_iff] at hematch
      simp only [hematch.1, Bool.true_and, List.any_eq_true]
      exact ⟨m, hmem, by simp [hclosed, (of_decide_eq_true hematch.2).symm]⟩
  | vouch s t tag => simp at hematch

/-- Every `closed` member of `a`'s closure carries a policy-admitted vouch
    enumerated in `basis a` — the asserted-species half. -/
theorem closed_carries_vouch_in_basis (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a m : Node Payload) (hmem : m ∈ depclosure a)
    (hclosed : classify gate tagOf closureOk P σ m = .closed) :
    ∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t tag, e = .vouch s t tag := by
  cases m with
  | ground i isSeed => simp [classify] at hclosed
  | derived i payload inputs =>
      have hest :=
        (declaration_alone_never_closes gate tagOf closureOk P σ i payload inputs hclosed).1
      have hunfold := hest
      simp only [established] at hunfold
      obtain ⟨_, hv⟩ := Bool.and_eq_true_iff.mp hunfold
      simp only [List.any_eq_true] at hv
      obtain ⟨e, heσ, hematch⟩ := hv
      cases e with
      | vouch s t tag =>
          refine ⟨.vouch s t tag, ?_, s, t, tag, rfl⟩
          simp only [basis, List.mem_filter]
          refine ⟨heσ, ?_⟩
          simp only [Bool.and_eq_true_iff] at hematch
          obtain ⟨⟨hsv, htv⟩, htagv⟩ := hematch
          simp only [hsv, Bool.true_and, List.any_eq_true]
          refine ⟨Node.derived i payload inputs, hmem, ?_⟩
          have hi : i = t := (of_decide_eq_true htv).symm
          simp only [Node.id, Bool.and_eq_true_iff]
          exact ⟨by simp [hi], htagv, hest⟩
      | corroboration s t => simp at hematch

/-- Packaged enumeration: under `Total a`, EVERY non-seed member of `a`'s
    closure carries both evidence species in `basis a` — `Total` forces each
    non-seed member `closed` (`total_iff_every_nonseed_closed`), from which
    both per-member halves above apply. This is the "nothing is silently
    trusted at the ceiling" display: the enumeration ranges over the whole
    closure, not just the root, and it needs `Total` nontrivially (an
    unclosed member has no counted evidence to enumerate). The root-only
    reading follows at `m := a` via `self_mem_depclosure`. -/
theorem total_carries_both_species (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) (hTotal : Total gate tagOf closureOk P σ a)
    (m : Node Payload) (hmem : m ∈ depclosure a) (hnotSeed : m.seed? = false) :
    (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t, e = .corroboration s t) ∧
      (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t tag, e = .vouch s t tag) := by
  have hclosed : classify gate tagOf closureOk P σ m = .closed :=
    (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal m hmem hnotSeed
  exact ⟨closed_carries_corroboration_in_basis gate tagOf closureOk P σ a m hmem hclosed,
        closed_carries_vouch_in_basis gate tagOf closureOk P σ a m hmem hclosed⟩

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

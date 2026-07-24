import Core
import Ceiling
import Transport

/-!
# Instance.Identity — the identity ceiling: a hash chain, genesis-bound

The generality witness: a cryptographic identity system whose record is a
hash chain of key events and whose genesis is a single binding commitment.
Instantiates `Ceiling`'s neutral verification ceiling at this domain and
exercises the verifiable case, T1 (determination-failure, via the gate) and
T3 (monotonicity, split-view / freshness); its companion
`Instance.SuretyLite` exercises the verifiable case, T1, and T2.

No Mathlib, no `Effective` — a TCB line the paper states: neither of the
generality witnesses needs a computability library.
-/

namespace Instance.Identity

open EonEalm
open Ceiling

/-! ## Domain plug-in (the §3-of-`Ceiling`-design contract) -/

variable (PrincipalId : Type) [DecidableEq PrincipalId]

/-- The chain's domain payload: a key event naming the principal it concerns
    and whether its own record is well-formed. Mirrors `Ceiling.Node`'s
    `Payload` slot at this domain — no other field is needed. -/
structure KeyEvent where
  principal : PrincipalId
  wellformed : Bool

variable {PrincipalId}

/-- Evidence reading (docstring, not code): a **corroboration** is an
    admitted party's re-verification of a chain link — a re-runnable check
    against the event's own committed content; a **vouch** is an
    introduction or attestation binding the event to the principal it
    names — keyed judgment, not re-runnable. `gate` is the mechanical half
    (record well-formedness); `established`'s vouch conjunct (`Ceiling.
    Classify`) is the testimony half. -/
def gate (ev : KeyEvent PrincipalId) : Bool := ev.wellformed

/-- The event's own named principal — the `Tag` every vouch for it must
    match. -/
def tagOf (ev : KeyEvent PrincipalId) : PrincipalId := ev.principal

/-- Identity has no domain-level closure-mode obligation beyond the neutral
    core's own (corroboration + recursive closure); the plug-in is the
    constant `true`. -/
def closureOk (_ : KeyEvent PrincipalId) : Bool := true

variable {Signer : Type}

/-! Instance-local abbreviations (§G: the architect's rejected-variable-
    promotion idiom) — collapsing the three fixed domain functions at every
    call site; `Signer`, the policy, the snapshot, and the node all thread
    normally. -/

abbrev classifyI (P : Policy Signer) (σ : Snapshot Signer PrincipalId)
    (m : Node (KeyEvent PrincipalId)) : Bucket :=
  Ceiling.classify gate tagOf closureOk P σ m

abbrev trustSurfaceI (P : Policy Signer) (σ : Snapshot Signer PrincipalId)
    (a : Node (KeyEvent PrincipalId)) : List (Node (KeyEvent PrincipalId)) :=
  Ceiling.trustSurface gate tagOf closureOk P σ a

abbrev basisI (P : Policy Signer) (σ : Snapshot Signer PrincipalId)
    (a : Node (KeyEvent PrincipalId)) : Snapshot Signer PrincipalId :=
  Ceiling.basis gate tagOf closureOk P σ a

abbrev TotalI (P : Policy Signer) (σ : Snapshot Signer PrincipalId)
    (a : Node (KeyEvent PrincipalId)) : Prop :=
  Ceiling.Total gate tagOf closureOk P σ a

/-! ## The binding claim (the axios `SuretyEonEalm` pattern, verbatim) -/

variable (BindsTo : Record → Context → Prop)

/-- The genesis binding claim as an `EonEalm.Claim` — no new structure, the
    direct identification the axios `SuretyEonEalm.genuineness` uses for
    genuineness,
    read here for binding: `w` is the committed chain bytes, `ξ` is the
    unrecorded key-custody/provenance context they were actually produced
    under. -/
def bindingClaim : Claim := fun w ξ => BindsTo w ξ

/-! `hfiber` — a **modeling hypothesis, never a theorem**: the fiber
witness that the same committed chain can arise under two distinct ambient
contexts with different binding verdicts (byte-identical chains under
honest custody vs. impersonation). Carried explicitly on every theorem
that needs it, per `Ceiling.Gate`'s own discipline — never proved here,
never a fresh axiom. -/

/-! ## Seeds -/

/-- The genesis binding event: the chain's own seed, flagged. -/
abbrev genesisSeed : Node (KeyEvent PrincipalId) := Node.ground 0 true

/-! ## The chain -/

/-- A chain of key events, newest-first: each event derives from (has as
    its sole build input) the chain of everything before it, bottoming out
    at the genesis seed. -/
def chain : List (Nat × KeyEvent PrincipalId) → Node (KeyEvent PrincipalId)
  | [] => genesisSeed
  | (i, ev) :: tl => .derived i ev [chain tl]

/-- The chain's own `derived` nodes, in order — the non-seed part of
    `depclosure (chain evs)` (`depclosure_chain` below). -/
def chainNodes : List (Nat × KeyEvent PrincipalId) → List (Node (KeyEvent PrincipalId))
  | [] => []
  | (i, ev) :: tl => .derived i ev [chain tl] :: chainNodes tl

omit [DecidableEq PrincipalId] in
/-- A `.derived` node with a single build input's dependency closure is
    that node itself, followed by the input's own closure — the
    `[p].attach.flatMap` collapse `Ceiling.depclosure`'s definition leaves
    implicit for a singleton `inputs` list. -/
private theorem depclosure_derived_singleton (i : Nat) (payload : KeyEvent PrincipalId)
    (p : Node (KeyEvent PrincipalId)) :
    depclosure (Node.derived i payload [p]) = Node.derived i payload [p] :: depclosure p := by
  rw [depclosure]
  simp

omit [DecidableEq PrincipalId] in
/-- **`depclosure_chain`**: the chain's dependency closure is exactly its
    own `derived` nodes, in order, followed by the single genesis seed —
    by induction on the event list, the singleton-input collapse above
    handling the one nontrivial step at each layer. -/
theorem depclosure_chain (evs : List (Nat × KeyEvent PrincipalId)) :
    depclosure (chain evs) = chainNodes evs ++ [genesisSeed] := by
  induction evs with
  | nil => simp [chain, chainNodes, depclosure, genesisSeed]
  | cons hd tl ih =>
      obtain ⟨i, ev⟩ := hd
      show depclosure (Node.derived i ev [chain tl]) = chainNodes ((i, ev) :: tl) ++ [genesisSeed]
      rw [depclosure_derived_singleton, ih]
      simp [chainNodes]

omit [DecidableEq PrincipalId] in
/-- Every `chainNodes` member is a `.derived` node — never a seed. Factored
    out of `principal_trust_bounded` so the induction on `evs` there doesn't
    generalize that theorem's own `P`/`σ`/`hTotal` hypotheses along with it. -/
private theorem chainNodes_not_seed (evs : List (Nat × KeyEvent PrincipalId))
    (m : Node (KeyEvent PrincipalId)) (hm : m ∈ chainNodes evs) : m.seed? = false := by
  induction evs with
  | nil => simp [chainNodes] at hm
  | cons hd tl ih =>
      obtain ⟨i, ev⟩ := hd
      simp only [chainNodes, List.mem_cons] at hm
      rcases hm with rfl | hm
      · rfl
      · exact ih hm

/-- **`principal_trust_bounded`** — the Cyphr display: under `Total (chain
    evs)`, the trust surface is exactly the genesis binding, nothing more.
    `Total` forces every non-seed closure member `closed`
    (`total_iff_every_nonseed_closed`); `depclosure_chain` splits the
    closure into `chainNodes evs` (all non-seed, all forced `closed`) and
    the seed (`seeds_are_imports` — never `closed`, always residual). The
    trust surface — the closure filtered to non-`closed` — is therefore
    exactly the singleton seed list. -/
theorem principal_trust_bounded (P : Policy Signer) (σ : Snapshot Signer PrincipalId)
    (evs : List (Nat × KeyEvent PrincipalId)) (hTotal : TotalI P σ (chain evs)) :
    trustSurfaceI P σ (chain evs) = [genesisSeed] := by
  have hnonseed := (total_iff_every_nonseed_closed gate tagOf closureOk P σ (chain evs)).mp hTotal
  show (depclosure (chain evs)).filter
      (fun m => !decide (Ceiling.classify gate tagOf closureOk P σ m = .closed)) = [genesisSeed]
  rw [depclosure_chain]
  rw [List.filter_append]
  have hchainNodes :
      (chainNodes evs).filter
        (fun m => !decide (Ceiling.classify gate tagOf closureOk P σ m = .closed)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm
    have hmem : m ∈ depclosure (chain evs) := by rw [depclosure_chain]; exact List.mem_append_left _ hm
    have hnotseed : m.seed? = false := chainNodes_not_seed evs m hm
    have := hnonseed m hmem hnotseed
    simp [this]
  have hseed : ([genesisSeed] : List (Node (KeyEvent PrincipalId))).filter
      (fun m => !decide (Ceiling.classify gate tagOf closureOk P σ m = .closed)) = [genesisSeed] := by
    have : Ceiling.classify gate tagOf closureOk P σ genesisSeed = .import :=
      seeds_are_imports gate tagOf closureOk P σ genesisSeed rfl
    simp [this]
  rw [hchainNodes, hseed]
  rfl

/-- **`identity_ceiling`** — the paper's "identity is at the ceiling"
    corollary: one application of `Ceiling.ceiling` at this domain, under
    the domain's own `hfiber`. The second conjunct is L2
    (`Ceiling.seeds_undischargeable_and_residual`): for every scheme
    `S : Scheme Γ (bindingClaim BindsTo)`, the genesis seed is both
    undischargeable by `S` and resident in the trust surface regardless. -/
theorem identity_ceiling {Comm : Type} (Γ : Commitment Comm)
    (BindsTo : Record → Context → Prop) (hfiber : ¬ Determined (bindingClaim BindsTo))
    (P : Policy Signer) (σ : Snapshot Signer PrincipalId) (a : Node (KeyEvent PrincipalId)) :
    (¬ ∃ S : Scheme Γ (bindingClaim BindsTo), SnapshotSound S) ∧
    (∀ S : Scheme Γ (bindingClaim BindsTo), ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Ceiling.Discharges Γ (bindingClaim BindsTo) S m ∧ m ∈ trustSurfaceI P σ a) ∧
    (TotalI P σ a → trustSurfaceI P σ a = (depclosure a).filter (fun m => m.seed?)) ∧
    (TotalI P σ a → ∀ m ∈ depclosure a, m.seed? = false →
      (∃ e ∈ basisI P σ a, ∃ s t, e = .corroboration s t) ∧
      (∃ e ∈ basisI P σ a, ∃ s t tag, e = .vouch s t tag)) :=
  Ceiling.ceiling Γ (bindingClaim BindsTo) hfiber gate tagOf closureOk P σ a

/-! ## The four non-vacuity witnesses (concrete `Unit` types) -/

section Nonvacuity

/-- The single concrete event every witness below reuses. -/
def w0 : KeyEvent Unit := ⟨(), true⟩

/-- The policy admitting the one signer as both corroborator and voucher. -/
def policyAll : Policy Unit := ⟨fun _ => true, fun _ => true⟩

/-- A snapshot carrying one admitted vouch and one admitted corroboration,
    both targeting node id `i`. -/
def snapClosing (i : Nat) : Snapshot Unit Unit :=
  [.vouch () i (), .corroboration () i]

/-- **W1** — a closed node: `σ` supplies one admitted vouch and one admitted
    corroboration targeting it. -/
theorem w1_closed_event :
    classifyI policyAll (snapClosing 1) (Node.derived 1 w0 []) = .closed := by
  simp [classifyI, Ceiling.classify, established, corroborated, gate, tagOf, closureOk,
    policyAll, snapClosing, Node.id, w0]

/-- **W2** — base-bounded `Total`: a one-link chain, closed by `snapClosing`,
    with `principal_trust_bounded` firing concretely. -/
theorem w2_base_bounded_total :
    TotalI policyAll (snapClosing 1) (chain [(1, w0)]) := by
  apply (total_iff_every_nonseed_closed gate tagOf closureOk policyAll (snapClosing 1)
    (chain [(1, w0)])).mpr
  intro m hmem hnotseed
  have hlist : depclosure (chain [(1, w0)]) = [Node.derived 1 w0 [genesisSeed], genesisSeed] := by
    rw [depclosure_chain]; rfl
  rw [hlist] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · simp [Ceiling.classify, established, corroborated, gate, tagOf, closureOk,
      policyAll, snapClosing, Node.id, w0, genesisSeed, Node.seed?]
  · simp [Node.seed?] at hnotseed

theorem w2_trust_surface_bounded :
    trustSurfaceI policyAll (snapClosing 1) (chain [(1, w0)]) = [genesisSeed] :=
  principal_trust_bounded policyAll (snapClosing 1) [(1, w0)] w2_base_bounded_total

/-- **W3** — defeated `Total`: the same chain, an empty snapshot —
    `establishGap` — defeats `Total` via `unclosed_member_defeats_total`. -/
theorem w3_defeated_total : ¬ TotalI policyAll ([] : Snapshot Unit Unit) (chain [(1, w0)]) := by
  apply unclosed_member_defeats_total gate tagOf closureOk policyAll ([] : Snapshot Unit Unit)
    (chain [(1, w0)]) (Node.derived 1 w0 [chain []])
  · rw [depclosure_chain]; simp [chainNodes]
  · rfl
  · simp [Ceiling.classify, established, gate, tagOf]

/-- **W4** — `no_vouchers_no_total`, instantiated: a policy admitting no
    vouchers forbids every non-seed `Total`. -/
theorem w4_no_vouchers_no_total :
    ¬ TotalI (PrincipalId := Unit) ⟨fun _ => true, fun _ => false⟩
      ([] : Snapshot Unit Unit) (Node.derived 1 w0 []) :=
  no_vouchers_no_total gate tagOf closureOk ⟨fun _ => true, fun _ => false⟩
    ([] : Snapshot Unit Unit) (fun _ => rfl) (Node.derived 1 w0 []) rfl

end Nonvacuity

/-! ## The split-view exhibit (M8)

Stated over `Trichotomy.Transport.RecordOf E` at `E := Bool` (design fact 1:
divergence between two views needs a genuinely two-element alphabet — over
the abstract `EonEalm.Entry` it is unprovable, since a unary alphabet is
totally ordered by prefix). -/

section SplitView

open Trichotomy.Transport (RecordOf ExtOf)

variable {E : Type}

/-- Two views are consistent iff one extends the other — `Transport.ExtOf`,
    the meta-record analogue of a Merkle consistency proof. -/
def viewsConsistent (w₁ w₂ : RecordOf E) : Prop := ExtOf w₁ w₂ ∨ ExtOf w₂ w₁

/-- Shared step for `divergence_permanent`'s two symmetric halves: given
    `w' ++ u' = (w ++ u) ++ u''` for some `u''` (i.e. `(w ++ u) ⊑ (w' ++ u')`
    after re-associating), `w` and `w'` are themselves consistent — whichever
    is the (weakly) shorter is a prefix of the other, via take-of-append-left
    (`List.take_left`) once the shorter side's take ignores the longer
    side's tail (`List.take_append_of_le_length`). -/
private theorem consistent_of_ext_append {w w' : RecordOf E} {u u' u'' : List E}
    (hu : w' ++ u' = (w ++ u) ++ u'') : viewsConsistent w w' := by
  rw [List.append_assoc] at hu
  by_cases hle : w.length ≤ w'.length
  · left
    have h1 : w'.take w.length = w := by
      rw [← List.take_append_of_le_length hle, hu, List.take_left]
    refine ⟨w'.drop w.length, ?_⟩
    calc w' = w'.take w.length ++ w'.drop w.length := (List.take_append_drop _ _).symm
      _ = w ++ w'.drop w.length := by rw [h1]
  · right
    have hle' : w'.length ≤ w.length := Nat.le_of_not_le hle
    have h1 : w.take w'.length = w' := by
      rw [← List.take_append_of_le_length hle', ← hu, List.take_left]
    refine ⟨w.drop w'.length, ?_⟩
    calc w = w.take w'.length ++ w.drop w'.length := (List.take_append_drop _ _).symm
      _ = w' ++ w.drop w'.length := by rw [h1]

/-- **`divergence_permanent`**: once two views disagree, no further
    extension of either can reconcile them — equivocation, once real, is
    permanent. -/
theorem divergence_permanent {w₁ w₂ : RecordOf E} (hdiv : ¬ viewsConsistent w₁ w₂) :
    ∀ u₁ u₂ : List E, ¬ viewsConsistent (w₁ ++ u₁) (w₂ ++ u₂) := by
  intro u₁ u₂ hcons
  apply hdiv
  rcases hcons with ⟨u, hu⟩ | ⟨u, hu⟩
  · exact consistent_of_ext_append hu
  · exact (consistent_of_ext_append hu).symm

/-- **`consistency_flips`** — the non-monotonicity witness: the empty views
    are (trivially) consistent, but extending them by one entry each —
    `[true]` vs. `[false]` — is not; they diverge at index 0. Over `E :=
    Bool`, the two-element alphabet `divergence_permanent` needs. -/
theorem consistency_flips :
    viewsConsistent ([] : RecordOf Bool) [] ∧
      ¬ viewsConsistent (([] : RecordOf Bool) ++ [true]) ([] ++ [false]) := by
  refine ⟨Or.inl ⟨[], rfl⟩, ?_⟩
  rintro (⟨u, hu⟩ | ⟨u, hu⟩) <;> simp at hu

end SplitView

/-! This is the T3 cell at the meta-record level: equivocation, once real,
is *permanent* (`divergence_permanent`), hence affirmable — its evidence
endures — while honesty is only ever refutative, never provable forever.
The minimal cure is a witness quorum or gossip protocol (cosigned
checkpoints), or restriction to "consistent as of time `t`." The eml
transparency log's own bridge (Cyphrme/Cyphr
`docs/models/lean-eml-bridge/EonEalmEml.lean`) instantiates this same
EON/EALM machinery for a concrete k-ary Merkle log — cited here as the
deployment realization of the record this split-view exhibit is stated
over, not imported. -/

end Instance.Identity

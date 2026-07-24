import Ceiling.Node
import Ceiling.Evidence

/-!
# Ceiling — Classify: establishment and the four-bucket cascade

The neutral core fixes the SHAPE of establishment and closure; the domain
supplies only payload-level predicates (`gate`, `tagOf`, `closureOk`).
Establishment is `gate ∧ admitted-vouch`; closure additionally demands
`closureOk ∧ corroborated ∧ recursive closure`. This is not domain
parochialism promoted to a core — it is the derived/asserted evidence
partition (`Ceiling.Evidence`) made structural: every `closed` verdict rests
on at least one **derived** item (a corroboration) and at least one
**asserted** item (a vouch), the two mandatory species of the determination
split showing up in the accounting. (Monotonicity is not a third evidence
species here — it enters elsewhere, as σ-relativity: retraction-as-omission
and re-evaluation.)

Recursive closure: every build input is either a seed or itself classifies
`closed` — acyclicity by the shape of `Node` (`Ceiling.Node`'s module
docstring), so the circular-justification differential is inexpressible
here, not merely excluded.
-/

namespace Ceiling

variable {Payload Tag Signer : Type} [DecidableEq Tag]

/-- The four classification buckets: `import` (no build record — clause 1),
    `establishGap` (not established — clause 2), `attestGap` (established but
    the closure-mode conjunction fails — clause 3), `closed` (all conditions
    hold). -/
inductive Bucket where
  | closed | attestGap | establishGap | import
  deriving DecidableEq, Repr

/-- Condition (ii)'s empirical half: at least one policy-admitted
    corroboration targets `m`. -/
def corroborated (P : Policy Signer) (σ : Snapshot Signer Tag)
    (m : Node Payload) : Bool :=
  σ.any fun e => match e with
    | .corroboration s t => P.admittedCorroborator s && decide (t = m.id)
    | .vouch .. => false

/-- `established (id, payload)`: the domain's mechanical `gate` passes over
    `payload`, and an admitted vouch for exactly `(id, tagOf payload)` exists
    in `σ`. The two conjuncts are the gate half (mechanical, over the node's
    own committed content) and the testimony half (asserted, keyed judgment)
    — establishment is never carried by either alone. -/
def established (gate : Payload → Bool) (tagOf : Payload → Tag)
    (P : Policy Signer) (σ : Snapshot Signer Tag)
    (id : Nat) (payload : Payload) : Bool :=
  gate payload &&
    σ.any fun e => match e with
      | .vouch s t tag => P.admittedVoucher s && decide (t = id) && decide (tag = tagOf payload)
      | .corroboration .. => false

/-- **`classify`**: total by construction — every case of `Node` is matched,
    and the `if`/`else` cascade always yields exactly one `Bucket`. `.ground`
    is precedence clause 1 (`import`, uniformly — no build record, seed or
    not). `.derived` always has a payload, so clause 1 never fires there:
    not established ⟹ `establishGap` (clause 2); established but any of
    (`closureOk`, `corroborated`, recursive closure) fails ⟹ `attestGap`
    (clause 3); all hold ⟹ `closed`. -/
def classify (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) :
    Node Payload → Bucket
  | .ground _ _ => .import
  | m@(.derived i payload inputs) =>
      let est := established gate tagOf P σ i payload
      let corr := corroborated P σ m
      let recClosed := inputs.attach.all fun p =>
        p.1.seed? || decide (classify gate tagOf closureOk P σ p.1 = .closed)
      if !est then .establishGap
      else if closureOk payload && corr && recClosed then .closed
      else .attestGap
termination_by m => sizeOf m
decreasing_by
  all_goals
    simp_wf
    have := List.sizeOf_lt_of_mem p.2
    omega

-- ===========================================================================
-- Cascade lemmas
-- ===========================================================================

/-- `classify_exhaustive` — every closure member lands in exactly one of the
    four buckets (match totality; a cheap lemma, useful for the paper
    display). -/
theorem classify_exhaustive (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (m : Node Payload) :
    classify gate tagOf closureOk P σ m = .import ∨
    classify gate tagOf closureOk P σ m = .establishGap ∨
    classify gate tagOf closureOk P σ m = .attestGap ∨
    classify gate tagOf closureOk P σ m = .closed := by
  cases h : classify gate tagOf closureOk P σ m with
  | «import» => exact Or.inl rfl
  | establishGap => exact Or.inr (Or.inl rfl)
  | attestGap => exact Or.inr (Or.inr (Or.inl rfl))
  | closed => exact Or.inr (Or.inr (Or.inr rfl))

/-- A `ground` node is forced into `import`, unconditionally. -/
theorem ground_forced_import (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (i : Nat) (isSeed : Bool) :
    classify gate tagOf closureOk P σ (Node.ground i isSeed) = .import := by
  simp [classify]

/-- Genesis seeds classify `import` — the permanent, named trust-import. -/
theorem seeds_are_imports (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (m : Node Payload) (hseed : m.seed? = true) :
    classify gate tagOf closureOk P σ m = .import := by
  cases m with
  | ground i isSeed => simp [classify]
  | derived i payload inputs => simp [Node.seed?] at hseed

/-- `closed` is never reached by testimony alone (or record alone): a
    `closed` node carries both species, pinned to its OWN fields — its own
    `(id, payload)` establishment (so the counted vouch's tag matches THIS
    node's payload, which is what `basis` membership needs) and an actual
    corroboration targeting it. `classify`'s cascade only ever calls
    `established` with the node's own fields, so no unrelated witness can
    stand in. Stated on the `derived` constructor: `ground` nodes never
    classify `closed` at all (`ground_forced_import`). -/
theorem declaration_alone_never_closes (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (i : Nat) (payload : Payload) (inputs : List (Node Payload))
    (hclosed : classify gate tagOf closureOk P σ (Node.derived i payload inputs) = .closed) :
    established gate tagOf P σ i payload = true ∧
      corroborated P σ (Node.derived i payload inputs) = true := by
  simp only [classify] at hclosed
  by_cases hest : established gate tagOf P σ i payload = true
  · simp only [hest, Bool.not_true, if_neg (by simp : ¬ ((false : Bool) = true))] at hclosed
    refine ⟨hest, ?_⟩
    by_cases hcascade :
        (closureOk payload && corroborated P σ (Node.derived i payload inputs) &&
          inputs.attach.all fun p => p.1.seed? ||
            decide (classify gate tagOf closureOk P σ p.1 = .closed)) = true
    · simp only [Bool.and_eq_true_iff] at hcascade
      exact hcascade.1.2
    · simp [hcascade] at hclosed
  · simp only [Bool.not_eq_true] at hest
    simp [hest] at hclosed

/-- An unestablished `derived` node is never `closed` — the direct,
    laundering-vocabulary-free statement of clause 2's force: no silent
    self-declaration without a policy-admitted vouch reaches `closed`. -/
theorem unestablished_never_closed (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (i : Nat) (payload : Payload) (inputs : List (Node Payload))
    (hnp : established gate tagOf P σ i payload = false) :
    classify gate tagOf closureOk P σ (Node.derived i payload inputs) ≠ .closed := by
  simp [classify, hnp]

end Ceiling

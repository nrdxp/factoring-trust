/-!
# Ceiling — Node: the neutral closure-member shape

A closure member is either `ground` (no domain payload — a raw admitted
input, a genesis seed when `isSeed = true`, or any other build-recordless
member) or `derived` (a domain payload plus a list of build inputs). Mirrors
the axios `docs/models/lean-surety/SuretyCeiling/Basic.lean`'s `Artifact`
shape, with
the domain-specific fields (class, mode, gates, …) collapsed into one
abstract `Payload` — the domain supplies its own predicates over `Payload`
in `Ceiling.Classify`, rather than this file baking in any particular
domain's field list.

Acyclicity is by construction, not by axiom: `inputs : List (Node Payload)`
inside `.derived` makes every build input a strictly smaller subterm, so no
node can (transitively) name itself as its own input. This file therefore
cannot express — let alone need to exclude — a circular-justification fixed
point; that is a stronger property than a bounded model-checked absence, but
a different claim, not a re-derivation of one.
-/

namespace Ceiling

variable (Payload : Type)

/-- A closure member: `ground` (no build record — carries only its identity
    tag and whether it is a genesis seed) or `derived` (a domain payload over
    a list of build inputs). -/
inductive Node where
  | ground (id : Nat) (isSeed : Bool)
  | derived (id : Nat) (payload : Payload) (inputs : List Node)

variable {Payload}

/-- The bare identity tag every `Node` carries — `Evidence` targets an `id`,
    not a full `Node` value, mirroring the reference's identity-not-structure
    comparison. -/
def Node.id : Node Payload → Nat
  | .ground i _ => i
  | .derived i _ _ => i

/-- A genesis seed is a `ground` node flagged as such; every `derived` node is
    never a seed. -/
def Node.seed? : Node Payload → Bool
  | .ground _ s => s
  | .derived .. => false

/-- The dependency closure of `m`: reflexive — `m` is always its own head —
    and the transitive image of `.derived`'s `inputs`. Well-founded by
    construction: each `p` drawn from `inputs.attach` is a strictly smaller
    subterm of `m`, discharged by `List.sizeOf_lt_of_mem`. No fuel, no axiom. -/
def depclosure : Node Payload → List (Node Payload)
  | .ground i s => [.ground i s]
  | .derived i p inputs =>
      .derived i p inputs :: inputs.attach.flatMap (fun q => depclosure q.1)
termination_by m => sizeOf m
decreasing_by
  all_goals
    simp_wf
    have := List.sizeOf_lt_of_mem q.2
    omega

theorem self_mem_depclosure (m : Node Payload) : m ∈ depclosure m := by
  cases m <;> simp [depclosure]

end Ceiling

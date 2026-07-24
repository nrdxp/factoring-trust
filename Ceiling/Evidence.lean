/-!
# Ceiling — Evidence: the derived/asserted evidence split

`Evidence` mirrors the axios `docs/models/lean-surety/SuretyCeiling/Basic.lean`'s
derived/asserted split (atom-model §4): a **corroboration** is a re-runnable
record — closing what is certifiable from the record itself — and a
**vouch** is pure keyed judgment naming a target and a tag — closing what is
not record-determined and hence closable by testimony only. `Snapshot` is
the evidence set at evaluation time; retraction is modeled as omission, not a
separate predicate. `Policy` is the consumer's admission rule: which signers
count as corroborators, and which as voucher — a relativity the classifier
itself never resolves.
-/

namespace Ceiling

/-- Evidence over the closure: a **corroboration** (derived species — a
    re-runnable record naming its `target`) or a **vouch** (asserted species
    — keyed judgment naming its `target` and the `tag` it vouches for). -/
inductive Evidence (Signer Tag : Type) where
  | corroboration (signer : Signer) (target : Nat) : Evidence Signer Tag
  | vouch (signer : Signer) (target : Nat) (tag : Tag) : Evidence Signer Tag
  deriving DecidableEq

/-- The evidence snapshot `σ`: the finite set of signed records that exist at
    evaluation time. Retraction is modeled as omission. -/
abbrev Snapshot (Signer Tag : Type) := List (Evidence Signer Tag)

/-- The consumer's admission policy: which signers count as admitted
    corroborators, and which as admitted vouchers. `Bool`-valued so
    `classify` stays computable and total by construction. -/
structure Policy (Signer : Type) where
  admittedCorroborator : Signer → Bool
  admittedVoucher      : Signer → Bool

end Ceiling

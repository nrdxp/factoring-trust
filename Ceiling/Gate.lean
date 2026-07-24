import Core
import Ceiling.Accounting

/-!
# Ceiling — Gate: the binding-admits-no-scheme instance pattern, and `ceiling`

The one place `Ceiling` imports `Core`: the determination gate
(`EonEalm.snapshot_characterization_determined`, restated in `Ceiling`'s own
vocabulary for instance authors) applied to a domain's own binding claim.

`hfiber` is a **modeling hypothesis, never a theorem**: it is the domain's
fiber witness (the fact that the same committed record can arise under two
distinct ambient contexts with different binding verdicts), taken as an
explicit argument to every theorem below — never proved here (proving it
would mean fixing a concrete claim and a concrete pair of contexts, exactly
what each instance is responsible for asserting) and never smuggled in as a
fresh axiom.

`Ceiling.Junction` builds on the gate here to prove the actual junction
between the accounting world (`Node`) and the scheme world
(`EonEalm.Record`/`Claim`/`Scheme`) — `Discharges` and the `ceiling` display
that supersedes the old three-fact bundle this module used to hold.
-/

namespace Ceiling

open EonEalm

/-- **The binding-admits-no-scheme gate**, stated once generically for any
    domain binding claim `φ_bind`: if `φ_bind` is not record-determined
    (`hfiber`), it admits no snapshot-sound evidence scheme over any
    commitment `Γ`. `Ceiling`'s own name for `EonEalm.determination_gate`
    (itself `snapshot_characterization_determined`'s contrapositive) — kept
    so instance authors never need to reach past this package into `Core`'s
    own vocabulary. -/
theorem binding_admits_no_scheme (φ_bind : Claim) (hfiber : ¬ Determined φ_bind)
    {Comm : Type} (Γ : Commitment Comm) :
    ¬ ∃ S : Scheme Γ φ_bind, SnapshotSound S :=
  determination_gate hfiber

end Ceiling

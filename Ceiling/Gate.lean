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

`ceiling` is the paper's companion display: a **bundle** of three mechanized
facts plus an interpretive reading ("the residue cannot be smaller than the
named base, and no evidence scheme substitutes for the admission"), not one
new deep theorem. No formal junction between the accounting world (`Node`)
and the scheme world (`EonEalm.Record`/`Claim`) is built here — the link
stays interpretive; building it is real modeling work with no display value
at this stage, left as future work.
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

variable {Payload Tag Signer : Type} [DecidableEq Tag]

/-- **`ceiling`** — the packaged minimality display, under a domain's
    `hfiber`: no evidence scheme substitutes for the admission (the gate);
    every seed in `a`'s closure is irreducibly part of its trust surface
    (`seeds_always_residual`); and under `Total a`, EVERY non-seed member of
    the closure carries both evidence species in the assumption basis
    (`total_carries_both_species`). Read together: the trust residue cannot
    be smaller than the named seed base, and at the ceiling nothing is
    silently trusted — every grain of admitted evidence the verdict rests
    on, for every member, is enumerated. -/
theorem ceiling {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) (a : Node Payload) :
    (¬ ∃ S : Scheme Γ φ_bind, SnapshotSound S) ∧
    (∀ m ∈ depclosure a, m.seed? = true → m ∈ trustSurface gate tagOf closureOk P σ a) ∧
    (Total gate tagOf closureOk P σ a →
      ∀ m ∈ depclosure a, m.seed? = false →
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t, e = .corroboration s t) ∧
        (∃ e ∈ basis gate tagOf closureOk P σ a, ∃ s t tag, e = .vouch s t tag)) :=
  ⟨binding_admits_no_scheme φ_bind hfiber Γ,
   fun m hmem hseed => seeds_always_residual gate tagOf closureOk P σ a m hmem hseed,
   fun hTotal m hmem hnotSeed =>
     total_carries_both_species gate tagOf closureOk P σ a hTotal m hmem hnotSeed⟩

end Ceiling

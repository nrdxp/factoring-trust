import Ceiling.Node
import Ceiling.Evidence
import Ceiling.Classify
import Ceiling.Accounting
import Ceiling.Gate

/-!
# Ceiling — the neutral verification ceiling

The general (domain-neutral) companion to the trichotomy: the trust residue
is minimal and bounded. No Mathlib dependency anywhere in this package;
`Ceiling.Gate` is the only module that imports `Core`.

## The one principled decision

The neutral core fixes the SHAPE of establishment and closure; the domain
supplies only payload-level predicates. Establishment is
`gate ∧ admitted-vouch`; closure additionally demands
`admitted-corroboration ∧ domain-closure ∧ recursive closure`. This is NOT
domain parochialism promoted to a core — it is the derived/asserted evidence
partition (the atom-model's evidence split) made structural: every `closed`
verdict rests on at least one **derived** item (a corroboration — a
re-runnable record, closing what is certifiable from the record) and at
least one **asserted** item (a vouch — keyed judgment, closing what is not
record-determined and hence, by the gate, closable by testimony only). The
two mandatory species are the determination split showing up in the
accounting. Monotonicity is *not* promoted to a third evidence species here
— it enters as σ-relativity (retraction-as-omission and re-evaluation), not
as a species of evidence.

The rejected alternative: a fully-parametric admission rule under which the
domain returns whatever evidence set it counts. More general, but every
accounting theorem then carries lawfulness side-conditions for no motivating
third instance — two instances, one fixed shape.

## Module map

* `Ceiling.Node` — `Node`, `depclosure`, seeds.
* `Ceiling.Evidence` — `Evidence`, `Snapshot`, `Policy`.
* `Ceiling.Classify` — `established`, `corroborated`, `classify`, and the
  cascade lemmas.
* `Ceiling.Accounting` — `trustSurface`, `basis`, `Total`, and the
  completeness/non-vacuity theorems.
* `Ceiling.Gate` — `binding_admits_no_scheme` and the `ceiling` bundle
  (imports `Core`).

## The instance interface

Each instance over this one neutral core supplies: concrete `Payload`, `Tag`,
`Signer` types (with `[DecidableEq Tag]`); the three payload predicates
`gate`, `tagOf`, `closureOk`; its own binding claim `φ_bind : EonEalm.Claim`
with its `hfiber : ¬ EonEalm.Determined φ_bind` hypothesis (explicit,
never proved, never a fresh axiom); a seed inventory; and the four
non-vacuity witnesses (a closed node; a `Total` closure through a seed; a
defeated `Total`; and, when the instance's policy admits no vouchers,
`no_vouchers_no_total`'s witness). The parametrization itself — the section
variables threaded through `Ceiling.Classify`/`Ceiling.Accounting`/
`Ceiling.Gate` — IS the plug-in point; an instance is a module that opens
these definitions at concrete types rather than a separate bundling
structure. `Ceiling.Instance.Identity` and `Ceiling.Instance.SuretyLite` are
out of this package's scope.

The light surety witness's scope guard is structural, not a discipline to
police: this workspace's `lakefile.toml` requires only `mathlib`, so nothing
under `Instance/` can reach the axios `docs/models/lean-surety/` package's
gate/generator/RCAS machinery at all — an instance that tried to import it
would fail to build, not merely fail review.
-/

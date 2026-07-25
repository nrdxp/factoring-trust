import Effective.Trichotomy
import Effective.Cells
import Effective.NonCertifiable

/-!
# Effective — the computable stratum

The one Mathlib-dependent package: `Effective.Trichotomy` mirrors `Core`'s snapshot
and endurance characterizations at Turing-computability, using
`Mathlib.Computability.Halting`'s `Computable`/`ComputablePred`/`Primcodable`
vocabulary in place of Lean-internal `Decidable`. `Effective.Cells` annotates the
cell table's (`Witness.Cells`) fibered rows with `ComputablePred` witnesses, and
`Effective.NonCertifiable` inhabits the two certifiability-failure rows with
`Claim`-typed witnesses whose non-certifiability is proved from the halting problem.
-/

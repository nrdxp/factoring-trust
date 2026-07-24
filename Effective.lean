import Effective.Trichotomy
import Effective.Cells

/-!
# Effective — the computable stratum

The one Mathlib-dependent package: `Effective.Trichotomy` mirrors `Core`'s snapshot
and endurance characterizations at Turing-computability, using
`Mathlib.Computability.Halting`'s `Computable`/`ComputablePred`/`Primcodable`
vocabulary in place of Lean-internal `Decidable`. `Effective.Cells` annotates the
cell table's (`Witness.Cells`) fibered rows with `ComputablePred` witnesses.
-/

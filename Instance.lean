import Instance.Identity
import Instance.SuretyLite

/-!
# Instance — the two generality witnesses over the neutral ceiling

Mathlib-free (imports `Core`/`Ceiling`/`Transport` only, transitively — a
TCB line the paper states): `Instance.Identity` and `Instance.SuretyLite`
instantiate `Ceiling`'s domain-neutral verification ceiling over two
genuinely disjoint domains, chosen to exercise complementary cells of the
trichotomy rather than the same one twice. Identity inhabits T1+T3
(binding; freshness/split-view); surety-lite inhabits T1+T2 (genuineness;
degeneracy) — jointly, every axis has a witness in *some* instance, with
`Witness.Cells`' cell table as the map.

## Module map

* `Instance.Identity` — the hash-chain identity instance: `KeyEvent`, the
  chain and its dependency-closure/trust-bound theorems, the identity
  ceiling, and the split-view (equivocation) exhibit.
* `Instance.SuretyLite` — the light source-establishment instance: the
  three-field `LitePayload` guard and the surety ceiling.
-/

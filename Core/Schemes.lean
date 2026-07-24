import Core.Axes
import Core.Commitment

/-!
# Schemes — the verification scheme and its soundness flavors

A scheme `(C, V)` for a claim `φ`, with completeness (E1) stated as **certificate
existence**, never a bundled efficient prover: `∀ (w, ξ) ⊨ φ, ∃ c, |c| ≤ poly(|w|) ∧
V(C(w), c) = 1`. Bundling a poly-time prover as scheme data would, composed with
poly-time `C`/`V`, itself be a poly-time decider for `φ̂` — since the snapshot
characterization below is claimed for every determined oracle-certifiable `φ̂`, "a
scheme exists" would force `φ̂ ∈ P` for arbitrary NP `φ̂`, an unconditional `P = NP`
obligation. Stating completeness as bare witness-existence avoids this; the oracle
stratum's forced-NP direction (`snapshot_characterization_np`) survives unconditionally
from `V` poly-time and `|c|` bounded alone, never from a poly prover.

Offline (self-containedness) is not a separate hypothesis to discharge: `Scheme.V`'s
type, `Comm → Proof → Prop`, already excludes record access, oracle access,
interaction, a clock, and `ξ` — the signature *is* the offline constraint. Poly-time
bounds (`V` poly-time, `|c| ≤ poly(|w|)`) are an effective-stratum concern this
Mathlib-free package does not encode.
-/

namespace EonEalm

/-- Idealized ("`ψ ∈ NP`"): existence of a witness type and a checker whose ∃-closure
    is `ψ`. Poly-time boundedness is not modeled (see the module doc-comment); this
    captures the *shape* the oracle stratum contributes, not the complexity bound. -/
def NPMembership (ψ : Record → Prop) : Prop :=
  ∃ (Witness : Type) (Chk : Record → Witness → Prop), ∀ w, ψ w ↔ ∃ t, Chk w t

/-- A scheme `(V)` for `φ` over commitment `Γ`, with completeness in ∃-certificate
    form — no bundled prover. -/
structure Scheme {Comm : Type} (Γ : Commitment Comm) (φ : Claim) where
  /-- The certificate type. -/
  Proof : Type
  /-- The verifier. -/
  V : Comm → Proof → Prop
  /-- Completeness, ∃-certificate form: an accepting certificate exists for every
      `(w, ξ) ⊨ φ`; no efficient prover is asserted. -/
  completeness : ∀ w ξ, φ w ξ → ∃ c, V (Γ.C w) c

/-- Snapshot soundness (context-independence): acceptance forces `φ` at every
    context, for the record it names. -/
def SnapshotSound {Comm : Type} {Γ : Commitment Comm} {φ : Claim} (S : Scheme Γ φ) : Prop :=
  ∀ w c, S.V (Γ.C w) c → ∀ ξ, φ w ξ

/-- Enduring soundness (temporal): acceptance forces `φ` at every extension and
    every context. -/
def EnduringSound {Comm : Type} {Γ : Commitment Comm} {φ : Claim} (S : Scheme Γ φ) : Prop :=
  ∀ w c, S.V (Γ.C w) c → ∀ w' ξ, w ⊑ w' → φ w' ξ

/-- Enduring soundness implies snapshot soundness via `w′ := w`. -/
theorem enduringSound_snapshotSound {Comm : Type} {Γ : Commitment Comm} {φ : Claim}
    {S : Scheme Γ φ} (h : EnduringSound S) : SnapshotSound S :=
  fun w c hacc ξ => h w c hacc w ξ (ext_refl w)

end EonEalm

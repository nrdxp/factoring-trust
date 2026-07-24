import Ceiling

/-!
# Instance.SuretyLite — the surety ceiling, a deliberately light second witness

The complementary generality witness to `Instance.Identity`: an abstract,
vouch-shaped source-establishment predicate, exercising the verifiable case
and T1 (determination-failure, via the gate) alongside T2
(certifiability-failure), the complement of identity's T1+T3.

`SuretyLite`'s "proper name," wherever the general verification ceiling is
instantiated to the build domain, is the **surety ceiling** — this instance
is deliberately light: zero frontier machinery, no format/parse gates, no
corroboration quorum, no forced-generator or Rice/Rice–Shapiro tightness
result. The full empirical treatment is a follow-up paper, over the axios
corpus (`docs/models/lean-surety/`, its companion Alloy models, and the
full RCAS five-condition model): cited, never reproduced here.

**HARD GUARD (maintainer's WS-3 rider):** `LitePayload`'s field list is
exactly `{declaredClass, gateOk, closureModeOk}`. Growing it, or naming a
definition after format/parse/reproducibility/RCAS/generator vocabulary,
is the follow-up paper leaking in. The lakefile already blocks the import
channel (this workspace requires only `mathlib`); this guard is about
restatement, not import.
-/

namespace Instance.SuretyLite

open EonEalm
open Ceiling

variable (ClassName : Type) [DecidableEq ClassName]

/-- The surety-lite payload — one `Tag` field plus two opaque gate-shaped
    `Bool`s, and that is the whole mechanical content. `gateOk`/
    `closureModeOk` are left uninterpreted: the follow-up paper is where
    they get a concrete format/parse/reproducibility reading. -/
structure LitePayload where
  declaredClass : ClassName
  gateOk : Bool
  closureModeOk : Bool

variable {ClassName}

def gate (p : LitePayload ClassName) : Bool := p.gateOk

def tagOf (p : LitePayload ClassName) : ClassName := p.declaredClass

def closureOk (p : LitePayload ClassName) : Bool := p.closureModeOk

variable {Signer : Type}

/-! Instance-local abbreviations, the same idiom `Instance.Identity` uses. -/

abbrev classifyI (P : Policy Signer) (σ : Snapshot Signer ClassName)
    (m : Node (LitePayload ClassName)) : Bucket :=
  Ceiling.classify gate tagOf closureOk P σ m

abbrev trustSurfaceI (P : Policy Signer) (σ : Snapshot Signer ClassName)
    (a : Node (LitePayload ClassName)) : List (Node (LitePayload ClassName)) :=
  Ceiling.trustSurface gate tagOf closureOk P σ a

abbrev basisI (P : Policy Signer) (σ : Snapshot Signer ClassName)
    (a : Node (LitePayload ClassName)) : Snapshot Signer ClassName :=
  Ceiling.basis gate tagOf closureOk P σ a

abbrev TotalI (P : Policy Signer) (σ : Snapshot Signer ClassName)
    (a : Node (LitePayload ClassName)) : Prop :=
  Ceiling.Total gate tagOf closureOk P σ a

/-! ## The binding claim (the axios `SuretyEonEalm` pattern, verbatim) -/

variable (Genuine : Record → Context → Prop)

/-- Genuineness as an `EonEalm.Claim` — the direct identification the axios
    `SuretyEonEalm.genuineness` states: `w` is the committed source bytes,
    `ξ` is the unrecorded authorship/provenance context they were actually
    produced under. -/
def bindingClaim : Claim := fun w ξ => Genuine w ξ

/-! `hfiber : ¬ Determined (bindingClaim Genuine)` — a **modeling
hypothesis, never a theorem**, the same discipline `Instance.Identity` and
the axios `SuretyEonEalm` use: carried explicitly on every theorem that needs it,
never proved here, never a fresh axiom. -/

/-! ## Seeds -/

/-- The toolchain genesis seed. -/
abbrev genesisSeed : Node (LitePayload ClassName) := Node.ground 0 true

/-- **`surety_ceiling`** — the surety ceiling: one application of
    `Ceiling.ceiling` at this domain, under the domain's own `hfiber`.
    Cell coverage: T1 (verifiable, via `Total`/`trustSurface`) + T2
    (genuineness = ¬D, this theorem's gate; the forced generator's
    degeneracy = ¬C, cited from `Witness.Generator`, never restated here). -/
theorem surety_ceiling {Comm : Type} (Γ : Commitment Comm)
    (Genuine : Record → Context → Prop) (hfiber : ¬ Determined (bindingClaim Genuine))
    (P : Policy Signer) (σ : Snapshot Signer ClassName) (a : Node (LitePayload ClassName)) :
    (¬ ∃ S : Scheme Γ (bindingClaim Genuine), SnapshotSound S) ∧
    (∀ m ∈ depclosure a, m.seed? = true → m ∈ trustSurfaceI P σ a) ∧
    (TotalI P σ a → ∀ m ∈ depclosure a, m.seed? = false →
      (∃ e ∈ basisI P σ a, ∃ s t, e = .corroboration s t) ∧
      (∃ e ∈ basisI P σ a, ∃ s t tag, e = .vouch s t tag)) :=
  Ceiling.ceiling Γ (bindingClaim Genuine) hfiber gate tagOf closureOk P σ a

/-! ## The four non-vacuity witnesses (concrete `Unit` types) -/

section Nonvacuity

/-- The single concrete artifact every witness below reuses. -/
def p0 : LitePayload Unit := ⟨(), true, true⟩

def policyAll : Policy Unit := ⟨fun _ => true, fun _ => true⟩

def snapClosing (i : Nat) : Snapshot Unit Unit := [.vouch () i (), .corroboration () i]

/-- **W1** — a closed artifact: `σ` supplies one admitted vouch and one
    admitted corroboration targeting it. -/
theorem w1_closed_artifact :
    classifyI policyAll (snapClosing 1) (Node.derived 1 p0 []) = .closed := by
  simp [classifyI, Ceiling.classify, established, corroborated, gate, tagOf, closureOk,
    policyAll, snapClosing, p0, Node.id]

/-- **W2** — base-bounded `Total`: a single artifact closing directly onto
    the genesis seed. -/
theorem w2_base_bounded_total :
    TotalI policyAll (snapClosing 1) (Node.derived 1 p0 [genesisSeed (ClassName := Unit)]) := by
  apply (total_iff_every_nonseed_closed gate tagOf closureOk policyAll (snapClosing 1)
    (Node.derived 1 p0 [genesisSeed (ClassName := Unit)])).mpr
  intro m hmem hnotseed
  have hlist : depclosure (Node.derived 1 p0 [genesisSeed (ClassName := Unit)]) =
      [Node.derived 1 p0 [genesisSeed (ClassName := Unit)], genesisSeed (ClassName := Unit)] := by
    rw [depclosure]; simp [genesisSeed, depclosure]
  rw [hlist] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · simp [Ceiling.classify, established, corroborated, gate, tagOf, closureOk,
      policyAll, snapClosing, p0, Node.id, genesisSeed, Node.seed?]
  · simp [Node.seed?] at hnotseed

/-- **W3** — defeated `Total`: the same shape, an empty snapshot —
    `establishGap` — defeats `Total` via `unclosed_member_defeats_total`. -/
theorem w3_defeated_total :
    ¬ TotalI policyAll ([] : Snapshot Unit Unit)
      (Node.derived 1 p0 [genesisSeed (ClassName := Unit)]) := by
  apply unclosed_member_defeats_total gate tagOf closureOk policyAll ([] : Snapshot Unit Unit)
    (Node.derived 1 p0 [genesisSeed (ClassName := Unit)]) (Node.derived 1 p0
      [genesisSeed (ClassName := Unit)])
  · exact self_mem_depclosure _
  · rfl
  · simp [Ceiling.classify, established, gate, tagOf]

/-- **W4** — `no_vouchers_no_total`, instantiated: a policy admitting no
    vouchers forbids every non-seed `Total`. -/
theorem w4_no_vouchers_no_total :
    ¬ TotalI (ClassName := Unit) ⟨fun _ => true, fun _ => false⟩
      ([] : Snapshot Unit Unit) (Node.derived 1 p0 []) :=
  no_vouchers_no_total gate tagOf closureOk ⟨fun _ => true, fun _ => false⟩
    ([] : Snapshot Unit Unit) (fun _ => rfl) (Node.derived 1 p0 []) rfl

end Nonvacuity

end Instance.SuretyLite

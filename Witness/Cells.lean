import Core

/-!
# Witness.Cells — the corrected cell table

Three binary axes — determination, certifiability, monotonicity — give
eight nominal cells. Certifiability is **fibered on determination**: a
claim failing determination admits no scheme at all
(`EonEalm.determination_gate`), so for the two `¬D` rows the certifiability
column is never a free coordinate — it is not a third axis observed to
happen to be "n.a.," it is forced empty by the determination gate itself.
The two nominal cells `(¬D, scheme-exists, ·)` are therefore **empty by
theorem** (`undetermined_cell_empty`/`undetermined_cell_empty_nonmonotone`
below), leaving six inhabited cells: one verifiable cell and five distinct
trust flavors, each with its own witness claim, grade, and minimal cure.

## Grades

Each row is marked **mechanized-parametric** (a Lean witness, parametric
in a given `Entry`/`Context` where `Core.Model.Entry` carries no
inhabitedness axiom — the landed `inclusionClaim`/`revokedClaim` idiom) or
**cited** (Rice/Rice–Shapiro-grade — degeneracy's failure of
semi-decidability is a theorem this workspace cites rather than proves;
see `Witness.Generator`'s module doc for why no computation model is built
there, and `Core.Corollaries`' `npMembership_trivial` for why the oracle
stratum cannot manufacture a `¬Σ₁` fact either).

The two `¬C` rows carry both grades. Their *cited* witness is degeneracy,
as below. Their *mechanized* inhabitant is a different claim — divergence
of a committed build — which needs Mathlib's halting problem and so lands
at the computable stratum (`Effective.NonCertifiable`), cited from here
rather than restated, since this file stays Core-only.

## Where `Context.nontrivial` is consumed in this file

Exactly twice — rows 2 and 5 below — each stating a *fresh* concrete
witness of the `Core.Axes.exists_undetermined_claim` shape (rather than
extracting the existential's opaque witness, which would not expose the
shape a monotonicity proof needs). This footprint is documented in
`Core.lean`'s own module note, which names all three consuming sites:
`Core.Axes.exists_undetermined_claim` and these two rows.
-/

namespace Witness.Cells

open EonEalm

/-! ## Row 1 — (D, C, M), the verifiable cell -/

/-- The inclusion claim, restated core-side (the identical shape
    `TrichotomyComp.inclusionClaim` proves at the computable stratum in
    `Effective.Trichotomy`, reproved here since this file stays
    Core-only). -/
def inclusionClaim (e : Entry) : Claim := fun w _ => e ∈ w

theorem inclusionClaim_determined (e : Entry) : Determined (inclusionClaim e) :=
  fun _ _ _ => Iff.rfl

/-- List-append can only add entries, so a membership witness for `w`
    survives to any `w'` extending it. -/
theorem inclusionClaim_monotone (e : Entry) : Monotone (inclusionClaim e) := by
  intro w w' _ hmem hext
  obtain ⟨u, hu⟩ := hext
  rw [hu]
  exact List.mem_append_left u hmem

/-! Certifiability is **mechanized**, cited from `Effective.Trichotomy`
(`TrichotomyComp.inclusionClaim_computableMembership`) — this file stays
Core-only and does not reproduce it. -/

/-! ## Row 2 — (¬D, –, M), "trust the witness-of-history" -/

/-- The same construction `Core.Axes.exists_undetermined_claim` uses,
    restated here (not extracted from that existential, whose bound
    witness is opaque and cannot be shown `Monotone`): record-independent
    claims are `Monotone` for free, since they never inspect `w`. Two
    grades of the same shape exist: this **unconditional-abstract** one,
    and an **interpreted-hypothetical** twin — every instance's
    `bindingClaim`/`genuineness`, `hfiber`-carried
    (`Instance.Identity.bindingClaim`, `Instance.SuretyLite.bindingClaim`)
    — cited from there, not reproduced here. -/
theorem exists_undetermined_monotone : ∃ φ : Claim, ¬ Determined φ ∧ Monotone φ := by
  obtain ⟨ξ₁, ξ₂, hne⟩ := Context.nontrivial
  refine ⟨fun _ ξ => ξ = ξ₁, fun hdet => hne (((hdet [] ξ₁ ξ₂).mp rfl).symm), ?_⟩
  intro w w' ξ h _hext
  exact h

/-! The certifiability column is n.a. for this row: `¬D` fibers the
determination gate (the module-doc convention above), so `C` is never a
free coordinate here. -/

/-! ## Row 3 — (D, C, ¬M), "trust the liveness-holder" -/

/-- The landed witness is `Trichotomy.Transport.revokedClaim`/
    `revokedClaim_not_monotone` (coproduct-typed) — cited, not restated.
    This row adds the cleaner single-record absence form, parametric in a
    given entry `e` (`Core.Model.Entry` carries no inhabitedness axiom, so
    every witness extending a record takes its entry as a parameter — the
    landed `inclusionClaim`/`revokedClaim` idiom). -/
def absenceClaim (e : Entry) : Claim := fun w _ => e ∉ w

theorem absenceClaim_determined (e : Entry) : Determined (absenceClaim e) :=
  fun _ _ _ => Iff.rfl

/-- Non-monotone: `e` is absent from `[]`, but appending `e` makes it
    present — the `[] → [e]` flip. -/
theorem absenceClaim_not_monotone (e : Entry) (ξ : Context) :
    ¬ Monotone (absenceClaim e) := by
  intro hmono
  have h0 : absenceClaim e [] ξ := by simp [absenceClaim]
  have hext : ([] : Record) ⊑ [e] := ⟨[e], by simp⟩
  exact (hmono [] [e] ξ h0 hext) (by simp)

/-! Certifiability is annotated in `Effective.Cells` (this file stays
Core-only). -/

/-! ## Row 4 — (D, ¬C, M), "trust the voucher"

The cited witness — `Witness.Generator.degenerate`/`genuine` — is cited,
never restated: "the committed generator is degenerate" is fixed by the
bytes (`Witness.Generator.degenerate_extensional`), monotone (a committed
generator stays committed, so once degenerate, always degenerate under
further extension of the record), and non-certifiable by Rice–Shapiro (a
purely semantic property of an unbounded-domain generator's denotation —
`Witness.Generator`'s module doc explains why this file's package
mechanizes no computation model to state that theorem about).

The cell's mechanized inhabitant is
`Effective.NonCertifiable.stuckClaim` — "some entry names a build that
never terminates" — `Determined`, `Monotone`, and proved to fail
`ComputableMembership` from the halting problem. No new Lean content in
this row: both witnesses live elsewhere. -/

/-! ## Row 5 — (¬D, –, ¬M), "authored-by-A and currently-absent" -/

/-- The composed history+freshness trust, parametric in a given entry `e`
    and a `Context.nontrivial` pair `ξ₁ ≠ ξ₂`: authored-by-`ξ₁` and
    `e`-absent. -/
def authoredAbsentClaim (ξ₁ : Context) (e : Entry) : Claim := fun w ξ => ξ = ξ₁ ∧ e ∉ w

/-- ¬D at `w = []`: the conjunct varies with `ξ` there (`e ∉ []` holds
    unconditionally, so only the `ξ = ξ₁` half distinguishes contexts). -/
theorem authoredAbsentClaim_not_determined (e : Entry) :
    ∃ ξ₁ : Context, ¬ Determined (authoredAbsentClaim ξ₁ e) := by
  obtain ⟨ξ₁, ξ₂, hne⟩ := Context.nontrivial
  refine ⟨ξ₁, fun hdet => ?_⟩
  have h1 : authoredAbsentClaim ξ₁ e [] ξ₁ := ⟨rfl, by simp⟩
  have h2 := (hdet [] ξ₁ ξ₂).mp h1
  exact hne h2.1.symm

/-- ¬M via the same `[] → [e]` flip as row 3, now under the conjunction. -/
theorem authoredAbsentClaim_not_monotone (ξ₁ : Context) (e : Entry) :
    ¬ Monotone (authoredAbsentClaim ξ₁ e) := by
  intro hmono
  have h0 : authoredAbsentClaim ξ₁ e [] ξ₁ := ⟨rfl, by simp⟩
  have hext : ([] : Record) ⊑ [e] := ⟨[e], by simp⟩
  exact (hmono [] [e] ξ₁ h0 hext).2 (by simp)

/-! Certifiability is annotated in `Effective.Cells` (this file stays
Core-only). -/

/-! ## Row 6 — (D, ¬C, ¬M), "the current head's committed generator is
degenerate"

The composed reading: bytes-fixed (as row 4), but now flips on further
extension of the record (the current head's generator need not be the
prior head's), and Rice–Shapiro-blocked exactly as row 4 — cited, citing
`Witness.Generator` and the statement's T2 floor.

The cell's mechanized inhabitant is
`Effective.NonCertifiable.unsettledClaim` — "no entry names a build that
has terminated" — `Determined`, refuted by the next append that lands a
settled build (`unsettledClaim_not_monotone`), and non-certifiable by the
same halting-problem restriction. No Lean here: both witnesses live
elsewhere. -/

/-! ## The two empty-by-theorem displays -/

/-- The nominal `(¬D, scheme-exists, M)` cell is empty by theorem:
    `EonEalm.determination_gate` forces any claim failing determination to
    admit no snapshot-sound scheme regardless of the other axes. Two-line
    wrapper so the paper's table can cite a Lean name for each nominal
    cell rather than the shared theorem twice under different names. This
    is Result 1's content, not an accident of the table shape. -/
theorem undetermined_cell_empty {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hnd : ¬ Determined φ) : ¬ ∃ S : Scheme Γ φ, SnapshotSound S :=
  determination_gate hnd

/-- The nominal `(¬D, scheme-exists, ¬M)` cell — likewise empty, the
    `¬Monotone` hypothesis carried only so the table can cite a distinct
    name for the distinct nominal cell; the gate itself never inspects
    it. -/
theorem undetermined_cell_empty_nonmonotone {Comm : Type} (Γ : Commitment Comm) (φ : Claim)
    (hnd : ¬ Determined φ) (_hnm : ¬ Monotone φ) : ¬ ∃ S : Scheme Γ φ, SnapshotSound S :=
  determination_gate hnd

end Witness.Cells

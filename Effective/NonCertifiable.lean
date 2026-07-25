import Effective.Trichotomy
import Mathlib.Computability.PartrecCode

/-!
# Effective.NonCertifiable — inhabiting the two certifiability-failure cells

`Witness.Cells`'s rows 4 and 6 — the `(D, ¬C, M)` and `(D, ¬C, ¬M)` cells, the
paper's rows 3 and 4 — carried no Lean content: the only formalized non-certifiable
property in the workspace, `Witness.Generator.degenerate`, is a predicate over a
bare `Denote` map with no connection to `EonEalm.Claim`, so those two cells were
argued rather than exhibited. This module exhibits them: two genuine `Claim`s,
`Determined`, one `Monotone` and one not, each **proved** — not posited — to admit
no computable-stratum evidence scheme.

## Where the non-certifiability comes from

Not from a hypothesis. `TrichotomyComp.ComputableMembership` is the Σ₁ side of the
computable trichotomy; `computableMembership_rePred` below identifies it with
Mathlib's `REPred` (recursive enumerability), and the two claims' projections
restrict, along a computable embedding, to the *complement* of the halting
predicate, which `ComputablePred.halting_problem_not_re` refutes. The consequence
is then read off the landed biconditional (`trichotomy_snap_COMP_iff`): no
commitment with a `Computable` commitment function admits even a *snapshot*-sound
scheme with a `ComputablePred` verifier for either claim.

This is a different witness from the paper's chosen exemplar. Generator degeneracy
is Rice–Shapiro-grade and stays cited; divergence of a committed build is Π₁ and is
mechanized here. Both inhabit the same cell, and the cell needs one inhabitant.

## The alphabet hypothesis, and why some hypothesis is unavoidable

`Core.Model.Entry` is an opaque `axiom`, so a claim over `Record = List Entry` can
only reach a non-Σ₁ predicate if the alphabet is rich enough to name programs.
`[Denumerable Entry]` — the alphabet is countably infinite under a computable
coding, exactly what `Core.Model.Entry`'s own doc-comment already asserts of Σ — is
the hypothesis taken here, and it is a hypothesis about the *alphabet*, never about
certifiability.

Some such hypothesis is forced, and `computableMembership_of_isEmpty` proves it: over
an empty alphabet `Record` collapses to `{[]}` and *every* claim's projection is
`ComputableMembership`, so the `¬C` cells are genuinely empty there. This is the
`Witness.Generator.bounded_domain_trivializes` idiom — the degenerate case stated as
a theorem rather than left as a warning.

`[Denumerable Entry]` is satisfiable (nothing in `Core` constrains `Entry`'s
cardinality; `Entry := ℕ` is a model), so the results below are not vacuous. It is
the same conditional grade every result in `Effective` already carries, which
assumes `[Primcodable Entry]` throughout.
-/

namespace Effective.NonCertifiable

open EonEalm TrichotomyComp

/-! ## Σ₁ membership *is* recursive enumerability -/

/-- `ComputableMembership` — a Σ₁-witness checker that is `ComputablePred`, existentially
    quantified over the witness type — implies Mathlib's `REPred`, the domain of a
    partial computable function. The bridge is an unbounded search over the witness
    type's `Primcodable` coding: `Nat.rfind` scans ℕ, decodes each index as a candidate
    witness, and halts on the first one the checker accepts. Without this, no
    computable-stratum claim can be *refuted*, only established. -/
theorem computableMembership_rePred [Primcodable Entry] {ψ : Record → Prop}
    (h : ComputableMembership ψ) : REPred ψ := by
  obtain ⟨W, hWPC, Chk, hChk, hiff⟩ := h
  letI := hWPC
  -- The checker as a `Bool`-valued computable function. `computable_iff` supplies it
  -- directly, so the `Decidable` instance bundled inside `ComputablePred` never has to
  -- be threaded through the search below (where it would be needed at a *different*
  -- argument shape than the one the bundle carries).
  obtain ⟨g, hg, hgeq⟩ := ComputablePred.computable_iff.1 hChk
  have hgiff : ∀ (w : Record) (t : W), Chk w t ↔ g (w, t) = true := fun w t =>
    (congrFun hgeq (w, t)).to_iff
  -- The search predicate: index `n` succeeds iff it codes a witness the checker accepts.
  have hqc : Computable₂ fun (w : Record) (n : ℕ) =>
      ((Encodable.decode (α := W) n).map fun t => g (w, t)).getD false :=
    Computable.option_getD
      (Computable.option_map (Computable.decode.comp Computable.snd)
        (hg.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)))
      (Computable.const false)
  refine (Partrec.dom_re (Partrec.rfind (Computable₂.partrec₂ hqc))).of_eq fun w => ?_
  constructor
  · intro hdom
    obtain ⟨n, hn, -⟩ := Nat.rfind_dom.1 hdom
    simp only [PFun.coe_val, Part.mem_some_iff] at hn
    refine (hiff w).2 ?_
    rcases hdec : Encodable.decode (α := W) n with - | t
    · rw [hdec] at hn; simp at hn
    · rw [hdec] at hn
      exact ⟨t, (hgiff w t).2 (by simpa using hn.symm)⟩
  · intro hψ
    obtain ⟨t, ht⟩ := (hiff w).1 hψ
    -- `encode t` is an index the search accepts, and every earlier index is total.
    refine Nat.rfind_dom.2 ⟨Encodable.encode t, ?_, fun {_} _ => trivial⟩
    simp [PFun.coe_val, Encodable.encodek, (hgiff w t).1 ht]

/-- `REPred` is closed under precomposition with a `Computable` map — the restriction
    step both refutations take. Stated here because `REPred` unfolds to `Partrec`, so
    dot notation on an `REPred` hypothesis goes looking for a nonexistent
    `REPred.comp`. -/
theorem rePred_comp {α β} [Primcodable α] [Primcodable β] {p : β → Prop} {f : α → β}
    (hp : REPred p) (hf : Computable f) : REPred fun a => p (f a) :=
  Partrec.comp hp hf

/-! ## The degenerate alphabet — why the hypothesis below is forced -/

/-- Over an empty alphabet `Record` has exactly one element, so every claim's
    projection is `ComputableMembership` and the `¬C` cells are empty. The
    counterpart of `Witness.Generator.bounded_domain_trivializes`: it is the
    alphabet's richness, not any choice of claim, that makes non-certifiability
    reachable at all. -/
theorem computableMembership_of_isEmpty [Primcodable Entry] [IsEmpty Entry]
    (ψ : Record → Prop) : ComputableMembership ψ := by
  classical
  have hnil : ∀ w : Record, w = [] := fun w => match w with
    | [] => rfl
    | e :: _ => (IsEmpty.false e).elim
  refine ⟨Unit, inferInstance, fun w _ => ψ w, ?_,
    fun _ => ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩⟩
  refine ComputablePred.computable_iff.2
    ⟨fun _ => decide (ψ ([] : Record)), Computable.const _, funext fun p => propext ?_⟩
  rw [hnil p.1]
  exact (decide_eq_true_iff).symm

/-! ## Reading an entry as a program

`Denumerable Entry` gives a computable bijection `Entry ≃ Code` in both directions,
which is all the two witnesses need: it lets a claim about the record speak about the
programs its entries name, and it lets the halting predicate be restricted back onto
single-entry records. -/

section Alphabet

variable [Denumerable Entry]

/-- The program an entry names, under the alphabet's own coding. -/
def entryCode (e : Entry) : Nat.Partrec.Code :=
  Denumerable.ofNat Nat.Partrec.Code (Encodable.encode e)

/-- The entry naming a given program — `entryCode`'s inverse, and the direction the
    refutations need computable. -/
def codeEntry (c : Nat.Partrec.Code) : Entry :=
  Denumerable.ofNat Entry (Encodable.encode c)

theorem entryCode_codeEntry (c : Nat.Partrec.Code) : entryCode (codeEntry c) = c := by
  simp [entryCode, codeEntry, Denumerable.encode_ofNat, Denumerable.ofNat_encode]

theorem codeEntry_computable : Computable (codeEntry : Nat.Partrec.Code → Entry) :=
  (Computable.ofNat Entry).comp Computable.encode

/-- A single-entry record, as a computable function of the program it names. This is
    the embedding along which both claims restrict to the halting predicate. -/
theorem singletonRecord_computable :
    Computable fun c : Nat.Partrec.Code => ([codeEntry c] : Record) :=
  Computable₂.comp Computable.list_cons codeEntry_computable (Computable.const [])

/-- The entry's build never terminates: the program it names diverges on input `0`.
    A Π₁ property of the bytes — determined by the record, and the complement of a
    Σ₁-complete one. -/
def Diverges (e : Entry) : Prop := ¬ (Nat.Partrec.Code.eval (entryCode e) 0).Dom

/-- A settled build, exhibited: `Code.zero` halts on every input, so the entry naming
    it is a concrete non-`Diverges` entry. This is what makes the non-monotone
    witness's flip a construction rather than an existence claim. -/
theorem not_diverges_settledEntry : ¬ Diverges (codeEntry Nat.Partrec.Code.zero) := by
  intro h
  refine h ?_
  rw [entryCode_codeEntry]
  exact trivial

end Alphabet

/-! ## Row 4 — `(D, ¬C, M)`, "trust the voucher"

"Some build in the record never terminates." Fixed by the bytes, monotone (an entry
already in the record stays in it), and not semi-decidable: restricted to
single-entry records it *is* the complement of the halting predicate. -/

section Witnesses

variable [Denumerable Entry]

/-- The `(D, ¬C, M)` witness: the record contains an entry whose build diverges. -/
def stuckClaim : Claim := fun w _ => ∃ e ∈ w, Diverges e

theorem stuckClaim_determined : Determined stuckClaim := fun _ _ _ => Iff.rfl

/-- Appending can only add entries, so a divergent entry present in `w` is still
    present in any `w'` extending it. -/
theorem stuckClaim_monotone : Monotone stuckClaim := by
  rintro w w' _ ⟨e, hmem, hdiv⟩ ⟨u, rfl⟩
  exact ⟨e, List.mem_append_left u hmem, hdiv⟩

/-- **The non-certifiability, proved.** Restricting the claim's projection along
    `c ↦ [codeEntry c]` gives exactly `¬(eval c 0).Dom`, which is not r.e.
    (`ComputablePred.halting_problem_not_re`); `computableMembership_rePred` carries
    that back to `ComputableMembership`. -/
theorem stuckClaim_not_computableMembership :
    ¬ ComputableMembership (determinedProj stuckClaim stuckClaim_determined) := by
  intro h
  refine ComputablePred.halting_problem_not_re 0 ?_
  refine REPred.of_eq
    (rePred_comp (computableMembership_rePred h) singletonRecord_computable) fun c => ?_
  simp [determinedProj, stuckClaim, Diverges, entryCode_codeEntry]

/-! ## Row 6 — `(D, ¬C, ¬M)`, the same failure composed with expiry

"No build in the record has terminated." Fixed by the bytes and non-certifiable for
the same reason, but refuted by the next append that lands a settled build — the
monotonicity failure is exhibited, not assumed. -/

/-- The `(D, ¬C, ¬M)` witness: every entry in the record names a divergent build. -/
def unsettledClaim : Claim := fun w _ => ∀ e ∈ w, Diverges e

theorem unsettledClaim_determined : Determined unsettledClaim :=
  fun _ _ _ => Iff.rfl

/-- Non-monotone via the `[] → [codeEntry Code.zero]` flip: the empty record satisfies
    the claim vacuously, and appending the entry naming a halting program refutes it. -/
theorem unsettledClaim_not_monotone (ξ : Context) :
    ¬ Monotone unsettledClaim := by
  intro hmono
  have h0 : unsettledClaim ([] : Record) ξ := by simp [unsettledClaim]
  have hext : ([] : Record) ⊑ [codeEntry Nat.Partrec.Code.zero] :=
    ⟨[codeEntry Nat.Partrec.Code.zero], by simp⟩
  exact not_diverges_settledEntry
    (hmono [] _ ξ h0 hext _ (List.mem_singleton_self _))

theorem unsettledClaim_not_computableMembership :
    ¬ ComputableMembership
      (determinedProj unsettledClaim unsettledClaim_determined) := by
  intro h
  refine ComputablePred.halting_problem_not_re 0 ?_
  refine REPred.of_eq
    (rePred_comp (computableMembership_rePred h) singletonRecord_computable) fun c => ?_
  simp [determinedProj, unsettledClaim, Diverges, entryCode_codeEntry]

/-! ## The cells, closed against the landed biconditional

`trichotomy_snap_COMP_iff` turns each `¬ComputableMembership` into the statement the
cell table actually makes: no scheme, over any commitment whose commitment function
is `Computable`. Snapshot-soundness is the *weaker* obligation, so refuting it
refutes enduring soundness too. -/

/-- Row 4's cell, closed: `stuckClaim` admits no snapshot-sound scheme with a
    `ComputablePred` verifier over any computable commitment. -/
theorem stuckClaim_no_snapshot_scheme {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm)
    (hCComp : Computable Γ.C) :
    ¬ ∃ (S : Scheme Γ stuckClaim) (_ : Primcodable S.Proof),
        SnapshotSound S ∧ ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2) := by
  intro hS
  obtain ⟨_, hcm⟩ := (trichotomy_snap_COMP_iff Γ stuckClaim hCComp).mp hS
  exact stuckClaim_not_computableMembership hcm

/-- The enduring form of row 4's cell, which is the one the row's monotonicity would
    otherwise buy: `EnduringSound` implies `SnapshotSound`, so the same refutation
    covers it. -/
theorem stuckClaim_no_enduring_scheme {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm)
    (hCComp : Computable Γ.C) :
    ¬ ∃ (S : Scheme Γ stuckClaim) (_ : Primcodable S.Proof),
        EnduringSound S ∧ ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2) := by
  rintro ⟨S, hSPC, hsound, hVComp⟩
  exact stuckClaim_no_snapshot_scheme Γ hCComp
    ⟨S, hSPC, enduringSound_snapshotSound hsound, hVComp⟩

/-- Row 6's cell, closed by the identical route. -/
theorem unsettledClaim_no_snapshot_scheme {Comm : Type} [Primcodable Comm] (Γ : Commitment Comm)
    (hCComp : Computable Γ.C) :
    ¬ ∃ (S : Scheme Γ unsettledClaim) (_ : Primcodable S.Proof),
        SnapshotSound S ∧ ComputablePred (fun p : Comm × S.Proof => S.V p.1 p.2) := by
  intro hS
  obtain ⟨_, hcm⟩ := (trichotomy_snap_COMP_iff Γ unsettledClaim hCComp).mp hS
  exact unsettledClaim_not_computableMembership hcm

end Witnesses

end Effective.NonCertifiable

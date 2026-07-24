import Core.Model

/-!
# Commitment — the abstract commitment scheme

Abstract commitment `C` with a **binding axiom** and an extension-verification relation
`VC`, bundled as a `Commitment` structure so a scheme can be built generically over any
instance. Deliberately **not** a set of bare top-level axioms: binding **without**
compression (`C = id` is a valid instance; binding-with-compression is unsatisfiable)
only typechecks as a genuine non-vacuity witness if `Commitment` is a first-class
structure with multiple inhabitants, not a global axiom. `idCommitment` below is
exactly that witness.
-/

namespace EonEalm

/-- An abstract commitment scheme over codomain `Comm` — the commitment function, its
    binding axiom, and the extension-verification relation `VC` with its
    soundness/completeness obligations. `VC h₀ h π` reads "`π` certifies that the
    record committing to `h₀` is a prefix of the record committing to `h`." -/
structure Commitment (Comm : Type) where
  /-- The extension-proof witness type. -/
  VCProof : Type
  /-- The commitment function, poly-time-computable at the effective stratum (not
      modeled here). -/
  C : Record → Comm
  /-- The extension-verification relation itself. -/
  VC : Comm → Comm → VCProof → Prop
  /-- Binding: `C(w) = C(w′) ⟹ w = w′`. The *only* axiom licensed on `C` — do NOT
      additionally assume compression. -/
  binding : ∀ w w', C w = C w' → w = w'
  /-- `VC`-soundness: an accepting extension proof forces the genuine prefix relation.
      At the effective stratum this is discharged by collision extraction (accepting
      forgery ⟹ extracted hash collision); see `Core.CollisionExtraction` for the
      abstract shape of that transport. -/
  soundness : ∀ w₀ w h₀ h π, VC h₀ h π → h₀ = C w₀ → h = C w → w₀ ⊑ w
  /-- `VC`-completeness: every genuine extension has a certifying proof. -/
  completeness : ∀ w₀ w, w₀ ⊑ w → ∃ π, VC (C w₀) (C w) π

/-- Non-vacuity witness: `Comm := Record`, `C := id`. Binding is `rfl`-immediate;
    `VC` is the extension relation itself (no cryptography, no compression). Confirms
    the `Commitment` structure's axioms are jointly satisfiable. -/
noncomputable def idCommitment : Commitment Record where
  VCProof := Unit
  C := id
  binding := fun _ _ h => h
  VC := fun h₀ h _ => h₀ ⊑ h
  soundness := fun _w₀ _w _h₀ _h _π hvc h₀eq heq => by
    simp only [id] at h₀eq heq; rw [h₀eq, heq] at hvc; exact hvc
  completeness := fun w₀ w hext => ⟨(), by simpa using hext⟩

/-! ## A computable commitment witness

`idCommitment` above is `noncomputable` and carries no `Decidable` instance, so it
cannot witness a decidable-verifier stratum's "`VC` decidable" requirement. `⊑` (`Ext`)
is a bare `∃`, not decidable in general over an abstract `Entry`; under
`[DecidableEq Entry]` a prefix check is a standard structural walk, so this section
adds a genuinely computable decision procedure for `⊑` and a decidable `Commitment`
built on it — additive only, `idCommitment` itself is untouched. -/

/-- Decision procedure for `⊑` given decidable equality on `Entry`: `w` is a prefix of
    `w'` iff they agree element-wise up to `w`'s length. -/
def extDec [DecidableEq Entry] : Record → Record → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then extDec as bs else false

theorem extDec_iff [DecidableEq Entry] :
    ∀ w w' : Record, extDec w w' = true ↔ w ⊑ w'
  | [], w' => by simp [extDec, Ext]
  | _ :: _, [] => by
      simp only [extDec, Bool.false_eq_true, false_iff]
      rintro ⟨u, hu⟩
      simp at hu
  | a :: as, b :: bs => by
      simp only [extDec]
      split
      · rename_i hab
        subst hab
        rw [extDec_iff as bs]
        constructor
        · rintro ⟨u, hu⟩
          exact ⟨u, by simp [hu]⟩
        · rintro ⟨u, hu⟩
          exact ⟨u, by simpa using hu⟩
      · rename_i hab
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨u, hu⟩
        simp at hu
        exact hab hu.1.symm

/-- `⊑` is decidable given decidable equality on `Entry`. -/
instance instDecidableExt [DecidableEq Entry] (w w' : Record) : Decidable (w ⊑ w') :=
  decidable_of_iff (extDec w w' = true) (extDec_iff w w')

/-- A computable commitment witness: same `C := id`, no-compression shape as
    `idCommitment`, but under `[DecidableEq Entry]`, where `VC` resolves through
    `instDecidableExt` rather than being merely propositional. -/
def idCommitmentComp [DecidableEq Entry] : Commitment Record where
  VCProof := Unit
  C := id
  binding := fun _ _ h => h
  VC := fun h₀ h _ => h₀ ⊑ h
  soundness := fun _w₀ _w _h₀ _h _π hvc h₀eq heq => by
    simp only [id] at h₀eq heq; rw [h₀eq, heq] at hvc; exact hvc
  completeness := fun w₀ w hext => ⟨(), by simpa using hext⟩

/-- `idCommitmentComp`'s `VC` is decidable. -/
instance instDecidableIdCommitmentCompVC [DecidableEq Entry]
    (h₀ h : Record) (π : Unit) : Decidable (idCommitmentComp.VC h₀ h π) := by
  show Decidable (h₀ ⊑ h)
  infer_instance

end EonEalm

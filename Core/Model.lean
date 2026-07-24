/-!
# Model — records, worlds, claims

No Mathlib dependency: the extension order `⊑` is the list-prefix relation, defined
and proved reflexive/transitive/antisymmetric directly rather than borrowed from a
`Preorder`/`List.IsPrefix` typeclass, keeping `Core`'s trust base to exactly the
axioms declared below.
-/

namespace EonEalm

/-- The entry alphabet Σ, abstract (countable, poly-time-computable length measure
    `|·|` — the length measure itself is not modeled here; it is the effective
    stratum's proof-size bound, and this package does not encode complexity bounds
    at all). -/
axiom Entry : Type

/-- Record space `R = Σ*`, records are finite lists of entries; `(R, ⊑)` is a poset
    with least element `[]`. -/
abbrev Record := List Entry

/-- Extension order `⊑` = prefix order (what a Merkle log realizes). -/
def Ext (w w' : Record) : Prop := ∃ u : List Entry, w' = w ++ u

@[inherit_doc] scoped infix:50 " ⊑ " => Ext

theorem ext_refl (w : Record) : w ⊑ w := ⟨[], by simp⟩

theorem ext_trans {w w' w'' : Record} (h1 : w ⊑ w') (h2 : w' ⊑ w'') : w ⊑ w'' := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨u', hu'⟩ := h2
  exact ⟨u ++ u', by rw [hu', hu, List.append_assoc]⟩

theorem ext_antisymm {w w' : Record} (h1 : w ⊑ w') (h2 : w' ⊑ w) : w = w' := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨u', hu'⟩ := h2
  have hlen : w.length = w'.length := by
    have := congrArg List.length hu'
    simp only [hu, List.length_append] at this ⊢
    omega
  have : u = [] := by
    have hlu : w.length + u.length = w'.length := by rw [hu]; simp
    have : u.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  rw [hu, this, List.append_nil]

/-- Ambient contexts Ξ — authorship facts, intentions, key custody, other artifacts.
    Inhabited (licenses non-vacuity of the axes below) and non-trivial (`|Ξ| ≥ 2`, so
    "record-determined" is a genuine restriction rather than vacuously true). No
    order is imposed on Ξ. -/
axiom Context : Type
axiom Context.inhabited : Nonempty Context
axiom Context.nontrivial : ∃ ξ ξ' : Context, ξ ≠ ξ'

noncomputable instance : Inhabited Context := ⟨Classical.choice Context.inhabited⟩

/-- Worlds = R × Ξ. -/
abbrev World := Record × Context

/-- A claim is a predicate over worlds. -/
abbrev Claim := Record → Context → Prop

end EonEalm

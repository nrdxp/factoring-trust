/-!
# Generator — the forced generator: denotation, degeneracy, and underdetermination

Models the **forced generator** object: a program `G` whose execution reconstructs an
artifact's output. `⟦G⟧` is `G`'s **denotation** — the (partial) computable function it
computes, in the Scott–Strachey sense. `degenerate(G) ⟺ finite(range(⟦G⟧))`,
considered with its nominal, unbounded input signature.

## What this module deliberately does not do

- **No computation model, hence no undecidability theorem.** `Gen` carries no
  evaluator, no notion of program size, no `Decidable` instance for `degenerate` —
  there is nothing here for Rice's theorem to be stated *about* as an internal fact.
  Rice's theorem itself (and its promise-refinement) is cited evidence elsewhere, not
  mechanized in this package, and this module does not attempt a first mechanization
  of it either — only the **predicate** `degenerate` it ranges over.
- **No domain-specific wiring.** This is the domain-neutral generator model, used to
  witness the T2 (genuineness) cell generically; a concrete build-provenance
  instantiation (source classes, gates, corroboration) is a different, cited
  follow-up corpus this file does not depend on or reproduce.

## No Mathlib

Finiteness of a range is stated without `Set.Finite`: a function's range is finite
iff some list of outputs bounds every value it ever produces — classically
equivalent to `Set.Finite` over the induced set of realized outputs, without a new
Mathlib dependency.
-/

namespace Witness
namespace Generator

/-- A generator's denotation map `⟦·⟧ : Gen → (Input ⇀ Output)`. Partiality
    (`Option Output`) models non-halting or no output on a given input. Left as a
    bare parameter rather than an evaluator defined by recursion on `Gen`'s syntax,
    precisely because every definition below depends only on this map, never on how
    `G` is written — `degenerate_extensional` cashes that out as a proved fact, not
    an assumption. -/
abbrev Denote (Gen Input Output : Type) : Type := Gen → Input → Option Output

variable {Gen Input Output : Type}

/-- Range-finiteness, without `Set.Finite`: `f`'s range is finite iff some list of
    outputs bounds every value `f` ever produces. -/
def RangeFinite (f : Input → Option Output) : Prop :=
  ∃ ys : List Output, ∀ x y, f x = some y → y ∈ ys

/-- Degeneracy: `G` is degenerate iff `⟦G⟧`'s range is finite — emission from a
    finite table, uniformly covering the constant emitter and the lookup-table
    emitter, as opposed to a genuine parameterized transformation whose range over an
    unbounded domain is infinite. `G` is considered here with its *nominal* input
    type `Input` — the domain finiteness is measured against is the generator's
    declared signature, never the single committed argument any one realization
    actually supplied (`Realizes` below is the latter, and is a different,
    non-quantified notion). A purely *semantic* (extensional) property of `⟦G⟧`
    alone, never of `G`'s syntax, size, or program text — exactly Rice's theorem's
    precondition (the theorem itself is cited, not proved, here). -/
def degenerate (denote : Denote Gen Input Output) (G : Gen) : Prop :=
  RangeFinite (denote G)

/-- Genuineness: the complementary case, an infinite-range, genuinely parameterized
    transformation. Finite/infinite range is exhaustive by construction (classical
    logic) — there is no third case being elided. -/
def genuine (denote : Denote Gen Input Output) (G : Gen) : Prop :=
  ¬ degenerate denote G

theorem genuine_iff_infinite_range (denote : Denote Gen Input Output) (G : Gen) :
    genuine denote G ↔ ¬ RangeFinite (denote G) := Iff.rfl

/-- Degeneracy depends only on `⟦G⟧` — the extensionality Rice's theorem requires,
    stated as a proved consequence of the definition rather than merely asserted:
    two generators, however differently written, with the same denotation are
    degenerate (or not) together. -/
theorem degenerate_extensional (denote : Denote Gen Input Output) {G G' : Gen}
    (h : denote G = denote G') : degenerate denote G ↔ degenerate denote G' := by
  simp only [degenerate, h]

/-- The unbounded-domain clause, made precise: `Input` has no finite covering list.
    This is load-bearing ("over any finite domain every function is a lookup table
    and the property trivializes") — stated as a hypothesis a later theorem may
    carry, not baked into `degenerate`'s own definition (which stays meaningful, if
    trivial, without it: see `bounded_domain_trivializes`). -/
def UnboundedDomain (Input : Type) : Prop := ∀ l : List Input, ∃ x : Input, x ∉ l

/-- The trivialization, proved rather than merely asserted. Over a domain covered by
    a finite list, *every* function is degenerate — the distinction collapses
    exactly as the definition warns, which is why `degenerate` is only a meaningful
    (non-vacuous) split when `Input` satisfies `UnboundedDomain`. -/
theorem bounded_domain_trivializes {l : List Input} (hcover : ∀ x : Input, x ∈ l)
    (f : Input → Option Output) : RangeFinite f := by
  refine ⟨l.filterMap f, fun x y hxy => ?_⟩
  exact List.mem_filterMap.mpr ⟨x, hcover x, hxy⟩

/-- A build, as a generator applied to committed source: the artifact's record
    realizes `B = ⟦G⟧(z)` for its own committed input `z` and committed output `B` —
    the *one* input/output pair the build actually exhibited. Deliberately **not**
    `degenerate`/`genuine`: those quantify over the whole of `Input`, this over a
    single witnessed pair. Keeping the two apart is exactly the content that the
    witnessed pair buys the verifier nothing about `G`'s behavior on the rest of its
    domain — a fact this module states as a shape (the two predicates take different
    arguments) rather than proves (the proof is the cited halting-problem reduction,
    out of scope here). -/
def Realizes (denote : Denote Gen Input Output) (G : Gen) (z : Input) (B : Output) : Prop :=
  denote G z = some B

/-- Laundering via a degenerate forced generator: a build that realizes its output
    through a generator that is, in fact, degenerate. The canonical witness: `G`
    hardcodes one compressed literal `z` and always inflates it, so `⟦G⟧`'s range is
    finite (a single point, in the sharpest case) regardless of what `G`'s nominal
    signature could accept — as opposed to a stock decompressor, whose range over
    varying compressed inputs is unbounded. -/
def GeneratorLaundering (denote : Denote Gen Input Output) (G : Gen) (z : Input)
    (B : Output) : Prop :=
  Realizes denote G z B ∧ degenerate denote G

/-- A `GeneratorLaundering` build is, in particular, a `Realizes` witness. -/
theorem generatorLaundering_realizes (denote : Denote Gen Input Output) {G : Gen}
    {z : Input} {B : Output} (h : GeneratorLaundering denote G z B) :
    Realizes denote G z B := h.1

end Generator

/-! ## Genuineness is underdetermined by the output alone, and the split is
non-vacuous over byte-shaped inputs

Two theorems, domain-neutral: observing an artifact's output bytes alone cannot
distinguish a genuine generator from a degenerate (laundering) one, and the
genuine/degenerate split is achievable — not just abstractly, but for a faithful
concrete choice of what a generator actually consumes: arbitrary-length byte/bit
strings, of no fixed bound. -/

/-- An element of a `Nat` list is bounded by the list's `foldr max`. Core-Lean
    helper, no Mathlib. -/
private theorem le_foldr_max : ∀ (xs : List Nat) (n : Nat), n ∈ xs → n ≤ xs.foldr max 0
  | [], _, hn => by cases hn
  | a :: as, n, hn => by
      rcases List.mem_cons.mp hn with h | h
      · subst h
        show n ≤ max n (as.foldr max 0)
        exact Nat.le_max_left _ _
      · show n ≤ max a (as.foldr max 0)
        exact Nat.le_trans (le_foldr_max as n h) (Nat.le_max_right _ _)

/-- **The underdetermination witness.** A genuine generator (`true`, the identity on
    `Nat` — unbounded range, so `genuine`) and a degenerate one (`false`, constantly
    `42` — range `{42}`, so `degenerate`) both realize the *same* output `42`, the
    first on input `42` (identity(42) = 42), the second on input `0` (constant(0) =
    42). This is an actual exhibited pair over a concrete `Denote`, not a hypothesis
    about one: the pair `(z, B) = (42, 42)` (or `(z', B) = (0, 42)`) is consistent
    with both a genuine and a degenerate generator, so observing it settles nothing
    about which side of the genuine/degenerate split the committed `G` is actually
    on. -/
theorem genuineness_underdetermined :
    ∃ (Gen Input Output : Type) (denote : Generator.Denote Gen Input Output)
      (G G' : Gen) (z z' : Input) (B : Output),
      Generator.genuine denote G ∧ Generator.degenerate denote G'
        ∧ Generator.Realizes denote G z B ∧ Generator.Realizes denote G' z' B := by
  refine ⟨Bool, Nat, Nat,
    fun g n => match g with | true => some n | false => some 42,
    true, false, 42, 0, 42, ?_, ?_, rfl, rfl⟩
  · -- genuine true: ¬ RangeFinite (fun n => some n) — no finite list bounds all of ℕ.
    rintro ⟨ys, hys⟩
    have hmem : (ys.foldr max 0 + 1) ∈ ys := hys _ _ rfl
    have hbound := le_foldr_max ys _ hmem
    omega
  · -- degenerate false: RangeFinite (fun _ => some 42), witnessed by [42].
    refine ⟨[42], fun x y hxy => ?_⟩
    have : (42 : Nat) = y := by injection hxy
    simp [this]

/-- **The transfer, proved rather than merely asserted.** `List Bool` —
    arbitrary-length bit strings, the faithful shape of a committed byte payload —
    satisfies `UnboundedDomain`: given any finite covering candidate `l`, the
    all-`false` string one longer than every member of `l` cannot equal any member
    of `l` (distinct lengths), so `l` fails to cover it. -/
theorem unboundedDomain_byteInput : Generator.UnboundedDomain (List Bool) := by
  intro l
  refine ⟨List.replicate ((l.map List.length).foldr max 0 + 1) false, ?_⟩
  generalize hn : (l.map List.length).foldr max 0 + 1 = n
  intro hmem
  have hlen : (List.replicate n false).length = n := by simp
  have hmem' : (List.replicate n false).length ∈ l.map List.length :=
    List.mem_map_of_mem hmem
  rw [hlen] at hmem'
  have hbound : n ≤ (l.map List.length).foldr max 0 := le_foldr_max (l.map List.length) n hmem'
  omega

end Witness

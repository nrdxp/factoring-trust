import Core
import Ceiling.Gate

/-!
# Ceiling — Junction: the gate's scheme-world result forces the accounting-world
# trust surface to contain the seeds, for every scheme

`Ceiling.Gate`'s old `ceiling` bundled three facts sharing the argument names
`φ_bind : Claim` and `a : Node Payload` without ever relating them. This file
builds the missing junction. **It has already been through one failed
attempt, and the failure is recorded here because the fix depends on it.**

## Round 1 (rejected) — a conjunction is not a relation

The first `Discharges` here was `m.seed? = true ∧ SnapshotSound S`. The
lead-maintainer's objection, verified against the file and conceded:
**every consumer projected exactly one component.** L1's proof
(`fun h => binding_admits_no_scheme φ_bind hfiber Γ ⟨S, h.2⟩`) discards `m`
entirely; the seed-only non-vacuity check discards `S`. A conjunction whose
every use projects one side is two independent facts riding in a pair, not a
relation — the SAME defect §1.6(iii)'s bundle had, with more syntax around
it. `discharges_requires_seed` (that both conjuncts were individually
non-trivial) answered the wrong question: non-vacuity of each half is not
evidence the two interact.

## Round 2 — why it couldn't be fixed in place

`Scheme Γ φ_bind`'s only surface is `Comm`/`Proof` (`V : Comm → Proof →
Prop`); nothing in `Node Payload` — abstract, carrying no `Record` — can
reach it without a map. `EonEalm.Entry` is `axiom Entry : Type`, opaque by
construction, so the neutral core cannot manufacture one: domain-neutrality
working as designed, not a gap (`.ledger/trichotomy/STATEMENT-rc-v0.7.md`,
v0.8 AMENDMENT, ratified 2026-07-24). The fix is `RecordRealization` below:
the junction is now PARAMETERIZED on a domain-supplied record map, exactly
the shape `Ceiling.Commitment`-style structures already take (see
`Core.Commitment`) — a function bundled with the properties it must satisfy,
supplied per domain, never manufactured in the neutral core.

## `RecordRealization` — the missing embedding, named and required

A **record realization** `ρ : RecordRealization Payload` is `recordOf : Node
Payload → Record` satisfying:
- **(R1) faithful** — dependency-order faithfulness: `m ∈ depclosure n →
  recordOf m ⊑ recordOf n`, so building atop an artifact EXTENDS its record.
- **(R2) seedBoundary** — a node is a seed exactly when its record commits no
  prior entries: `m.seed? = true ↔ recordOf m = []`. This is the conjunct
  round 1's `Discharges` was missing: it ties the accounting-side seed flag
  to a scheme-side FACT ABOUT THE RECORD, not to a bare Boolean sitting next
  to an unrelated one.

`countRealization` below (parametric in one `Entry`, since the axiom carries
no inhabitedness) proves R1+R2 jointly satisfiable — the structure itself is
non-vacuous before anything is built on it.

## `Discharges`, round 2 — a genuine relation

`Discharges Γ φ_bind ρ S m := SnapshotSound S ∧ ∃ c, S.V (Γ.C (ρ.recordOf m))
c` — "S certifies m's establishment from `ρ.recordOf m` alone." **The
acceptance test round 1 failed: does any proof consume both components in
one step?** `discharges_forces_binding` does:
`hsound (ρ.recordOf m) c hc` applies the FIRST component (a function) to
witnesses extracted from the SECOND — neither half is discardable there.
Honesty about what did NOT change: L1 (`no_seed_discharged`) still proves
its conclusion from `SnapshotSound S` alone, because that fact — `hfiber`
kills every `SnapshotSound` scheme for `φ_bind`, full stop — is genuinely
`m`-independent; no amount of definitional cleverness makes it otherwise, and
claiming L1 itself was the joint witness would repeat round 1's mistake in a
different sentence. The joint content lives in `discharges_forces_binding`
and `discharges_seed_iff_certifies_empty`, not in L1.

## Round 3 — both instances CONSTRUCT their realization

An unconstructed `ρ` only shows the ceiling holds IF a realization exists;
it never shows one does. `Instance.Identity.identityRealization` and
`Instance.SuretyLite.suretyRealization` both build `countRealization`
concretely — `identity_ceiling`/`surety_ceiling` no longer take `ρ` as an
argument at all, only the one `Entry` `countRealization` needs. Neither
instance's LOCAL model (`KeyEvent`/`chain`, `LitePayload`) imports the eml
bridge or the axios atom DAG — both stay self-contained, vendoring nothing.
`Instance.Identity.identity_recCount_chain` additionally checks the
construction against the domain's own closure characterization
(`depclosure_chain`-shaped induction on `chain`), not just cites the
general bound.
-/

namespace Ceiling

open EonEalm

variable {Payload : Type}

-- ===========================================================================
-- RecordRealization — the missing embedding
-- ===========================================================================

/-- **A record realization for `a`**: the domain-supplied map from the
    accounting world into the scheme world, subject to (R1) dependency-order
    faithfulness and (R2) the seed boundary — both scoped to `a`'s own
    closure, not the whole `Node Payload` type. **Why scoped (round 4):**
    the ceiling itself is always a statement about one specific `a`
    (`Ceiling.ceiling` takes it as a parameter); `recordOf` is never
    consulted outside `depclosure a`. The unscoped version demanded a
    property the theorem never uses — `∀ m : Node Payload, m.seed? = true ↔
    m.id = 0` is REFUTABLE by `Node.ground 5 true`, a value no domain's
    builder ever constructs but the open `Node` type still contains, and no
    refinement of a builder's own signature changes what `Node.ground`/
    `Node.derived` — the type's OWN constructors — allow. Scoping to
    `depclosure a` weakens nothing the ceiling depends on and makes the
    obligation exactly the theorem a real builder's structure can prove
    (`Instance.Identity.identity_id_mono`). Bundled as a structure —
    function plus the properties it must satisfy — mirroring
    `EonEalm.Commitment`'s own shape; never constructed in the neutral core,
    always supplied by the instance whose record it is. -/
structure RecordRealization (Payload : Type) (a : Node Payload) where
  /-- The embedding itself — a total function; only its BEHAVIOR on
      `depclosure a` is constrained below. -/
  recordOf : Node Payload → Record
  /-- (R1) Dependency-order faithfulness, scoped to `a`'s closure: for every
      `n` in it, everything `n` depends on (within that same closure)
      records a genuine prefix of `n`'s own record. `m ∈ depclosure a` is
      not separately required — it follows from `n ∈ depclosure a` and
      `m ∈ depclosure n`, and no theorem here needs it stated twice. -/
  faithful : ∀ n ∈ depclosure a, ∀ m ∈ depclosure n, recordOf m ⊑ recordOf n
  /-- (R2) The seed boundary, scoped to `a`'s closure: a seed within it is
      exactly a node whose record commits no prior entries. -/
  seedBoundary : ∀ m ∈ depclosure a, m.seed? = true ↔ recordOf m = []

section RecordRealizationNonvacuity

/-! ## `countRealization` — the general construction, and the finding that forces it

**Finding, stated before the construction because the construction is a
direct consequence of it.** For ANY `Payload`, a `recordOf` whose value on a
`.derived` node genuinely varies with that node's OWN payload content (an
injective — or even just non-constant — `encode : Payload → Entry` folded
into a per-node entry) CANNOT satisfy (R1) once `Node Payload` admits a
`.derived` node with two or more non-seed inputs — which the type always
does, for any `Payload`, regardless of what any particular domain's own
builder functions happen to construct. Proof: let `n` have non-seed
siblings `c₁ ≠ c₂` among its inputs (e.g. two `.derived` leaves over
distinct payloads). (R1) forces `recordOf c₁ ⊑ recordOf n` and
`recordOf c₂ ⊑ recordOf n`; two prefixes of the SAME list are always
mutually comparable, so `recordOf c₁ ⊑ recordOf c₂ ∨ recordOf c₂ ⊑
recordOf c₁` is forced too. But `recordOf` is an ordinary structural
recursion on the NODE VALUE alone — `recordOf c₁` cannot depend on `c₂`
(its sibling) or on `n` (its parent), so this comparability must already
hold between `c₁` and `c₂` evaluated as STANDALONE values, with no shared
context to arrange it. Nothing about two independently-encoded, unrelated
payloads' entries guarantees that. The only escape is for `recordOf`'s
non-seed range to be intrinsically totally ordered regardless of content —
exactly what a LENGTH (count) does, and exactly what `encode` collapsing to
one entry does. `Instance.Identity`/`Instance.SuretyLite` never build such
siblings in practice (`chain` and every witness use single-input
`.derived` nodes only), so scoping `RecordRealization` to `depclosure a`
(round 4, below) does not rescue content-informative `encode` either — a
domain whose OWN closure genuinely branches would still hit this, scoped
or not; the neutral core cannot assume otherwise. This is the "obstruction,
named": `encode : Payload → Entry`, informative per payload, is not
constructible into a total `RecordRealization`; `countRealization` below
is the construction that actually exists, using one entry, not a
per-payload encoding. -/

/-- The post-order size: seeds contribute `0`; every other node contributes
    `1` plus its inputs' sizes (summed — a DAG-shared input is counted once
    per path to it, which only strengthens the monotonicity `faithful`
    below needs, never weakens it). -/
def recCount : Node Payload → Nat
  | .ground _ true => 0
  | .ground _ false => 1
  | .derived _ _ inputs => 1 + (inputs.attach.map (fun p => recCount p.1)).sum
termination_by m => sizeOf m
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem p.2
  omega

theorem recCount_eq_zero_iff_seed (m : Node Payload) : recCount m = 0 ↔ m.seed? = true := by
  cases m with
  | ground i s => cases s <;> simp [recCount, Node.seed?]
  | derived i p inputs => simp [recCount, Node.seed?]

/-- A single term of a `List Nat` sum is bounded by the sum — this
    Mathlib-free package proves the one fact `recCount_mono` needs directly
    rather than importing a general-purpose ordered-sum library. -/
theorem le_sum_of_mem {l : List Nat} {x : Nat} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.sum_cons]
      rcases hx with rfl | hx
      · omega
      · have := ih hx; omega

/-- **(R1)'s content, proved by the SAME well-founded recursion `recCount`
    itself uses**: a node's size never exceeds any ancestor's — the
    `List.replicate`-based `⊑` this licenses (`countRecordOf_faithful`
    below) is where it cashes out. -/
theorem recCount_mono (m : Node Payload) :
    ∀ n : Node Payload, m ∈ depclosure n → recCount m ≤ recCount n
  | .ground i s, hmem => by
      simp only [depclosure, List.mem_cons, List.not_mem_nil, or_false] at hmem
      subst hmem
      exact Nat.le_refl _
  | .derived i payload inputs, hmem => by
      simp only [depclosure, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Nat.le_refl _
      · simp only [List.mem_flatMap] at hmem
        obtain ⟨q, hq, hmq⟩ := hmem
        have h1 : recCount m ≤ recCount q.1 := recCount_mono m q.1 hmq
        have h2 : recCount q.1 ≤ (inputs.attach.map (fun p => recCount p.1)).sum :=
          le_sum_of_mem (List.mem_map_of_mem hq)
        simp only [recCount]
        omega
termination_by n => sizeOf n
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem q.2
  omega

/-- The realization itself: `recCount` entries of one given `e`. Parametric
    in a single `Entry` — `Core.Model.Entry` carries no inhabitedness
    axiom, so this (like every entry-parametric witness in the corpus,
    e.g. `Witness.Cells.inclusionClaim`) takes one as a hypothesis rather
    than manufacturing it. -/
def countRecordOf (e : Entry) (m : Node Payload) : Record := List.replicate (recCount m) e

theorem countRecordOf_seedBoundary (e : Entry) (m : Node Payload) :
    m.seed? = true ↔ countRecordOf e m = [] := by
  rw [← recCount_eq_zero_iff_seed, countRecordOf, List.replicate_eq_nil_iff]

theorem countRecordOf_faithful (e : Entry) :
    ∀ m n : Node Payload, m ∈ depclosure n → countRecordOf e m ⊑ countRecordOf e n := by
  intro m n hmem
  obtain ⟨k, hk⟩ := Nat.le.dest (recCount_mono m n hmem)
  refine ⟨List.replicate k e, ?_⟩
  show countRecordOf e n = countRecordOf e m ++ List.replicate k e
  simp only [countRecordOf, ← hk]
  induction recCount m with
  | zero => simp
  | succ j ih => rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, ih, List.cons_append]

/-- **Non-vacuity of `RecordRealization` itself**: R1 and R2 are jointly
    satisfiable, not merely individually statable, unconditionally — no
    hypothesis on `a` needed at all, since `countRecordOf_faithful`/
    `countRecordOf_seedBoundary` already hold for the FULL `Node Payload`
    type, a fortiori for any `depclosure a` restriction of it. -/
def countRealization (e : Entry) (a : Node Payload) : RecordRealization Payload a where
  recordOf := countRecordOf e
  faithful := fun n _ m hmem => countRecordOf_faithful e m n hmem
  seedBoundary := fun m _ => countRecordOf_seedBoundary e m

end RecordRealizationNonvacuity

section LogRealization

/-! ## `logRealization` — content-VARYING, but conditional, and here is exactly why

**The proposed fix, checked precisely.** "`recordOf m` is the log prefix up
to `m`'s position" reads two ways, and only one survives.

**Reading A (rejected) — `recordOf m` built from `m`'s OWN `depclosure`,
sorted by `id`.** Take `n` with non-seed siblings `c₁ (id 5) ≠ c₂ (id 7)`,
both leaves, `n.id = 10`. Even granting id-monotonicity (dependencies have
lower ids than dependents — `5, 7 < 10` here), `recordOf n` (built from
`n`'s full closure `{c₁, c₂, n}`, id-sorted) is `[encode c₁, encode c₂,
encode n]`. But `recordOf c₂` is built from `c₂`'s OWN closure, `{c₂}`
alone — `[encode c₂]`. `[encode c₂] ⊑ [encode c₁, encode c₂, …]` fails
(it does not even start with `encode c₂`) UNLESS `encode c₁ = encode c₂`,
collapsing content exactly as before. `recordOf`, computed via ordinary
structural recursion on `c₂` ALONE, has no way to know `c₁` exists — `c₁`
is `c₂`'s sibling, not `c₂`'s dependency, so nothing about id-monotonicity
(an ordering fact) puts `c₁`'s content INSIDE `c₂`'s own record. Same
obstruction, id-sorted dressing.

**Reading B (works) — `recordOf m` is a prefix of ONE AMBIENT,
externally-supplied log, indexed by `id`, not assembled from `m`'s own
subtree at all.** `logRecordOf globalLog m := (List.range m.id).map
globalLog` for a domain-supplied `globalLog : Nat → Entry`. Two siblings
under `n` are now both literal prefixes of the SAME `globalLog`-indexed
sequence, so they ARE comparable — proved below
(`logRecordOf_faithful`/`logRecordOf_seedBoundary`), unconditionally
GIVEN two named hypotheses. This is genuinely content-VARYING (unlike
`countRealization`, two different ids get different entries whenever
`globalLog` does).

**What Reading B costs, stated precisely, not smuggled — matching (R1)/
(R2) exactly, and NOW SCOPED to `depclosure a` (round 4) rather than the
whole type:**
- **(H1) id-monotonicity, on `a`'s closure**: `∀ n ∈ depclosure a,
  ∀ m ∈ depclosure n, m.id ≤ n.id`.
- **(H2) the seed boundary transported to `id`, on `a`'s closure**:
  `∀ m ∈ depclosure a, m.seed? = true ↔ m.id = 0`.

Scoping matters here specifically because the UNSCOPED forms are
REFUTABLE, not merely undischarged (`Node.ground 5 true` refutes unscoped
H2; `Node.derived 3 () [Node.ground 99 true]` refutes unscoped H1 — both
values `chain`/`LitePayload` never build but the open `Node` type still
contains). Scoped to `depclosure a`, both become theorems about a REAL
closure's own structure — `Instance.Identity.identity_id_mono`/
`identity_id_seedBoundary` discharge them for `a := chain evs`.

**What Reading B does NOT deliver, honestly**: `globalLog : Nat → Entry`
is indexed by POSITION, not by PAYLOAD — it is not literally `encode :
Payload → Entry` applied to `m`'s own content. Two DIFFERENT non-seed
nodes sharing an `id` (`Node`'s type does not forbid this) would collide
regardless of payload. Recovering genuine payload-faithfulness needs a
THIRD hypothesis (id-injectivity keyed to payload identity) that neither
instance discharges below — flagged, not silently dropped. -/

def logRecordOf (globalLog : Nat → Entry) (m : Node Payload) : Record :=
  (List.range m.id).map globalLog

theorem range_eq_nil_iff (a : Nat) : List.range a = [] ↔ a = 0 := by
  cases a <;> simp [List.range_succ]

theorem logRecordOf_faithful (globalLog : Nat → Entry) (a : Node Payload)
    (hMono : ∀ n ∈ depclosure a, ∀ m ∈ depclosure n, m.id ≤ n.id)
    (n : Node Payload) (hn : n ∈ depclosure a) (m : Node Payload) (hmem : m ∈ depclosure n) :
    logRecordOf globalLog m ⊑ logRecordOf globalLog n := by
  obtain ⟨k, hk⟩ := Nat.le.dest (hMono n hn m hmem)
  refine ⟨(List.range k).map (fun x => globalLog (m.id + x)), ?_⟩
  show logRecordOf globalLog n = logRecordOf globalLog m ++ (List.range k).map (fun x => globalLog (m.id + x))
  unfold logRecordOf
  rw [← hk, List.range_add, List.map_append, List.map_map]
  rfl

theorem logRecordOf_seedBoundary (globalLog : Nat → Entry) (a : Node Payload)
    (hSeedZero : ∀ m ∈ depclosure a, m.seed? = true ↔ m.id = 0)
    (m : Node Payload) (hm : m ∈ depclosure a) :
    m.seed? = true ↔ logRecordOf globalLog m = [] := by
  rw [hSeedZero m hm, ← range_eq_nil_iff]
  unfold logRecordOf
  exact List.map_eq_nil_iff.symm

/-- The conditional, content-varying construction — GIVEN (H1)/(H2) scoped
    to `a`'s own closure, a genuine `RecordRealization Payload a`, distinct
    from `countRealization`'s content-neutral one. -/
def logRealization (globalLog : Nat → Entry) (a : Node Payload)
    (hMono : ∀ n ∈ depclosure a, ∀ m ∈ depclosure n, m.id ≤ n.id)
    (hSeedZero : ∀ m ∈ depclosure a, m.seed? = true ↔ m.id = 0) : RecordRealization Payload a where
  recordOf := logRecordOf globalLog
  faithful := fun n hn m hmem => logRecordOf_faithful globalLog a hMono n hn m hmem
  seedBoundary := logRecordOf_seedBoundary globalLog a hSeedZero

end LogRealization

-- ===========================================================================
-- Discharges, round 2 — a genuine relation
-- ===========================================================================

/-- **`Discharges`**: `S : Scheme Γ φ_bind` discharges `m`'s establishment
    without admission — `S` is snapshot-sound for the domain's binding
    claim, AND `S`'s verifier accepts a certificate for `m`'s OWN record
    under the realization `ρ`. Both conjuncts are consumed together in
    `discharges_forces_binding` below — the test round 1 failed. `ρ.recordOf`
    is a total function, so `Discharges` itself needs no membership proof —
    only `ρ`'s TYPE names the `a` its properties are scoped to. -/
def Discharges {Comm : Type} {a : Node Payload} (Γ : Commitment Comm) (φ_bind : Claim)
    (ρ : RecordRealization Payload a) (S : Scheme Γ φ_bind) (m : Node Payload) : Prop :=
  SnapshotSound S ∧ ∃ c, S.V (Γ.C (ρ.recordOf m)) c

/-- **The joint-consumption witness.** `hsound` (from the FIRST conjunct) is
    a function `∀ w c, S.V (Γ.C w) c → ∀ ξ, φ_bind w ξ`; applying it to `c`
    and `hc` (from the SECOND conjunct, at `w := ρ.recordOf m` specifically
    — `m`'s own record under `ρ`, nothing else) is the one proof step that
    genuinely needs both halves of `Discharges` — the first half alone is a
    function with nothing to apply it to, the second alone is an
    unauthenticated acceptance with no guarantee it means anything. -/
theorem discharges_forces_binding {Comm : Type} {a : Node Payload} (Γ : Commitment Comm)
    (φ_bind : Claim) (ρ : RecordRealization Payload a) (S : Scheme Γ φ_bind) (m : Node Payload)
    (h : Discharges Γ φ_bind ρ S m) : ∀ ξ, φ_bind (ρ.recordOf m) ξ := by
  obtain ⟨hsound, c, hc⟩ := h
  exact hsound (ρ.recordOf m) c hc

/-- **The seed-specific content R2 buys.** For a seed IN `a`'s closure,
    `Discharges` reduces to "S certifies at the EMPTY record" — a fact
    genuinely different from discharging any other node (which would
    certify at that node's own, generally nonempty, record). Uses R2
    (`ρ.seedBoundary`, needing `hm : m ∈ depclosure a` now that it is
    scoped) to rewrite `ρ.recordOf m` to `[]` under the seed hypothesis —
    the accounting-side flag and the realization's own law combining to
    produce a scheme-world fact, not decoration. -/
theorem discharges_seed_iff_certifies_empty {Comm : Type} {a : Node Payload} (Γ : Commitment Comm)
    (φ_bind : Claim) (ρ : RecordRealization Payload a) (S : Scheme Γ φ_bind) (m : Node Payload)
    (hm : m ∈ depclosure a) (hseed : m.seed? = true) :
    Discharges Γ φ_bind ρ S m ↔ SnapshotSound S ∧ ∃ c, S.V (Γ.C []) c := by
  have hrec : ρ.recordOf m = [] := (ρ.seedBoundary m hm).mp hseed
  rw [Discharges, hrec]

-- ===========================================================================
-- L1 — gate ⇒ nothing is discharged
-- ===========================================================================

/-- **L1.** Under the domain's own `hfiber`, no scheme discharges `m` —
    genuinely `m`-independent: `Discharges` demands `SnapshotSound S`, and
    `hfiber`, via `binding_admits_no_scheme`, rules out every
    `SnapshotSound` scheme for `φ_bind` outright, regardless of which record
    it would have certified. This is exactly the half of `Discharges` that
    does NOT need `ρ` — the half that does is
    `discharges_forces_binding`/`discharges_seed_iff_certifies_empty`. -/
theorem no_seed_discharged {Comm : Type} {a : Node Payload} (Γ : Commitment Comm)
    (φ_bind : Claim) (hfiber : ¬ Determined φ_bind) (ρ : RecordRealization Payload a)
    (S : Scheme Γ φ_bind) (m : Node Payload) :
    ¬ Discharges Γ φ_bind ρ S m :=
  fun h => binding_admits_no_scheme φ_bind hfiber Γ ⟨S, h.1⟩

-- ===========================================================================
-- Discharges — non-vacuity (positively inhabited, for any realization)
-- ===========================================================================

section DischargesNonvacuity

/-- The trivial binding claim: holds everywhere, at every record AND every
    context — genuinely context-free by inspection, not merely `Determined`
    (a weaker, context-INDEPENDENT-VALUE fact) in the sense the general
    machinery below would need. Used only to witness that `Discharges` is
    genuinely SATISFIABLE in general (contrast `ceiling_nonvacuous` below,
    where `hfiber` makes it never hold). -/
def trivialClaim : Claim := fun _ _ => True

/-- **Hand-built, not routed through `snapshot_characterization_backward`.**
    That general machinery goes through `Core.Axes.determinedProj`, which is
    `noncomputable` and picks a canonical `Context` witness from
    `EonEalm.Context.inhabited`'s bare `Nonempty` — i.e. `Classical.choice`,
    unconditionally, for ANY claim routed through it. `trivialClaim` never
    needs to inspect `ξ` at all, so the always-accepting verifier below is
    `SnapshotSound` by a one-line `trivial`, with no canonical-witness
    machinery and no `Classical.choice` anywhere in reach — this is exactly
    the difference between "a scheme exists because SOME claim is
    `Determined`" (needs choice to name a representative world) and "THIS
    claim needs no representative at all." -/
def trivialScheme {Comm : Type} (Γ : Commitment Comm) : Scheme Γ trivialClaim where
  Proof := Unit
  V := fun _ _ => True
  completeness := fun _ _ _ => ⟨(), trivial⟩

theorem trivialScheme_snapshotSound {Comm : Type} (Γ : Commitment Comm) :
    SnapshotSound (trivialScheme Γ) :=
  fun _ _ _ _ => trivial

theorem trivialClaim_scheme_exists {Comm : Type} (Γ : Commitment Comm) :
    ∃ S : Scheme Γ trivialClaim, SnapshotSound S :=
  ⟨trivialScheme Γ, trivialScheme_snapshotSound Γ⟩

/-- `Discharges` is inhabited FOR ANY node `m` and ANY realization `ρ` — not
    just seeds: `trivialClaim`'s scheme accepts a certificate at every
    record (its completeness is unconditional), so applying `S.completeness`
    AT `ρ.recordOf m` specifically produces the second conjunct. This is the
    design's falsification signpost — were `Discharges` identically `False`
    (or the two conjuncts unreachable together), neither L1 nor this witness
    would say anything. **`ξ` is an explicit parameter, not `default`**: the
    conclusion never mentions `ξ` (`Discharges` has none), so manufacturing
    one internally would only be for `S.completeness`'s sake — and manufacturing
    a `Context` value from the bare `Nonempty` `Context.inhabited` needs
    `Classical.choice`. Taking `ξ` from the caller keeps this theorem, and
    everything in `Ceiling/` that depends on it, in that choice's absence. -/
theorem discharges_nonvacuous {Comm : Type} {a : Node Payload} (Γ : Commitment Comm)
    (ρ : RecordRealization Payload a) (m : Node Payload) (ξ : Context) :
    ∃ S : Scheme Γ trivialClaim, Discharges Γ trivialClaim ρ S m := by
  obtain ⟨S, hS⟩ := trivialClaim_scheme_exists Γ
  obtain ⟨c, hc⟩ := S.completeness (ρ.recordOf m) ξ trivial
  exact ⟨S, hS, c, hc⟩

end DischargesNonvacuity

-- ===========================================================================
-- L2 — surface lower bound, genuinely joint
-- ===========================================================================

variable {Tag Signer : Type} [DecidableEq Tag]

/-- **L2 — the quantified-over-schemes claim §1.6(iii) asserts.** For EVERY
    scheme `S : Scheme Γ φ_bind`, every seed `m` in `a`'s closure is
    simultaneously (a) undischargeable by `S` (L1, the scheme-world side)
    and (b) forced into `a`'s trust surface regardless (`seeds_always_
    residual`, the accounting-world side) — the SAME `m`, in the SAME
    theorem, under the SAME hypothesis. Honest about (a): its own proof does
    not need `ρ` (L1 is `m`-independent, see `no_seed_discharged`'s
    docstring) — `ρ` enters L2 only to give `Discharges` a well-typed
    statement to negate. The genuine node/scheme interaction lives in
    `discharges_forces_binding`, not here; what IS new here is `φ_bind` and
    `a` co-occurring in one theorem's conclusion for the first time. -/
theorem seeds_undischargeable_and_residual {Comm : Type} (Γ : Commitment Comm)
    (φ_bind : Claim) (hfiber : ¬ Determined φ_bind) (a : Node Payload)
    (ρ : RecordRealization Payload a)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) :
    ∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind ρ S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a :=
  fun S m hmem hseed =>
    ⟨no_seed_discharged Γ φ_bind hfiber ρ S m,
     seeds_always_residual gate tagOf closureOk P σ a m hmem hseed⟩

-- ===========================================================================
-- L3 — ceiling: minimality attained, not merely bounded
-- ===========================================================================

/-- **L3.** Under `Total a`, the trust surface is EXACTLY the seed members of
    the closure — not merely bounded below by them (`seeds_always_residual`
    gives that unconditionally) but equal, the "minimality attained" reading
    of §1.6(iii)/`.ledger/trichotomy/STATEMENT-rc-v0.7.md` item 4. Promotes
    `total_iff_every_nonseed_closed` (`Ceiling/Accounting.lean:72`, today
    accounting-internal) to the companion theorem's own vocabulary
    (`trustSurface`/seed-filter over `depclosure`). -/
theorem ceiling_minimality (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) (σ : Snapshot Signer Tag)
    (a : Node Payload) :
    Total gate tagOf closureOk P σ a ↔
      trustSurface gate tagOf closureOk P σ a = (depclosure a).filter (fun m => m.seed?) := by
  constructor
  · intro hTotal
    have hnonseed := (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mp hTotal
    show (depclosure a).filter (fun m => !decide (classify gate tagOf closureOk P σ m = .closed)) =
        (depclosure a).filter (fun m => m.seed?)
    apply List.filter_congr
    intro m hmem
    by_cases hseed : m.seed? = true
    · simp [hseed, seeds_are_imports gate tagOf closureOk P σ m hseed]
    · have hnotseed : m.seed? = false := by simpa using hseed
      simp [hnotseed, hnonseed m hmem hnotseed]
  · intro heq
    apply (total_iff_every_nonseed_closed gate tagOf closureOk P σ a).mpr
    intro m hmem hnotseed
    by_cases hnc : classify gate tagOf closureOk P σ m = .closed
    · exact hnc
    · exfalso
      have hmemSurface : m ∈ trustSurface gate tagOf closureOk P σ a := by
        simp only [trustSurface, List.mem_filter]
        exact ⟨hmem, by simp [hnc]⟩
      rw [heq] at hmemSurface
      simp only [List.mem_filter] at hmemSurface
      rw [hmemSurface.2] at hnotseed
      exact absurd hnotseed (by simp)

-- ===========================================================================
-- Growth alignment (item 5) — resolved in two halves
-- ===========================================================================

/-- Evidence-snapshot extension: `σ` grows into `σ'` when every entry of `σ`
    is also present in `σ'` — a SET-growth order (evidence accumulates; a
    later corroboration or vouch never displaces one already admitted), not
    the record-world's sequential PREFIX order `⊑`. Stated as a plain
    quantifier, not `List.Subset`/`⊆`, so this file adds no dependency on
    which `List` API surface happens to carry that notation. -/
def SnapshotExt (σ σ' : Snapshot Signer Tag) : Prop := ∀ e ∈ σ, e ∈ σ'

omit [DecidableEq Tag] in
theorem corroborated_mono_snapshot {σ σ' : Snapshot Signer Tag} (hext : SnapshotExt σ σ')
    (P : Policy Signer) (m : Node Payload) (h : corroborated P σ m = true) :
    corroborated P σ' m = true := by
  simp only [corroborated, List.any_eq_true] at h ⊢
  obtain ⟨e, he, hmatch⟩ := h
  exact ⟨e, hext e he, hmatch⟩

theorem established_mono_snapshot {σ σ' : Snapshot Signer Tag} (hext : SnapshotExt σ σ')
    (gate : Payload → Bool) (tagOf : Payload → Tag) (P : Policy Signer)
    (id : Nat) (payload : Payload) (h : established gate tagOf P σ id payload = true) :
    established gate tagOf P σ' id payload = true := by
  simp only [established, Bool.and_eq_true_iff, List.any_eq_true] at h ⊢
  obtain ⟨hgate, e, he, hmatch⟩ := h
  exact ⟨hgate, e, hext e he, hmatch⟩

/-- **Growth alignment, accounting-internal half — aligns for free.**
    `classify`'s admission predicates only ever test "does σ contain a
    matching admitted entry," never its absence, so growing σ can only turn
    `.closed` into `.closed` again, never undo it — proved by the SAME
    well-founded recursion `classify` itself uses. -/
theorem classify_closed_mono_snapshot (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) :
    ∀ {σ σ' : Snapshot Signer Tag}, SnapshotExt σ σ' → ∀ m : Node Payload,
      classify gate tagOf closureOk P σ m = .closed →
      classify gate tagOf closureOk P σ' m = .closed
  | σ, σ', _, .ground i _, h => by simp [classify] at h
  | σ, σ', hext, .derived i payload inputs, h => by
      have hpieces :
          established gate tagOf P σ i payload = true ∧
          closureOk payload = true ∧
          corroborated P σ (Node.derived i payload inputs) = true ∧
          (inputs.attach.all fun p =>
            p.1.seed? || decide (classify gate tagOf closureOk P σ p.1 = .closed)) = true := by
        simp only [classify] at h
        by_cases he : established gate tagOf P σ i payload = true
        · simp only [he, Bool.not_true, if_neg (by simp : ¬ ((false : Bool) = true))] at h
          by_cases hc :
              (closureOk payload && corroborated P σ (Node.derived i payload inputs) &&
                inputs.attach.all fun p =>
                  p.1.seed? || decide (classify gate tagOf closureOk P σ p.1 = .closed)) = true
          · simp only [Bool.and_eq_true_iff] at hc
            exact ⟨he, hc.1.1, hc.1.2, hc.2⟩
          · simp [hc] at h
        · simp [he] at h
      obtain ⟨hest, hco, hcorr, hrec⟩ := hpieces
      have hest' := established_mono_snapshot hext gate tagOf P i payload hest
      have hcorr' := corroborated_mono_snapshot hext P (Node.derived i payload inputs) hcorr
      have hrec' :
          (inputs.attach.all fun p =>
            p.1.seed? || decide (classify gate tagOf closureOk P σ' p.1 = .closed)) = true := by
        rw [List.all_eq_true] at hrec ⊢
        intro x hx
        have hx' := hrec x hx
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hx' ⊢
        rcases hx' with hseed | hc2
        · exact Or.inl hseed
        · exact Or.inr (classify_closed_mono_snapshot gate tagOf closureOk P hext x.1 hc2)
      show classify gate tagOf closureOk P σ' (Node.derived i payload inputs) = .closed
      simp [classify, hest', hco, hcorr', hrec']
termination_by σ σ' _hext m _h => sizeOf m
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem x.2
  omega

/-- The `Total` corollary: totality, once achieved, survives every further
    extension of the evidence snapshot. -/
theorem total_mono_snapshot (gate : Payload → Bool) (tagOf : Payload → Tag)
    (closureOk : Payload → Bool) (P : Policy Signer) {σ σ' : Snapshot Signer Tag}
    (hext : SnapshotExt σ σ') (a : Node Payload) (hTotal : Total gate tagOf closureOk P σ a) :
    Total gate tagOf closureOk P σ' a := by
  rw [total_iff_every_nonseed_closed] at hTotal ⊢
  intro m hmem hnotseed
  exact classify_closed_mono_snapshot gate tagOf closureOk P hext m (hTotal m hmem hnotseed)

/-! **Growth alignment, cross-domain half — resolved by `RecordRealization`
above.** "Record extension `⊑`" is an order on `EonEalm.Record`;
`SnapshotExt` above is an order on `Ceiling.Snapshot Signer Tag` — the two
stay genuinely disjoint (this section's `SnapshotExt` facts are unconditional
and never need a realization at all). `RecordRealization`'s own (R1) IS the
growth-alignment hypothesis, scoped to `a`'s closure — `ρ.faithful` is
literally "`depclosure`-membership within `a`'s own closure transports to
`⊑`." `growth_alignment` below is the `Monotone` consequence of R1, stated
directly in `depclosure`'s own vocabulary rather than a bare `⊑` hypothesis. -/

/-- **Growth alignment.** Given a realization `ρ` for `a` and `φ_bind`
    `Monotone`: `φ_bind` holding at `m`'s record transports to any `n` in
    `a`'s closure with `m` in its dependency closure — accounting-world
    growth (`depclosure` membership) forces scheme-world growth (`⊑`) via
    (R1), and `Monotone` does the rest. -/
theorem growth_alignment {Payload : Type} {a : Node Payload} (φ_bind : Claim)
    (hmono : Monotone φ_bind) (ρ : RecordRealization Payload a)
    (n : Node Payload) (hn : n ∈ depclosure a) (m : Node Payload) (hmem : m ∈ depclosure n)
    (ξ : Context) (h : φ_bind (ρ.recordOf m) ξ) :
    φ_bind (ρ.recordOf n) ξ :=
  hmono (ρ.recordOf m) (ρ.recordOf n) ξ h (ρ.faithful n hn m hmem)

-- ===========================================================================
-- `ceiling`, restated — φ_bind and a genuinely linked
-- ===========================================================================

/-- **`ceiling`, superseding `Ceiling.Gate.ceiling`.** The companion display:
    the gate (i); the quantified-over-schemes seed junction (L2); the
    ceiling's minimality equality (L3); and completeness (ii,
    `total_carries_both_species` — per-member: each non-seed closure member
    is `derived`, and both counted items name that member's own `id`, the
    vouch its own `tagOf` payload besides). `ρ` is threaded through
    for `Discharges` to be well-typed — supplied by the caller (an instance)
    or, absent one, taken as an explicit hypothesis exactly like `hfiber`. -/
theorem ceiling {Comm : Type} (Γ : Commitment Comm) (φ_bind : Claim)
    (hfiber : ¬ Determined φ_bind) (a : Node Payload) (ρ : RecordRealization Payload a)
    (gate : Payload → Bool) (tagOf : Payload → Tag) (closureOk : Payload → Bool)
    (P : Policy Signer) (σ : Snapshot Signer Tag) :
    (¬ ∃ S : Scheme Γ φ_bind, SnapshotSound S) ∧
    (∀ S : Scheme Γ φ_bind, ∀ m ∈ depclosure a, m.seed? = true →
      ¬ Discharges Γ φ_bind ρ S m ∧ m ∈ trustSurface gate tagOf closureOk P σ a) ∧
    (Total gate tagOf closureOk P σ a →
      trustSurface gate tagOf closureOk P σ a = (depclosure a).filter (fun m => m.seed?)) ∧
    (Total gate tagOf closureOk P σ a →
      ∀ m ∈ depclosure a, m.seed? = false →
        ∃ i payload inputs, m = .derived i payload inputs ∧
          (∃ s, Evidence.corroboration (Tag := Tag) s i ∈ basis gate tagOf closureOk P σ a) ∧
          (∃ s, Evidence.vouch s i (tagOf payload) ∈ basis gate tagOf closureOk P σ a)) :=
  ⟨binding_admits_no_scheme φ_bind hfiber Γ,
   seeds_undischargeable_and_residual Γ φ_bind hfiber a ρ gate tagOf closureOk P σ,
   fun hTotal => (ceiling_minimality gate tagOf closureOk P σ a).mp hTotal,
   fun hTotal m hmem hnotSeed =>
     total_carries_both_species gate tagOf closureOk P σ a hTotal m hmem hnotSeed⟩

-- ===========================================================================
-- Non-vacuity for the junction itself
-- ===========================================================================

section Nonvacuity

/-- The witness closure: a single derived node closing directly onto the
    genesis seed — the neutral core's own instance of the `SuretyLite`/
    `Identity` W2 shape, reused here so the junction's non-vacuity does not
    depend on either instance package. -/
def wNode : Node Unit := .derived 1 () [Node.ground 0 true]

def wPolicy : Policy Unit := ⟨fun _ => true, fun _ => true⟩
def wSnap : Snapshot Unit Unit := [.vouch () 1 (), .corroboration () 1]
def wGate : Unit → Bool := fun _ => true
def wTagOf : Unit → Unit := fun _ => ()
def wClosureOk : Unit → Bool := fun _ => true

theorem wNode_total : Total wGate wTagOf wClosureOk wPolicy wSnap wNode := by
  apply (total_iff_every_nonseed_closed wGate wTagOf wClosureOk wPolicy wSnap wNode).mpr
  intro m hmem hnotseed
  have hlist : depclosure wNode = [Node.derived 1 () [Node.ground 0 true], Node.ground 0 true] := by
    show depclosure (Node.derived 1 () [Node.ground 0 true]) = _
    rw [depclosure]; simp [depclosure]
  rw [hlist] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · simp [Ceiling.classify, established, corroborated, wGate, wTagOf, wClosureOk,
      wPolicy, wSnap, Node.id, Node.seed?]
  · simp [Node.seed?] at hnotseed

/-- **Non-vacuity for `ceiling` itself**, in the corpus's own style
    (`comp_COMP_nonvacuous`, `Effective/Trichotomy.lean:410`; the axios
    `SuretyCeiling/Nonvacuity.lean` pattern): a genuinely undetermined
    `φ_bind` — `Core.Axes.exists_undetermined_claim`'s witness, reused
    rather than re-extracted, so this file adds no new consumption site for
    `Context.nontrivial` (`Core.lean`'s three-site accounting stays
    accurate) — over a genuine `Total` closure (`wNode_total`) and a genuine
    `RecordRealization` (`countRealization e`, parametric in one `Entry`),
    with every conjunct of the restated `ceiling` firing on real data. -/
theorem ceiling_nonvacuous (e : Entry) :
    ∃ (φ_bind : Claim), ¬ Determined φ_bind ∧
      (¬ ∃ S : Scheme idCommitment φ_bind, SnapshotSound S) ∧
      (∀ S : Scheme idCommitment φ_bind, ∀ m ∈ depclosure wNode, m.seed? = true →
        ¬ Discharges idCommitment φ_bind (countRealization e wNode) S m ∧
          m ∈ trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode) ∧
      trustSurface wGate wTagOf wClosureOk wPolicy wSnap wNode =
        (depclosure wNode).filter (fun m => m.seed?) := by
  obtain ⟨φ_bind, hnd⟩ := exists_undetermined_claim
  exact ⟨φ_bind, hnd, binding_admits_no_scheme φ_bind hnd idCommitment,
    seeds_undischargeable_and_residual idCommitment φ_bind hnd wNode (countRealization e wNode)
      wGate wTagOf wClosureOk wPolicy wSnap,
    (ceiling_minimality wGate wTagOf wClosureOk wPolicy wSnap wNode).mp wNode_total⟩

end Nonvacuity

end Ceiling

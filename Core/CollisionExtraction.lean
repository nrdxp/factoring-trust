import Core.Commitment

/-!
# Collision extraction — the effective-stratum soundness pattern

The general `accepts → φ ∨ ∃ collision` shape: replay the snapshot verifier against an
**arbitrary** commitment function `Cw` — not assumed binding — and show acceptance
forces either a genuine witness at exactly the claimed record, or a `Cw`-collision.
This is the pattern a concrete effective-stratum instantiation discharges instead of
assuming an unconditional binding axiom the way `Core.Commitment`'s idealized
`Commitment.binding` does.

Two strata live here and must not be conflated.

*Above* the reduction sits `Commitment`, which is provably incompressible
(`Core.Commitment.no_commitment_over_bool`): its `binding` field **is** `NoCollision`
on the nose, so `collisionCommitment` below discharges that field from a
collision-resistance hypothesis rather than assuming it — an honest routing, but one
that buys no compression, because no routing can. A hash is not a `Commitment` and
cannot be made one.

*At* the reduction, nothing is assumed: `collision_extraction_reduction` and
`preimageVC_soundness_up_to_collision` quantify over an arbitrary `Cw`, so a genuinely
compressing digest is expressible there, and the collision disjunct is exactly the
price it pays. `parityDigest` at the end of this file is such a digest, and the
reduction run against it lands in the collision branch on a real forgery. That is the
whole difference between the two strata, mechanized.
-/

namespace EonEalm

/-- `Cw` has no collision: it is genuinely injective. The hypothesis a concrete
    effective-stratum construction discharges instead of assuming outright. -/
def NoCollision {Comm : Type} (Cw : Record → Comm) : Prop := ∀ w w', Cw w = Cw w' → w = w'

/-- The collision-extraction reduction: replaying the snapshot `(w, t)` witness/checker
    verifier against an arbitrary (not-assumed-binding) `Cw`, an accepting `(w', t)`
    against target `target` either exhibits a genuine oracle witness for `target`
    itself (`w' = target`) or a `Cw`-collision between `w'` and `target`. No
    cryptographic hypothesis is needed for *this* general shape; `NoCollision` only
    becomes load-bearing once this is composed with a scheme's soundness obligation. -/
theorem collision_extraction_reduction {Comm : Type} (Cw : Record → Comm)
    (Witness : Type) (Chk : Record → Witness → Prop) (φ' : Record → Prop)
    (hφ' : ∀ w, φ' w ↔ ∃ t, Chk w t) (target : Record) (c : Record × Witness)
    (hacc : Cw c.1 = Cw target ∧ Chk c.1 c.2) :
    φ' target ∨ (c.1 ≠ target ∧ Cw c.1 = Cw target) := by
  obtain ⟨heq, hchk⟩ := hacc
  by_cases hc : c.1 = target
  · left
    rw [hφ']
    exact ⟨c.2, hc ▸ hchk⟩
  · right
    exact ⟨hc, heq⟩

/-- Under `NoCollision Cw`, the reduction's right disjunct is impossible, so
    acceptance forces the genuine witness — "no forgery without a collision." -/
theorem collision_extraction_reduction_of_noCollision {Comm : Type} (Cw : Record → Comm)
    (Witness : Type) (Chk : Record → Witness → Prop) (φ' : Record → Prop)
    (hφ' : ∀ w, φ' w ↔ ∃ t, Chk w t) (hnc : NoCollision Cw) (target : Record)
    (c : Record × Witness) (hacc : Cw c.1 = Cw target ∧ Chk c.1 c.2) : φ' target := by
  rcases collision_extraction_reduction Cw Witness Chk φ' hφ' target c hacc with h | ⟨hne, heq⟩
  · exact h
  · exact absurd (hnc c.1 target heq) hne

/-! ## The extension relation, reduced

`Commitment.VC`'s soundness obligation has the same shape as the snapshot verifier's,
one order up: an accepting extension certificate must force the genuine prefix
relation. A certificate carrying the records it claims as preimages is checkable
against an arbitrary `Cw`, and the same case split extracts a collision when the
claim is a forgery. A Merkle extension path is this certificate with the preimages
compressed away; carrying them keeps the extraction visible instead of burying it in
a hash-tree argument the record model cannot see. -/

/-- The preimage-carrying extension certificate: `π = (v₀, v)` claims `v₀` and `v` as
    preimages of the two commitments, and `v₀ ⊑ v`. -/
def preimageVC {Comm : Type} (Cw : Record → Comm) :
    Comm → Comm → Record × Record → Prop :=
  fun h₀ h π => Cw π.1 = h₀ ∧ Cw π.2 = h ∧ π.1 ⊑ π.2

/-- Completeness of `preimageVC` for any `Cw`: a genuine extension certifies itself. -/
theorem preimageVC_completeness {Comm : Type} (Cw : Record → Comm) (w₀ w : Record)
    (hext : w₀ ⊑ w) : ∃ π, preimageVC Cw (Cw w₀) (Cw w) π :=
  ⟨(w₀, w), rfl, rfl, hext⟩

/-- Extension soundness up to a collision, for an **arbitrary** `Cw` — no
    cryptographic hypothesis. Either the certified extension is genuine, or one of
    the certificate's two carried preimages collides with the record it is claimed to
    commit to. The collision is read off the certificate, not merely asserted to
    exist somewhere: this is an extractor, not an existence claim. -/
theorem preimageVC_soundness_up_to_collision {Comm : Type} (Cw : Record → Comm)
    (w₀ w : Record) (π : Record × Record) (hvc : preimageVC Cw (Cw w₀) (Cw w) π) :
    w₀ ⊑ w ∨ (π.1 ≠ w₀ ∧ Cw π.1 = Cw w₀) ∨ (π.2 ≠ w ∧ Cw π.2 = Cw w) := by
  obtain ⟨h₀, h, hext⟩ := hvc
  by_cases hv₀ : π.1 = w₀
  · by_cases hv : π.2 = w
    · exact Or.inl (by rw [← hv₀, ← hv]; exact hext)
    · exact Or.inr (Or.inr ⟨hv, h⟩)
  · exact Or.inr (Or.inl ⟨hv₀, h₀⟩)

/-- The commitment the reduction buys: every obligation `Commitment` imposes is
    *derived* from the single hypothesis `hnc`, none assumed of `Cw` separately.
    `VC`-soundness is the extraction above with its collision disjunct closed by
    `hnc`. The existing witnesses discharge that obligation by letting `VC` *be* the
    extension relation, so no verification happens and nothing about `C` is used;
    here it is discharged from a stated property of `C`, which is what an
    effective-stratum instance has to do.

    `binding` is the honest exception: `NoCollision Cw` is that field's type on the
    nose, so routing it through `hnc` renames the hypothesis without weakening it.
    That is not a defect of this construction but the shape of the obstruction —
    `Commitment` is incompressible by `Core.Commitment.no_commitment_over_bool`, so
    *no* constructor can hand back a compressing one, and the reduction's real reach
    is the hypothesis-free statements above, which never mention `Commitment`. -/
def collisionCommitment {Comm : Type} (Cw : Record → Comm) (hnc : NoCollision Cw) :
    Commitment Comm where
  VCProof := Record × Record
  C := Cw
  VC := preimageVC Cw
  binding := hnc
  soundness := fun w₀ w _h₀ _h π hvc h₀eq heq => by
    subst h₀eq; subst heq
    rcases preimageVC_soundness_up_to_collision Cw w₀ w π hvc with
      hx | ⟨hne, hc⟩ | ⟨hne, hc⟩
    · exact hx
    · exact absurd (hnc _ _ hc) hne
    · exact absurd (hnc _ _ hc) hne
  completeness := preimageVC_completeness Cw

/-- Non-vacuity for `collisionCommitment`, and a commitment whose `C` is not `id`:
    `Option.some` is injective into a codomain that is not `Record`, so distinctness
    from `idCommitment` is by type rather than by an entry-alphabet assumption the
    model does not license. It is an *expanding* commitment — which is as far as any
    `Commitment` can move from `id`, incompressibility being a theorem. -/
def optionCommitment : Commitment (Option Record) :=
  collisionCommitment Option.some (fun _ _ h => Option.some.inj h)

/-! ## A compressing commitment function

`Commitment` cannot host one; the reduction never needed it to. A one-bit digest is
the extreme case — it retains nothing but a record's length parity — and every
statement above applies to it verbatim, reporting exactly how weak it is: its
`NoCollision` hypothesis is outright false, and the reduction's collision branch is
reachable by an explicit forgery. A real hash sits between this and `id`, and the
model now has somewhere to put it. -/

/-- A one-bit digest: the parity of a record's length. Genuinely compressing — the
    domain is all of `Record`, the codomain is `Bool`. -/
def parityDigest : Record → Bool := fun w => decide (w.length % 2 = 0)

/-- What `NoCollision` actually forbids, stated on the verifier rather than on the
    digest: no accepting certificate can name a claim that is false at the target it
    is checked against. This is the reduction's contrapositive and the discriminating
    property below — an injective `Cw` admits no false acceptance at all. -/
theorem no_false_acceptance_of_noCollision {Comm : Type} (Cw : Record → Comm)
    (Witness : Type) (Chk : Record → Witness → Prop) (φ' : Record → Prop)
    (hφ' : ∀ w, φ' w ↔ ∃ t, Chk w t) (hnc : NoCollision Cw) (target : Record)
    (c : Record × Witness) : ¬ ((Cw c.1 = Cw target ∧ Chk c.1 c.2) ∧ ¬ φ' target) :=
  fun ⟨hacc, hnφ⟩ =>
    hnφ (collision_extraction_reduction_of_noCollision Cw Witness Chk φ' hφ' hnc target c hacc)

/-- Compression admits a false acceptance. Take the claim "the record is empty",
    certified by the record itself: the certificate naming `[]` is accepted against
    the target `[e, e]`, because a one-bit digest cannot tell them apart, and the
    claim is false at that target. Nothing here is a statement about `parityDigest`'s
    collisions — it is a statement about what a verifier built over it accepts. -/
theorem parityDigest_false_acceptance (e : Entry) :
    ((parityDigest ([] : Record) = parityDigest [e, e] ∧ ([] : Record) = []) ∧
      ¬ (([e, e] : Record) = [])) :=
  ⟨⟨by simp [parityDigest], rfl⟩, by simp⟩

/-- So `parityDigest` satisfies no binding axiom, and the proof runs the reduction
    rather than exhibiting a collision by hand: a digest whose verifier accepts a
    false claim cannot be collision-free, because `no_false_acceptance_of_noCollision`
    says collision-free digests have no false acceptances. That is the cryptographic
    argument in its usual direction — from a broken scheme to a broken hash — and it
    is what wires the reduction to a concrete compressing commitment.

    Combined with `Core.Commitment.no_commitment_over_bool`, this is the boundary in
    full: `parityDigest` is expressible as a commitment *function* and reasoned about
    soundly, and is provably not a `Commitment`. -/
theorem parityDigest_not_noCollision (e : Entry) : ¬ NoCollision parityDigest :=
  fun hnc =>
    no_false_acceptance_of_noCollision parityDigest Unit (fun w _ => w = [])
      (fun w => w = []) (fun _ => ⟨fun hw => ⟨(), hw⟩, fun ⟨_, hw⟩ => hw⟩) hnc
      [e, e] ([], ()) (parityDigest_false_acceptance e)

end EonEalm

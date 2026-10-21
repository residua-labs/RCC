import Init

/-!
# RCC CM-1 typed claim modalities

Claims and evidence do not share one untyped payload plus a caller-supplied
string tag.  Their modality is an index of the Lean type itself.  The six
constructors frozen by CM-1 are:

* deductive;
* computational;
* probabilistic;
* statistical;
* empirical-window; and
* assumption-relative.

The trusted core accepts an untrusted claim/evidence pair only after
`alignEvidence` reconstructs a same-index `ClaimEvidencePacket`.  A
computational run cannot therefore inhabit deductive evidence, and a finite
empirical window cannot inhabit an unconditional deductive certificate.

Alignment establishes only modality compatibility.  Semantic acceptance is a
separate, modality-indexed verifier relation.  This file deliberately does not
claim that a well-typed payload proves its claim, nor does it silently provide
any evidence-upgrade rule.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.ClaimModality

/-- The complete CM-1 claim-modality vocabulary. -/
inductive Modality
  | deductive
  | computational
  | probabilistic
  | statistical
  | empiricalWindow
  | assumptionRelative
  deriving DecidableEq, Repr

/--
Claim syntax indexed by its modality.

The fields are proof coordinates rather than free-form modality tags.  In
particular, no constructor accepts a `String` and then decides which modality
that string means.
-/
inductive Claim : Modality → Type
  | deductive
      (claimQ propositionQ kernelQ : String) :
      Claim .deductive
  | computational
      (claimQ programQ inputQ outputPredicateQ : String) :
      Claim .computational
  | probabilistic
      (claimQ experimentQ adversaryClassQ : String)
      (securityParameter boundNumerator boundDenominator : Nat) :
      Claim .probabilistic
  | statistical
      (claimQ estimatorQ populationQ sampleFrameQ : String)
      (sampleSize confidenceNumerator confidenceDenominator : Nat) :
      Claim .statistical
  | empiricalWindow
      (claimQ windowQ universeQ observationPredicateQ : String) :
      Claim .empiricalWindow
  | assumptionRelative
      (claimQ propositionQ assumptionRootQ derivationSystemQ : String) :
      Claim .assumptionRelative

/--
Evidence syntax indexed by the same modality family as `Claim`.

The constructors intentionally retain the evidence kind: a finite execution
receipt is computational evidence, while a sealed finite observation window
is empirical evidence.  Neither can be constructed at the deductive index.
-/
inductive Evidence : Modality → Type
  | deductive
      (theoremQ kernelQ certificateQ : String) :
      Evidence .deductive
  | computational
      (programQ inputQ outputQ implementationQ runReceiptQ : String) :
      Evidence .computational
  | probabilistic
      (experimentQ adversaryClassQ proofQ : String)
      (securityParameter boundNumerator boundDenominator : Nat) :
      Evidence .probabilistic
  | statistical
      (sampleFrameQ estimatorQ reportQ : String)
      (sampleSize confidenceNumerator confidenceDenominator : Nat) :
      Evidence .statistical
  | empiricalWindow
      (windowQ universeQ coverageQ observationsQ : String) :
      Evidence .empiricalWindow
  | assumptionRelative
      (assumptionRootQ dependencySetQ derivationQ : String) :
      Evidence .assumptionRelative

/-- Existential claim boundary used for untrusted or serialized inputs. -/
inductive ClaimEnvelope
  | deductive (claim : Claim .deductive)
  | computational (claim : Claim .computational)
  | probabilistic (claim : Claim .probabilistic)
  | statistical (claim : Claim .statistical)
  | empiricalWindow (claim : Claim .empiricalWindow)
  | assumptionRelative (claim : Claim .assumptionRelative)

/-- Existential evidence boundary used for untrusted or serialized inputs. -/
inductive EvidenceEnvelope
  | deductive (evidence : Evidence .deductive)
  | computational (evidence : Evidence .computational)
  | probabilistic (evidence : Evidence .probabilistic)
  | statistical (evidence : Evidence .statistical)
  | empiricalWindow (evidence : Evidence .empiricalWindow)
  | assumptionRelative (evidence : Evidence .assumptionRelative)

/-- Erase a claim envelope only to its type-derived modality. -/
def ClaimEnvelope.modality : ClaimEnvelope → Modality
  | .deductive _ => .deductive
  | .computational _ => .computational
  | .probabilistic _ => .probabilistic
  | .statistical _ => .statistical
  | .empiricalWindow _ => .empiricalWindow
  | .assumptionRelative _ => .assumptionRelative

/-- Erase an evidence envelope only to its type-derived modality. -/
def EvidenceEnvelope.modality : EvidenceEnvelope → Modality
  | .deductive _ => .deductive
  | .computational _ => .computational
  | .probabilistic _ => .probabilistic
  | .statistical _ => .statistical
  | .empiricalWindow _ => .empiricalWindow
  | .assumptionRelative _ => .assumptionRelative

/--
The only evidence packet admitted past the CM-1 typing boundary.

The shared type index is load-bearing.  There is no field by which a caller can
assert that differently indexed evidence should count as this claim's
modality.
-/
structure ClaimEvidencePacket (modality : Modality) where
  claim : Claim modality
  evidence : Evidence modality

/-- Existential packaging of a packet after same-modality reconstruction. -/
inductive SomeClaimEvidencePacket
  | pack
      (modality : Modality)
      (packet : ClaimEvidencePacket modality)

/-- The modality of an aligned packet is its dependent type index. -/
def SomeClaimEvidencePacket.modality : SomeClaimEvidencePacket → Modality
  | .pack modality _ => modality

/-- Named CM-1 refusal: the expected and actual indices differ. -/
inductive ClaimModalityResidue
  | evidenceModalityMismatch (expected actual : Modality)
  deriving DecidableEq, Repr

/--
The total output of the modality boundary.

`aligned` is not yet semantic proof acceptance.  It is the only input shape on
which a modality-indexed verifier is permitted to operate.
-/
inductive EvidenceAlignmentResult
  | aligned (packet : SomeClaimEvidencePacket)
  | refuse (residue : ClaimModalityResidue)

/--
Mechanically align untrusted claim and evidence envelopes.

All six matching pairs reconstruct a dependent packet.  Every other pair is a
typed refusal carrying expected and actual modalities derived from the
constructors, not supplied by a string tag.
-/
def alignEvidence :
    ClaimEnvelope → EvidenceEnvelope → EvidenceAlignmentResult
  | .deductive claim, .deductive evidence =>
      .aligned (.pack .deductive ⟨claim, evidence⟩)
  | .computational claim, .computational evidence =>
      .aligned (.pack .computational ⟨claim, evidence⟩)
  | .probabilistic claim, .probabilistic evidence =>
      .aligned (.pack .probabilistic ⟨claim, evidence⟩)
  | .statistical claim, .statistical evidence =>
      .aligned (.pack .statistical ⟨claim, evidence⟩)
  | .empiricalWindow claim, .empiricalWindow evidence =>
      .aligned (.pack .empiricalWindow ⟨claim, evidence⟩)
  | .assumptionRelative claim, .assumptionRelative evidence =>
      .aligned (.pack .assumptionRelative ⟨claim, evidence⟩)
  | claim, evidence =>
      .refuse
        (.evidenceModalityMismatch claim.modality evidence.modality)

/--
A semantic verifier is itself modality-indexed.

It cannot even be applied to evidence of the wrong modality.  Soundness of a
particular verifier remains an instance theorem and is not manufactured by
CM-1.
-/
structure ModalityVerifier where
  Accepts :
    {modality : Modality} →
      Claim modality → Evidence modality → Prop

/--
Proof-carrying semantic acceptance after modality alignment.

The acceptance proof and its payload necessarily have the same type index.
-/
structure VerifiedClaim
    (verifier : ModalityVerifier)
    (modality : Modality) where
  claim : Claim modality
  evidence : Evidence modality
  accepted : verifier.Accepts claim evidence

/-- Every aligned packet reports the modality of both original envelopes. -/
theorem aligned_packet_preserves_both_modalities
    (claim : ClaimEnvelope)
    (evidence : EvidenceEnvelope)
    (packet : SomeClaimEvidencePacket)
    (aligned : alignEvidence claim evidence = .aligned packet) :
    packet.modality = claim.modality ∧
      packet.modality = evidence.modality := by
  cases claim <;> cases evidence <;>
    simp [alignEvidence, SomeClaimEvidencePacket.modality,
      ClaimEnvelope.modality, EvidenceEnvelope.modality] at aligned ⊢
  all_goals cases aligned
  all_goals simp

/-- Unequal type-derived modalities always take the named refusal branch. -/
theorem mismatched_modalities_are_refused
    (claim : ClaimEnvelope)
    (evidence : EvidenceEnvelope)
    (mismatch : claim.modality ≠ evidence.modality) :
    alignEvidence claim evidence =
      .refuse
        (.evidenceModalityMismatch claim.modality evidence.modality) := by
  cases claim <;> cases evidence <;>
    simp [alignEvidence, ClaimEnvelope.modality,
      EvidenceEnvelope.modality] at mismatch ⊢

/-- The alignment boundary is exhaustive: it either reconstructs or refuses. -/
theorem alignment_result_exhaustive
    (claim : ClaimEnvelope)
    (evidence : EvidenceEnvelope) :
    (∃ packet, alignEvidence claim evidence = .aligned packet) ∨
      (∃ residue, alignEvidence claim evidence = .refuse residue) := by
  cases result : alignEvidence claim evidence with
  | aligned packet =>
      exact Or.inl ⟨packet, rfl⟩
  | refuse residue =>
      exact Or.inr ⟨residue, rfl⟩

end Residua.RCC.ClaimModality

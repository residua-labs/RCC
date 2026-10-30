import RCC.ClaimModality

/-!
# Registration site for CM-1 (ResiduaRCCClaimModality)

The six-modality index is a type index, not a string tag.  Positive half:
`alignEvidence` reconstructs a dependent packet at a matching deductive pair,
and every modality is one of the six registered constructors.  Discriminating
half: a mismatched deductive/computational pair takes the named refusal, and a
caller-tag mutant accepts what the boundary refuses.  The library theorems are
untouched.
-/

open Residua.RCC.ClaimModality

namespace Residua.RCC.RegistrationSites.CM1

/-- The CM-1 vocabulary enumerated at the fixture: exactly six modalities. -/
def sixModalities : List Modality :=
  [.deductive, .computational, .probabilistic, .statistical,
   .empiricalWindow, .assumptionRelative]

/-- Positive: every inhabitant of the index is one of the six. -/
theorem every_modality_is_one_of_six (modality : Modality) :
    modality ∈ sixModalities := by
  cases modality <;> decide

/-- Concrete deductive pair. -/
def dedClaim : Claim .deductive := .deductive "cq" "pq" "kq"
def dedEvidence : Evidence .deductive := .deductive "tq" "kq" "certq"

/-- Concrete computational evidence, used for the mismatch. -/
def compEvidence : Evidence .computational :=
  .computational "pq" "iq" "oq" "implq" "runq"

/-- Positive: matching envelopes align to a packet that preserves both
modalities. -/
theorem aligned_at_matching_envelopes :
    ∃ packet,
      alignEvidence (.deductive dedClaim) (.deductive dedEvidence) =
        .aligned packet := ⟨_, rfl⟩

theorem aligned_packet_is_deductive :
    ∀ packet,
      alignEvidence (.deductive dedClaim) (.deductive dedEvidence) =
        .aligned packet →
      packet.modality = .deductive := by
  intro packet aligned
  exact
    (aligned_packet_preserves_both_modalities _ _ _ aligned).1

/-- Discriminating: the mismatched pair is refused with both modalities named
in the residue. -/
theorem mismatched_envelopes_refused_at_fixture :
    alignEvidence (.deductive dedClaim) (.computational compEvidence) =
      .refuse (.evidenceModalityMismatch .deductive .computational) :=
  mismatched_modalities_are_refused _ _ (by decide)

/-- The caller-tag mutant: a boundary that decides by a string the caller
supplies instead of the type index. -/
def tagMutant (_claim : ClaimEnvelope) (_evidence : EvidenceEnvelope)
    (tag : String) : Bool :=
  tag == "aligned"

/-- Discriminating: the mutant accepts exactly the mismatched pair the real
boundary refuses — the two verdicts differ at the fixture. -/
theorem mutant_accepts_what_boundary_refuses :
    tagMutant (.deductive dedClaim) (.computational compEvidence) "aligned" =
        true ∧
      ∃ residue,
        alignEvidence (.deductive dedClaim) (.computational compEvidence) =
          .refuse residue :=
  ⟨rfl, _, mismatched_envelopes_refused_at_fixture⟩

/-- The mutant's acceptance carries no modality information: the same verdict
is returned for any two envelopes, so it cannot be the boundary CM-1 states. -/
theorem mutant_verdict_is_tag_only :
    ∀ claim₁ claim₂ : ClaimEnvelope,
      ∀ evidence₁ evidence₂ : EvidenceEnvelope,
      ∀ tag,
        tagMutant claim₁ evidence₁ tag = tagMutant claim₂ evidence₂ tag := by
  intro _ _ _ _ _; rfl

#print axioms every_modality_is_one_of_six
#print axioms aligned_at_matching_envelopes
#print axioms aligned_packet_is_deductive
#print axioms mismatched_envelopes_refused_at_fixture
#print axioms mutant_accepts_what_boundary_refuses
#print axioms mutant_verdict_is_tag_only

end Residua.RCC.RegistrationSites.CM1

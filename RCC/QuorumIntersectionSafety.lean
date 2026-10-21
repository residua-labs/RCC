/-!
# RCC-40 Quorum Intersection Safety

This finite kernel states quorum safety at the general set level: every two
lawful quorums intersect in a signer outside every declared allowed fault set.
A finite vote-lock state plus non-equivocation for signers outside the actual
fault set then makes two same-slot valid quorum certificates judgment-equivalent.

`allowedFaultSets` is a caller-supplied closed-world declaration.  This file
does not prove that it includes every fault set that can occur in reality;
fault-set completeness remains an explicit instance assumption/nonclaim.
Cardinality bounds such as `2q > n + f` may justify concrete configurations,
but they are not the definition or proof of the general theorem here.

Constructive Prelude-only Lean 4.14; no Mathlib or repository
detector/registry/workflow/aggregator integration.
-/

namespace Residua.RCC.QuorumIntersectionSafety

universe u v w

/-- Finite authority configuration and its judgment-equivalence relation. -/
structure FiniteQuorumSystem where
  Member : Type u
  Slot : Type v
  Judgment : Type w
  equivalent : Judgment → Judgment → Prop
  members : List Member
  quorums : List (List Member)
  allowedFaultSets : List (List Member)

/-- A lawful quorum is listed, duplicate-free, and contains only members. -/
def LawfulQuorum (system : FiniteQuorumSystem)
    (quorum : List system.Member) : Prop :=
  quorum ∈ system.quorums ∧
    quorum.Nodup ∧
    ∀ signer, signer ∈ quorum → signer ∈ system.members

/-- An allowed fault set is listed, duplicate-free, and contains only members. -/
def AllowedFaultSet (system : FiniteQuorumSystem)
    (faultSet : List system.Member) : Prop :=
  faultSet ∈ system.allowedFaultSets ∧
    faultSet.Nodup ∧
    ∀ signer, signer ∈ faultSet → signer ∈ system.members

/--
The general RCC-40 condition: the intersection of any two lawful quorums is not
covered by any declared allowed fault set.
-/
def QuorumIntersectionSafe (system : FiniteQuorumSystem) : Prop :=
  ∀ first,
    LawfulQuorum system first →
      ∀ second,
        LawfulQuorum system second →
          ∀ faultSet,
            AllowedFaultSet system faultSet →
              ∃ signer,
                signer ∈ first ∧
                  signer ∈ second ∧
                  signer ∉ faultSet

/-- One durable vote-lock entry. -/
structure LockedVote (system : FiniteQuorumSystem) where
  signer : system.Member
  slot : system.Slot
  judgment : system.Judgment

/-- A finite snapshot of durable vote-lock entries. -/
structure VoteLockState (system : FiniteQuorumSystem) where
  lockedVotes : List (LockedVote system)

/-- The finite lock snapshot contains this exact signer/slot/judgment vote. -/
def HasLockedVote {system : FiniteQuorumSystem}
    (locks : VoteLockState system)
    (signer : system.Member) (slot : system.Slot)
    (judgment : system.Judgment) : Prop :=
  ∃ locked,
    locked ∈ locks.lockedVotes ∧
      locked.signer = signer ∧
      locked.slot = slot ∧
      locked.judgment = judgment

/--
Every member outside the actual fault set is non-equivocating in the durable
lock snapshot.  Members inside the fault set may have conflicting locks.
-/
def HonestNonEquivocation (system : FiniteQuorumSystem)
    (locks : VoteLockState system)
    (faultSet : List system.Member) : Prop :=
  ∀ signer,
    signer ∈ system.members →
      signer ∉ faultSet →
        ∀ slot firstJudgment secondJudgment,
          HasLockedVote locks signer slot firstJudgment →
            HasLockedVote locks signer slot secondJudgment →
              system.equivalent firstJudgment secondJudgment

/-- A listed lawful quorum whose every signer has a locked vote. -/
structure ValidQC (system : FiniteQuorumSystem)
    (locks : VoteLockState system)
    (slot : system.Slot) (judgment : system.Judgment) where
  quorum : List system.Member
  lawful : LawfulQuorum system quorum
  votes :
    ∀ signer, signer ∈ quorum →
      HasLockedVote locks signer slot judgment

/--
RCC-40: an honest signer in the quorum intersection links two same-slot valid
QCs, and its durable non-equivocation makes their judgments equivalent.
-/
theorem valid_qcs_same_slot_equivalent
    (system : FiniteQuorumSystem)
    (locks : VoteLockState system)
    (intersectionSafe : QuorumIntersectionSafe system)
    (faultSet : List system.Member)
    (faultAllowed : AllowedFaultSet system faultSet)
    (honestLocks : HonestNonEquivocation system locks faultSet)
    {slot : system.Slot}
    {firstJudgment secondJudgment : system.Judgment}
    (firstQC : ValidQC system locks slot firstJudgment)
    (secondQC : ValidQC system locks slot secondJudgment) :
    system.equivalent firstJudgment secondJudgment := by
  obtain ⟨signer, hfirst, hsecond, hhonest⟩ :=
    intersectionSafe
      firstQC.quorum firstQC.lawful
      secondQC.quorum secondQC.lawful
      faultSet faultAllowed
  exact honestLocks signer
    (firstQC.lawful.2.2 signer hfirst)
    hhonest slot firstJudgment secondJudgment
    (firstQC.votes signer hfirst)
    (secondQC.votes signer hsecond)

end Residua.RCC.QuorumIntersectionSafety

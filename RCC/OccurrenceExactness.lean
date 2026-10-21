/-!
# RCC-27 Occurrence Exactness

Occurrence identity names one logical effect occurrence, not its payload
content.  A retry preserves every occurrence coordinate; an intentional repeat
must change at least one coordinate, normally `generation`.

This kernel proves exactness for the structured occurrence key before hashing.
Digest binding, collision handling, at-least-once delivery, atomic receiver
deduplication, and fencing remain separate AddressKernel / RCC-28 obligations.
-/

namespace Residua.RCC.OccurrenceExactness

universe u v w x

/-- One logical effect occurrence. -/
structure Occurrence
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) where
  run : Run
  slot : Slot
  generation : Generation
  effectKind : EffectKind
  deriving DecidableEq, Repr

/--
The structured canonical identity committed before domain-separated encoding
and digesting.
-/
structure OccurrenceKey
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) where
  run : Run
  slot : Slot
  generation : Generation
  effectKind : EffectKind
  deriving DecidableEq, Repr

def occurrenceKey
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (occurrence : Occurrence Run Slot Generation EffectKind) :
    OccurrenceKey Run Slot Generation EffectKind where
  run := occurrence.run
  slot := occurrence.slot
  generation := occurrence.generation
  effectKind := occurrence.effectKind

/-- The role relation independently names equality of all four coordinates. -/
def SameLogicalOccurrence
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (left right : Occurrence Run Slot Generation EffectKind) : Prop :=
  left.run = right.run ∧
    left.slot = right.slot ∧
    left.generation = right.generation ∧
    left.effectKind = right.effectKind

theorem occurrence_key_exact
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (left right : Occurrence Run Slot Generation EffectKind) :
    occurrenceKey left = occurrenceKey right ↔
      SameLogicalOccurrence left right := by
  cases left with
  | mk leftRun leftSlot leftGeneration leftKind =>
      cases right with
      | mk rightRun rightSlot rightGeneration rightKind =>
          constructor
          · intro equal
            exact
              ⟨congrArg
                  (fun key :
                    OccurrenceKey Run Slot Generation EffectKind => key.run)
                  equal,
                congrArg
                  (fun key :
                    OccurrenceKey Run Slot Generation EffectKind => key.slot)
                  equal,
                congrArg
                  (fun key :
                    OccurrenceKey Run Slot Generation EffectKind => key.generation)
                  equal,
                congrArg
                  (fun key :
                    OccurrenceKey Run Slot Generation EffectKind => key.effectKind)
                  equal⟩
          · rintro ⟨runEqual, slotEqual, generationEqual, kindEqual⟩
            cases runEqual
            cases slotEqual
            cases generationEqual
            cases kindEqual
            rfl

theorem same_logical_occurrence_refl
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (occurrence : Occurrence Run Slot Generation EffectKind) :
    SameLogicalOccurrence occurrence occurrence :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem same_logical_occurrence_symm
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    {left right : Occurrence Run Slot Generation EffectKind}
    (same : SameLogicalOccurrence left right) :
    SameLogicalOccurrence right left := by
  rcases same with ⟨runEqual, slotEqual, generationEqual, kindEqual⟩
  exact ⟨runEqual.symm, slotEqual.symm, generationEqual.symm, kindEqual.symm⟩

theorem same_logical_occurrence_trans
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    {first second third : Occurrence Run Slot Generation EffectKind}
    (firstSecond : SameLogicalOccurrence first second)
    (secondThird : SameLogicalOccurrence second third) :
    SameLogicalOccurrence first third := by
  rcases firstSecond with ⟨run₁, slot₁, generation₁, kind₁⟩
  rcases secondThird with ⟨run₂, slot₂, generation₂, kind₂⟩
  exact
    ⟨run₁.trans run₂, slot₁.trans slot₂, generation₁.trans generation₂,
      kind₁.trans kind₂⟩

end Residua.RCC.OccurrenceExactness

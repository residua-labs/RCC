import RCC.AddressResolution

/-!
# RCC addressed-graph foundation

This module defines the proof-free addressed-graph syntax and its exact,
structural TLV codec.  Graph closure, reachability, selector bounds, SCC
canonicalization, and graph quotient laws deliberately live downstream.
-/

namespace Residua.RCC.Addressing.AddressedGraph.Foundation

open Residua.RCC.Addressing

set_option linter.deprecated false

abbrev GraphBytes := List Nat

structure GraphText where
  scalars : List Char
  deriving DecidableEq, Repr

def GraphText.value (text : GraphText) : String :=
  String.mk text.scalars

abbrev GraphLabel := GraphText

structure GraphWireAddress (kind : AddressKind) where
  algorithm : GraphText
  domainQ : GraphText
  schemaQ : GraphText
  digest : GraphText
  deriving DecidableEq, Repr

def GraphWireAddress.toAddress
    (address : GraphWireAddress kind) : Address kind where
  algorithm := ⟨address.algorithm.value⟩
  domainQ := ⟨address.domainQ.value⟩
  schemaQ := ⟨address.schemaQ.value⟩
  digest := ⟨address.digest.value⟩

structure GraphKindSchema where
  Kind : Type
  decideKindEq : (left right : Kind) → Decidable (left = right)
  enumerate : List Kind
  enumerateNoDuplicates :
    ∀ (leftIndex rightIndex)
      (leftBound : leftIndex < enumerate.length)
      (rightBound : rightIndex < enumerate.length),
      enumerate[leftIndex]'leftBound =
          enumerate[rightIndex]'rightBound →
      leftIndex = rightIndex
  enumerateComplete : ∀ kind, kind ∈ enumerate
  kindCode : Kind → Nat
  kindCodeInjective :
    ∀ {left right}, kindCode left = kindCode right → left = right
  toAddressKind : Kind → AddressKind
  toAddressKindInjective :
    ∀ {left right},
      toAddressKind left = toAddressKind right → left = right

instance (schema : GraphKindSchema) : DecidableEq schema.Kind :=
  schema.decideKindEq

structure BlockNodeAddress
    (schema : GraphKindSchema) (kind : schema.Kind) where
  blockQ : GraphWireAddress (schema.toAddressKind kind)
  canonicalLocalIndex : Nat

def BlockNodeAddress.address
    (target : BlockNodeAddress schema kind) :
    Address (schema.toAddressKind kind) :=
  target.blockQ.toAddress

structure ExternalRef (schema : GraphKindSchema) where
  kind : schema.Kind
  target : BlockNodeAddress schema kind

inductive GraphRef (External : Type)
  | external : External → GraphRef External
  | local : Nat → GraphRef External

inductive EdgeDirection
  | outgoing
  | incoming
  deriving DecidableEq, Repr

inductive EdgeCollectionMode
  | ordered
  | unordered
  deriving DecidableEq, Repr

inductive EdgeCollection
    (schema : GraphKindSchema) (External : Type)
  | ordered (label : GraphLabel) (direction : EdgeDirection)
      (expectedTargetKind : schema.Kind) (targets : List (GraphRef External))
  | unordered (label : GraphLabel) (direction : EdgeDirection)
      (expectedTargetKind : schema.Kind) (targets : List (GraphRef External))

def EdgeCollection.mode :
    EdgeCollection schema External → EdgeCollectionMode
  | .ordered .. => .ordered
  | .unordered .. => .unordered

def EdgeCollection.labelText :
    EdgeCollection schema External → GraphLabel
  | .ordered label .. => label
  | .unordered label .. => label

def EdgeCollection.label
    (collection : EdgeCollection schema External) : String :=
  collection.labelText.value

def EdgeCollection.direction :
    EdgeCollection schema External → EdgeDirection
  | .ordered _ direction .. => direction
  | .unordered _ direction .. => direction

def EdgeCollection.expectedTargetKind :
    EdgeCollection schema External → schema.Kind
  | .ordered _ _ expected _ => expected
  | .unordered _ _ expected _ => expected

def EdgeCollection.targets :
    EdgeCollection schema External → List (GraphRef External)
  | .ordered _ _ _ targets => targets
  | .unordered _ _ _ targets => targets

structure GraphNode
    (schema : GraphKindSchema) (External : Type) where
  payload : Nat
  edgeCollections : List (EdgeCollection schema External)

abbrev CanonicalNode (schema : GraphKindSchema) :=
  GraphNode schema (ExternalRef schema)

inductive CanonicalBlock
    (schema : GraphKindSchema) (sourceKind : schema.Kind)
  | dagSingleton : CanonicalNode schema → CanonicalBlock schema sourceKind
  | cyclic : List (CanonicalNode schema) → CanonicalBlock schema sourceKind

def CanonicalBlock.nodes :
    CanonicalBlock schema kind → List (CanonicalNode schema)
  | .dagSingleton node => [node]
  | .cyclic nodes => nodes

inductive CanonicalBlockForm
  | dagSingleton
  | cyclic
  deriving DecidableEq, Repr

def CanonicalBlock.form :
    CanonicalBlock schema kind → CanonicalBlockForm
  | .dagSingleton _ => .dagSingleton
  | .cyclic _ => .cyclic

inductive BlockDecodeResidue
  | unknownTag
  | truncated
  | noncanonicalNatural
  | noncanonicalString
  | invalidKindCode
  | malformedLength
  | trailingData
  deriving DecidableEq, Repr

private def tlv (tag : Nat) (payload : GraphBytes) : GraphBytes :=
  [tag, payload.length] ++ payload

private def encodeText (value : GraphText) : GraphBytes :=
  value.scalars.length :: value.scalars.map Char.toNat

private def encodeKind
    (schema : GraphKindSchema) (kind : schema.Kind) : GraphBytes :=
  tlv 10 [schema.kindCode kind]

def encodeTypedAddress
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (address : GraphWireAddress (schema.toAddressKind kind)) :
    GraphBytes :=
  tlv 14
    (encodeKind schema kind ++
      encodeText address.algorithm ++
      encodeText address.domainQ ++
      encodeText address.schemaQ ++
      encodeText address.digest)

private def encodeExternal
    (schema : GraphKindSchema) (external : ExternalRef schema) : GraphBytes :=
  tlv 11
    (encodeTypedAddress schema external.kind external.target.blockQ ++
      tlv 12 [external.target.canonicalLocalIndex])

private def encodeRef
    (schema : GraphKindSchema) : GraphRef (ExternalRef schema) → GraphBytes
  | .local index => tlv 12 [index]
  | .external external => encodeExternal schema external

private def encodeList
    (encode : α → GraphBytes) (values : List α) : GraphBytes :=
  tlv 13
    (values.length ::
      values.flatMap fun value =>
        let encoded := encode value
        encoded.length :: encoded)

private def encodeDirection : EdgeDirection → GraphBytes
  | .outgoing => tlv 8 []
  | .incoming => tlv 9 []

private def encodeCollection
    (schema : GraphKindSchema)
    (collection : EdgeCollection schema (ExternalRef schema)) : GraphBytes :=
  let payload :=
    tlv 7 (encodeText collection.labelText) ++
      encodeDirection collection.direction ++
      encodeKind schema collection.expectedTargetKind ++
      encodeList (encodeRef schema) collection.targets
  match collection.mode with
  | .ordered => tlv 5 payload
  | .unordered => tlv 6 payload

private def encodeNode
    (schema : GraphKindSchema) (node : CanonicalNode schema) : GraphBytes :=
  tlv 3
    (tlv 4 [node.payload] ++
      encodeList (encodeCollection schema) node.edgeCollections)

def encodeCanonicalBlock :
    CanonicalBlock schema kind → GraphBytes
  | .dagSingleton node => tlv 1 (encodeNode schema node)
  | .cyclic nodes => tlv 2 (encodeList (encodeNode schema) nodes)

private abbrev DecodeM (α : Type) :=
  Except BlockDecodeResidue α

private abbrev Parsed (α : Type) :=
  α × GraphBytes

private def readTlv : GraphBytes → DecodeM (Parsed (Nat × GraphBytes))
  | tag :: length :: rest =>
      if _enough : length ≤ rest.length then
        .ok ((tag, rest.take length), rest.drop length)
      else
        .error .truncated
  | _ => .error .truncated

private theorem read_tlv_encode
    (tag : Nat) (payload suffix : GraphBytes) :
    readTlv (tlv tag payload ++ suffix) =
      .ok ((tag, payload), suffix) := by
  simp [readTlv, tlv]

private theorem read_tlv_decode
    {bytes : GraphBytes} {tag : Nat} {payload suffix : GraphBytes}
    (accepted : readTlv bytes = .ok ((tag, payload), suffix)) :
    tlv tag payload ++ suffix = bytes := by
  cases bytes with
  | nil =>
      simp [readTlv] at accepted
  | cons actualTag rest =>
      cases rest with
      | nil =>
          simp [readTlv] at accepted
      | cons length body =>
          simp only [readTlv] at accepted
          split at accepted
          next enough =>
            cases accepted
            simp [tlv, List.take_append_drop, Nat.min_eq_left enough]
          next notEnough =>
            contradiction

private def parseExactNat : GraphBytes → Except BlockDecodeResidue Nat
  | [value] => .ok value
  | _ => .error .noncanonicalNatural

private theorem parse_exact_nat_decode
    {bytes : GraphBytes} {value : Nat}
    (accepted : parseExactNat bytes = .ok value) :
    [value] = bytes := by
  cases bytes with
  | nil =>
      simp [parseExactNat] at accepted
  | cons first rest =>
      cases rest with
      | nil =>
          simp [parseExactNat] at accepted
          cases accepted
          rfl
      | cons second rest =>
          simp [parseExactNat] at accepted

private def charOfCanonicalNat (value : Nat) :
    Except BlockDecodeResidue Char :=
  let character := Char.ofNat value
  if character.toNat = value then .ok character
  else .error .noncanonicalString

private theorem char_of_canonical_nat_decode
    {value : Nat} {character : Char}
    (accepted : charOfCanonicalNat value = .ok character) :
    character.toNat = value := by
  by_cases valid : (Char.ofNat value).toNat = value
  · simp [charOfCanonicalNat, valid] at accepted
    cases accepted
    exact valid
  · simp [charOfCanonicalNat, valid] at accepted

private def parseChars :
    List Nat → Except BlockDecodeResidue (List Char)
  | [] => .ok []
  | value :: rest => do
      let character ← charOfCanonicalNat value
      let characters ← parseChars rest
      pure (character :: characters)

private theorem parse_chars_decode
    {codes : List Nat} {characters : List Char}
    (accepted : parseChars codes = .ok characters) :
    characters.map Char.toNat = codes := by
  induction codes generalizing characters with
  | nil =>
      simp [parseChars] at accepted
      cases accepted
      rfl
  | cons code rest inductionHypothesis =>
      simp only [parseChars] at accepted
      cases decodedCharacter : charOfCanonicalNat code with
      | error residue =>
          rw [decodedCharacter] at accepted
          contradiction
      | ok character =>
          rw [decodedCharacter] at accepted
          dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
          cases decodedRest : parseChars rest with
          | error residue =>
              rw [decodedRest] at accepted
              contradiction
          | ok tail =>
              simp only [decodedRest] at accepted
              cases accepted
              simp [
                char_of_canonical_nat_decode decodedCharacter,
                inductionHypothesis decodedRest
              ]

private def takeCells
    (length : Nat) (bytes : GraphBytes) :
    Except BlockDecodeResidue (GraphBytes × GraphBytes) :=
  if _enough : length ≤ bytes.length then
    .ok (bytes.take length, bytes.drop length)
  else
    .error .truncated

private theorem take_cells_decode
    {length : Nat} {bytes taken suffix : GraphBytes}
    (accepted : takeCells length bytes = .ok (taken, suffix)) :
    taken ++ suffix = bytes ∧ taken.length = length := by
  unfold takeCells at accepted
  split at accepted
  next enough =>
    cases accepted
    constructor
    · exact List.take_append_drop length bytes
    · simp [List.length_take, Nat.min_eq_left enough]
  next notEnough =>
    contradiction

private def parseText : GraphBytes → DecodeM (Parsed GraphText)
  | [] => .error .truncated
  | length :: rest =>
      match takeCells length rest with
      | .error residue => .error residue
      | .ok (codes, suffix) =>
          match parseChars codes with
          | .error residue => .error residue
          | .ok characters => .ok ({ scalars := characters }, suffix)

private theorem parse_text_decode
    {bytes : GraphBytes} {text : GraphText} {suffix : GraphBytes}
    (accepted : parseText bytes = .ok (text, suffix)) :
    encodeText text ++ suffix = bytes := by
  cases bytes with
  | nil =>
      simp [parseText] at accepted
  | cons length rest =>
      simp only [parseText] at accepted
      cases splitCells : takeCells length rest with
      | error residue =>
          simp [splitCells] at accepted
      | ok splitResult =>
          cases splitResult with
          | mk codes parsedSuffix =>
              simp only [splitCells] at accepted
              cases decodedChars : parseChars codes with
              | error residue =>
                  simp [decodedChars] at accepted
              | ok characters =>
                  simp only [decodedChars] at accepted
                  cases accepted
                  have reconstructed :=
                    (take_cells_decode splitCells).1
                  have exactLength :=
                    (take_cells_decode splitCells).2
                  have exactCodes := parse_chars_decode decodedChars
                  have characterLength :
                      characters.length = length := by
                    calc
                      characters.length =
                          (characters.map Char.toNat).length := by
                            simp
                      _ = codes.length := congrArg List.length exactCodes
                      _ = length := exactLength
                  simp only [encodeText]
                  simp [exactCodes, characterLength, reconstructed]

private def decodeKindCode
    (schema : GraphKindSchema) (code : Nat) : Option schema.Kind :=
  schema.enumerate.find? fun kind => schema.kindCode kind = code

private theorem decode_kind_code_encode
    (schema : GraphKindSchema) (kind : schema.Kind) :
    decodeKindCode schema (schema.kindCode kind) = some kind := by
  unfold decodeKindCode
  cases found :
      schema.enumerate.find? fun candidate =>
        schema.kindCode candidate = schema.kindCode kind with
  | none =>
      have rejected :=
        (List.find?_eq_none.mp found) kind (schema.enumerateComplete kind)
      simp at rejected
  | some candidate =>
      have equalCode :
          schema.kindCode candidate = schema.kindCode kind := by
        simpa using List.find?_some found
      have equalKind := schema.kindCodeInjective equalCode
      cases equalKind
      rfl

private theorem decode_kind_code_decode
    (schema : GraphKindSchema) {code : Nat} {kind : schema.Kind}
    (accepted : decodeKindCode schema code = some kind) :
    schema.kindCode kind = code := by
  unfold decodeKindCode at accepted
  simpa using List.find?_some accepted

private def parseKind
    (schema : GraphKindSchema) (bytes : GraphBytes) :
    DecodeM (Parsed schema.Kind) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag = 10 then
    let code ←
      match parseExactNat payload with
      | .ok code => pure code
      | .error residue => throw residue
    match decodeKindCode schema code with
    | some kind => pure (kind, suffix)
    | none => throw .invalidKindCode
  else
    throw .unknownTag

private theorem parse_kind_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes} {kind : schema.Kind} {suffix : GraphBytes}
    (accepted : parseKind schema bytes = .ok (kind, suffix)) :
    encodeKind schema kind ++ suffix = bytes := by
  simp only [parseKind] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases expectedTag : tag = 10
      · subst tag
        simp only [↓reduceIte] at accepted
        cases parsedNat : parseExactNat payload with
        | error residue =>
            rw [parsedNat] at accepted
            contradiction
        | ok code =>
            rw [parsedNat] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
            change
              (match decodeKindCode schema code with
                | some decoded => Except.ok (decoded, parsedSuffix)
                | none =>
                    Except.error BlockDecodeResidue.invalidKindCode) =
                Except.ok (kind, suffix) at accepted
            cases decodedKind : decodeKindCode schema code with
            | none =>
                rw [decodedKind] at accepted
                contradiction
            | some actualKind =>
                rw [decodedKind] at accepted
                cases accepted
                have framedExact := read_tlv_decode framedResult
                have payloadExact := parse_exact_nat_decode parsedNat
                have codeExact := decode_kind_code_decode schema decodedKind
                simp only [encodeKind]
                rw [codeExact, payloadExact]
                exact framedExact
      · simp [expectedTag] at accepted

private def parseAddressAfterKind
    (schema : GraphKindSchema) (kind : schema.Kind)
    (payload : GraphBytes) :
    DecodeM (Parsed (GraphWireAddress (schema.toAddressKind kind))) := do
  let parsedAlgorithm ← parseText payload
  let algorithm := parsedAlgorithm.1
  let afterAlgorithm := parsedAlgorithm.2
  let parsedDomain ← parseText afterAlgorithm
  let domain := parsedDomain.1
  let afterDomain := parsedDomain.2
  let parsedSchema ← parseText afterDomain
  let schemaValue := parsedSchema.1
  let afterSchema := parsedSchema.2
  let parsedDigest ← parseText afterSchema
  let digest := parsedDigest.1
  let suffix := parsedDigest.2
  pure
    ({ algorithm := algorithm
       domainQ := domain
       schemaQ := schemaValue
       digest := digest },
      suffix)

private theorem parse_address_decode
    (schema : GraphKindSchema) (kind : schema.Kind)
    {bytes : GraphBytes}
    {address : GraphWireAddress (schema.toAddressKind kind)}
    {suffix : GraphBytes}
    (accepted :
      parseAddressAfterKind schema kind bytes = .ok (address, suffix)) :
    encodeText address.algorithm ++
        encodeText address.domainQ ++
        encodeText address.schemaQ ++
        encodeText address.digest ++ suffix =
      bytes := by
  simp only [parseAddressAfterKind] at accepted
  cases algorithmResult : parseText bytes with
  | error residue =>
      rw [algorithmResult] at accepted
      contradiction
  | ok parsedAlgorithm =>
      rw [algorithmResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases parsedAlgorithm with ⟨algorithm, afterAlgorithm⟩
      cases domainResult : parseText afterAlgorithm with
      | error residue =>
          rw [domainResult] at accepted
          contradiction
      | ok parsedDomain =>
          rw [domainResult] at accepted
          dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
          rcases parsedDomain with ⟨domain, afterDomain⟩
          cases schemaResult : parseText afterDomain with
          | error residue =>
              rw [schemaResult] at accepted
              contradiction
          | ok parsedSchema =>
              rw [schemaResult] at accepted
              dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
              rcases parsedSchema with ⟨schemaValue, afterSchema⟩
              cases digestResult : parseText afterSchema with
              | error residue =>
                  rw [digestResult] at accepted
                  contradiction
              | ok parsedDigest =>
                  rw [digestResult] at accepted
                  dsimp only [Bind.bind, Except.instMonad, Except.bind]
                    at accepted
                  rcases parsedDigest with ⟨digest, parsedSuffix⟩
                  cases accepted
                  have algorithmExact := parse_text_decode algorithmResult
                  have domainExact := parse_text_decode domainResult
                  have schemaExact := parse_text_decode schemaResult
                  have digestExact := parse_text_decode digestResult
                  simp only [List.append_assoc]
                  rw [digestExact, schemaExact, domainExact, algorithmExact]

private structure DecodedTypedAddress (schema : GraphKindSchema) where
  kind : schema.Kind
  address : GraphWireAddress (schema.toAddressKind kind)

private def parseTypedAddress
    (schema : GraphKindSchema) (bytes : GraphBytes) :
    DecodeM (Parsed (DecodedTypedAddress schema)) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag ≠ 14 then
    throw .unknownTag
  let parsedKind ← parseKind schema payload
  let kind := parsedKind.1
  let afterKind := parsedKind.2
  let parsedAddress ← parseAddressAfterKind schema kind afterKind
  let address := parsedAddress.1
  let afterAddress := parsedAddress.2
  if afterAddress ≠ [] then
    throw .malformedLength
  pure ({ kind := kind, address := address }, suffix)

private theorem parse_typed_address_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes} {typed : DecodedTypedAddress schema}
    {suffix : GraphBytes}
    (accepted : parseTypedAddress schema bytes = .ok (typed, suffix)) :
    encodeTypedAddress schema typed.kind typed.address ++ suffix = bytes := by
  simp only [parseTypedAddress] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases correctTag : tag = 14
      · subst tag
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at accepted
        cases kindResult : parseKind schema payload with
        | error residue =>
            rw [kindResult] at accepted
            contradiction
        | ok parsedKind =>
            rw [kindResult] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
            rcases parsedKind with ⟨kind, afterKind⟩
            cases addressResult :
                parseAddressAfterKind schema kind afterKind with
            | error residue =>
                rw [addressResult] at accepted
                contradiction
            | ok parsedAddress =>
                rw [addressResult] at accepted
                dsimp only [Bind.bind, Except.instMonad, Except.bind]
                  at accepted
                rcases parsedAddress with ⟨address, afterAddress⟩
                by_cases hasRemainder : afterAddress ≠ []
                · simp [hasRemainder] at accepted
                  change
                    Except.error BlockDecodeResidue.malformedLength =
                      Except.ok (typed, suffix) at accepted
                  contradiction
                · have emptyRemainder : afterAddress = [] :=
                    Decidable.not_not.mp hasRemainder
                  subst afterAddress
                  simp only [not_true_eq_false, ↓reduceIte]
                    at accepted
                  cases accepted
                  have framedExact := read_tlv_decode framedResult
                  have kindExact := parse_kind_decode schema kindResult
                  have addressExact := parse_address_decode schema kind
                    addressResult
                  simp only [encodeTypedAddress, List.append_assoc]
                  simp only [List.append_nil] at addressExact
                  rw [← addressExact] at kindExact
                  simp only [List.append_assoc] at kindExact
                  rw [kindExact, framedExact]
      · have wrongTag : tag ≠ 14 := correctTag
        simp [wrongTag] at accepted

private def parseExternalPayload
    (schema : GraphKindSchema) (payload : GraphBytes) :
    Except BlockDecodeResidue (ExternalRef schema) := do
  let parsedTyped ← parseTypedAddress schema payload
  let typed := parsedTyped.1
  let afterAddress := parsedTyped.2
  let framedIndex ← readTlv afterAddress
  let indexTag := framedIndex.1.1
  let indexPayload := framedIndex.1.2
  let suffix := framedIndex.2
  if indexTag ≠ 12 then
    throw .unknownTag
  if suffix ≠ [] then
    throw .malformedLength
  let index ←
    match parseExactNat indexPayload with
    | .ok index => pure index
    | .error residue => throw residue
  pure
    { kind := typed.kind
      target :=
        { blockQ := typed.address
          canonicalLocalIndex := index } }

private theorem parse_external_payload_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes} {external : ExternalRef schema}
    (accepted : parseExternalPayload schema bytes = .ok external) :
    encodeTypedAddress schema external.kind external.target.blockQ ++
        tlv 12 [external.target.canonicalLocalIndex] =
      bytes := by
  simp only [parseExternalPayload] at accepted
  cases typedResult : parseTypedAddress schema bytes with
  | error residue =>
      rw [typedResult] at accepted
      contradiction
  | ok parsedTyped =>
      rw [typedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases parsedTyped with ⟨typed, afterAddress⟩
      cases indexFrameResult : readTlv afterAddress with
      | error residue =>
          rw [indexFrameResult] at accepted
          contradiction
      | ok indexFrame =>
          rw [indexFrameResult] at accepted
          dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
          rcases indexFrame with ⟨⟨indexTag, indexPayload⟩, frameSuffix⟩
          by_cases correctTag : indexTag = 12
          · subst indexTag
            simp only [ne_eq, not_true_eq_false, ↓reduceIte] at accepted
            by_cases hasRemainder : frameSuffix ≠ []
            · simp [hasRemainder] at accepted
              change
                Except.error BlockDecodeResidue.malformedLength =
                  Except.ok external at accepted
              contradiction
            · have emptyRemainder : frameSuffix = [] :=
                Decidable.not_not.mp hasRemainder
              subst frameSuffix
              simp only [not_true_eq_false, ↓reduceIte] at accepted
              cases indexResult : parseExactNat indexPayload with
              | error residue =>
                  rw [indexResult] at accepted
                  contradiction
              | ok index =>
                  rw [indexResult] at accepted
                  dsimp only [Bind.bind, Except.instMonad, Except.bind]
                    at accepted
                  cases accepted
                  have typedExact := parse_typed_address_decode schema
                    typedResult
                  have frameExact := read_tlv_decode indexFrameResult
                  have indexExact := parse_exact_nat_decode indexResult
                  simp only [List.append_nil] at frameExact
                  rw [← indexExact] at frameExact
                  change
                    encodeTypedAddress schema typed.kind typed.address ++
                        tlv 12 [index] =
                      bytes
                  rw [frameExact, typedExact]
          · have wrongTag : indexTag ≠ 12 := correctTag
            simp [wrongTag] at accepted

private def parseRef
    (schema : GraphKindSchema) (bytes : GraphBytes) :
    DecodeM (Parsed (GraphRef (ExternalRef schema))) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag = 11 then
    let external ← parseExternalPayload schema payload
    pure (.external external, suffix)
  else if tag = 12 then
      let index ←
        match parseExactNat payload with
        | .ok index => pure index
        | .error residue => throw residue
      pure (.local index, suffix)
  else
    throw .unknownTag

private theorem parse_ref_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes} {reference : GraphRef (ExternalRef schema)}
    {suffix : GraphBytes}
    (accepted : parseRef schema bytes = .ok (reference, suffix)) :
    encodeRef schema reference ++ suffix = bytes := by
  simp only [parseRef] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases externalTag : tag = 11
      · subst tag
        simp only [↓reduceIte] at accepted
        cases externalResult : parseExternalPayload schema payload with
        | error residue =>
            rw [externalResult] at accepted
            contradiction
        | ok external =>
            rw [externalResult] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
            cases accepted
            have framedExact := read_tlv_decode framedResult
            have externalExact :=
              parse_external_payload_decode schema externalResult
            simp only [encodeRef, encodeExternal]
            rw [externalExact, framedExact]
      · by_cases localTag : tag = 12
        · subst tag
          simp only [externalTag, ↓reduceIte] at accepted
          cases indexResult : parseExactNat payload with
          | error residue =>
              rw [indexResult] at accepted
              contradiction
          | ok index =>
              rw [indexResult] at accepted
              dsimp only [Bind.bind, Except.instMonad, Except.bind]
                at accepted
              cases accepted
              have framedExact := read_tlv_decode framedResult
              have indexExact := parse_exact_nat_decode indexResult
              simp only [encodeRef]
              rw [indexExact, framedExact]
        · simp [externalTag, localTag] at accepted

private def parseFramedElements
    (parse : GraphBytes → DecodeM (Parsed α)) :
    Nat → GraphBytes → Except BlockDecodeResidue (List α)
  | 0, [] => .ok []
  | 0, _ => .error .malformedLength
  | _ + 1, [] => .error .malformedLength
  | count + 1, length :: rest =>
      if _enough : length ≤ rest.length then do
        let elementBytes := rest.take length
        let suffix := rest.drop length
        let parsed ← parse elementBytes
        let value := parsed.1
        let elementSuffix := parsed.2
        if elementSuffix ≠ [] then
          throw .malformedLength
        let values ← parseFramedElements parse count suffix
        pure (value :: values)
      else
        .error .malformedLength

private theorem parse_framed_elements_length
    (parse : GraphBytes → DecodeM (Parsed α))
    {count : Nat} {bytes : GraphBytes} {values : List α}
    (accepted : parseFramedElements parse count bytes = .ok values) :
    values.length = count := by
  induction count generalizing bytes values with
  | zero =>
      cases bytes with
      | nil =>
          simp [parseFramedElements] at accepted
          cases accepted
          rfl
      | cons first rest =>
          simp [parseFramedElements] at accepted
  | succ count inductionHypothesis =>
      cases bytes with
      | nil =>
          simp [parseFramedElements] at accepted
      | cons length rest =>
          simp only [parseFramedElements] at accepted
          by_cases enough : length ≤ rest.length
          · simp only [enough, ↓reduceDIte] at accepted
            cases elementResult : parse (rest.take length) with
            | error residue =>
                rw [elementResult] at accepted
                contradiction
            | ok parsedElement =>
                rw [elementResult] at accepted
                dsimp only [Bind.bind, Except.instMonad, Except.bind]
                  at accepted
                rcases parsedElement with ⟨value, elementSuffix⟩
                by_cases hasRemainder : elementSuffix ≠ []
                · simp [hasRemainder] at accepted
                · have emptyRemainder : elementSuffix = [] :=
                    Decidable.not_not.mp hasRemainder
                  subst elementSuffix
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
                    at accepted
                  cases tailResult :
                      parseFramedElements parse count (rest.drop length) with
                  | error residue =>
                      rw [tailResult] at accepted
                      contradiction
                  | ok tail =>
                      rw [tailResult] at accepted
                      dsimp only [Bind.bind, Except.instMonad, Except.bind]
                        at accepted
                      cases accepted
                      simp only [List.length_cons]
                      rw [inductionHypothesis tailResult]
          · simp [enough] at accepted

private theorem parse_framed_elements_decode
    (encode : α → GraphBytes)
    (parse : GraphBytes → DecodeM (Parsed α))
    (reverse :
      ∀ {bytes value suffix},
        parse bytes = .ok (value, suffix) →
        encode value ++ suffix = bytes)
    {count : Nat} {bytes : GraphBytes} {values : List α}
    (accepted : parseFramedElements parse count bytes = .ok values) :
    (values.flatMap fun value =>
        let encoded := encode value
        encoded.length :: encoded) =
      bytes := by
  induction count generalizing bytes values with
  | zero =>
      cases bytes with
      | nil =>
          simp [parseFramedElements] at accepted
          cases accepted
          rfl
      | cons first rest =>
          simp [parseFramedElements] at accepted
  | succ count inductionHypothesis =>
      cases bytes with
      | nil =>
          simp [parseFramedElements] at accepted
      | cons length rest =>
          simp only [parseFramedElements] at accepted
          by_cases enough : length ≤ rest.length
          · simp only [enough, ↓reduceDIte] at accepted
            let elementBytes := rest.take length
            let remainingBytes := rest.drop length
            cases elementResult : parse elementBytes with
            | error residue =>
                rw [elementResult] at accepted
                contradiction
            | ok parsedElement =>
                rw [elementResult] at accepted
                dsimp only [Bind.bind, Except.instMonad, Except.bind]
                  at accepted
                rcases parsedElement with ⟨value, elementSuffix⟩
                by_cases hasRemainder : elementSuffix ≠ []
                · simp [hasRemainder] at accepted
                · have emptyRemainder : elementSuffix = [] :=
                    Decidable.not_not.mp hasRemainder
                  subst elementSuffix
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
                    at accepted
                  cases tailResult :
                      parseFramedElements parse count remainingBytes with
                  | error residue =>
                      rw [tailResult] at accepted
                      contradiction
                  | ok tail =>
                      rw [tailResult] at accepted
                      dsimp only [Bind.bind, Except.instMonad, Except.bind]
                        at accepted
                      cases accepted
                      have elementExact := reverse elementResult
                      simp only [List.append_nil] at elementExact
                      have tailExact := inductionHypothesis tailResult
                      have splitExact :
                          elementBytes ++ remainingBytes = rest :=
                        List.take_append_drop length rest
                      have elementLength :
                          elementBytes.length = length := by
                        simp [
                          elementBytes, List.length_take,
                          Nat.min_eq_left enough
                        ]
                      simp only [List.flatMap_cons]
                      rw [elementExact]
                      simp only [elementLength]
                      rw [tailExact]
                      exact congrArg (List.cons length) splitExact
          · simp [enough] at accepted

private def parseList
    (parse : GraphBytes → DecodeM (Parsed α))
    (bytes : GraphBytes) : DecodeM (Parsed (List α)) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag ≠ 13 then
    throw .unknownTag
  match payload with
  | [] => throw .malformedLength
  | count :: elements =>
      let values ← parseFramedElements parse count elements
      pure (values, suffix)

private theorem parse_list_decode
    (encode : α → GraphBytes)
    (parse : GraphBytes → DecodeM (Parsed α))
    (reverse :
      ∀ {bytes value suffix},
        parse bytes = .ok (value, suffix) →
        encode value ++ suffix = bytes)
    {bytes : GraphBytes} {values : List α} {suffix : GraphBytes}
    (accepted : parseList parse bytes = .ok (values, suffix)) :
    encodeList encode values ++ suffix = bytes := by
  simp only [parseList] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases correctTag : tag = 13
      · subst tag
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at accepted
        cases payload with
        | nil =>
            change
              Except.error BlockDecodeResidue.malformedLength =
                Except.ok (values, suffix) at accepted
            contradiction
        | cons count elements =>
            simp only [] at accepted
            cases elementsResult :
                parseFramedElements parse count elements with
            | error residue =>
                rw [elementsResult] at accepted
                contradiction
            | ok parsedValues =>
                rw [elementsResult] at accepted
                dsimp only [Bind.bind, Except.instMonad, Except.bind]
                  at accepted
                cases accepted
                have framedExact := read_tlv_decode framedResult
                have elementsExact :=
                  parse_framed_elements_decode encode parse reverse
                    elementsResult
                have countExact :=
                  parse_framed_elements_length parse elementsResult
                simp only [encodeList]
                rw [countExact, elementsExact, framedExact]
      · have wrongTag : tag ≠ 13 := correctTag
        simp [wrongTag] at accepted

private def parseDirection
    (bytes : GraphBytes) : DecodeM (Parsed EdgeDirection) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag = 8 then
      if payload = [] then pure (.outgoing, suffix)
      else throw .malformedLength
  else if tag = 9 then
      if payload = [] then pure (.incoming, suffix)
      else throw .malformedLength
  else
    throw .unknownTag

private theorem parse_direction_decode
    {bytes : GraphBytes} {direction : EdgeDirection}
    {suffix : GraphBytes}
    (accepted : parseDirection bytes = .ok (direction, suffix)) :
    encodeDirection direction ++ suffix = bytes := by
  simp only [parseDirection] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases outgoingTag : tag = 8
      · subst tag
        simp only [↓reduceIte] at accepted
        by_cases emptyPayload : payload = []
        · subst payload
          simp only [↓reduceIte] at accepted
          cases accepted
          exact read_tlv_decode framedResult
        · simp [emptyPayload] at accepted
      · simp only [outgoingTag, ↓reduceIte] at accepted
        by_cases incomingTag : tag = 9
        · subst tag
          simp only [↓reduceIte] at accepted
          by_cases emptyPayload : payload = []
          · subst payload
            simp only [↓reduceIte] at accepted
            cases accepted
            exact read_tlv_decode framedResult
          · simp [emptyPayload] at accepted
        · simp [incomingTag] at accepted

private def parseLabel (bytes : GraphBytes) : DecodeM (Parsed GraphLabel) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag ≠ 7 then
    throw .unknownTag
  let parsedLabel ← parseText payload
  let label := parsedLabel.1
  let payloadSuffix := parsedLabel.2
  if payloadSuffix ≠ [] then
    throw .malformedLength
  pure (label, suffix)

private theorem parse_label_decode
    {bytes : GraphBytes} {label : GraphLabel} {suffix : GraphBytes}
    (accepted : parseLabel bytes = .ok (label, suffix)) :
    tlv 7 (encodeText label) ++ suffix = bytes := by
  simp only [parseLabel] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases expectedTag : tag = 7
      · subst tag
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at accepted
        cases labelResult : parseText payload with
        | error residue =>
            rw [labelResult] at accepted
            contradiction
        | ok parsedLabel =>
            rw [labelResult] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind]
              at accepted
            rcases parsedLabel with ⟨decodedLabel, payloadSuffix⟩
            by_cases hasRemainder : payloadSuffix ≠ []
            · simp [hasRemainder] at accepted
              change
                Except.error BlockDecodeResidue.malformedLength =
                  Except.ok (label, suffix) at accepted
              contradiction
            · have emptyRemainder : payloadSuffix = [] :=
                Decidable.not_not.mp hasRemainder
              subst payloadSuffix
              simp only [not_true_eq_false, ↓reduceIte]
                at accepted
              cases accepted
              have payloadExact := parse_text_decode labelResult
              simp only [List.append_nil] at payloadExact
              rw [payloadExact]
              exact read_tlv_decode framedResult
      · simp [expectedTag] at accepted

private def parseCollectionMode
    (tag : Nat) : Except BlockDecodeResidue EdgeCollectionMode :=
  if tag = 5 then
    .ok .ordered
  else if tag = 6 then
    .ok .unordered
  else
    .error .unknownTag

private theorem parse_collection_mode_ordered_decode
    {tag : Nat}
    (accepted : parseCollectionMode tag = .ok .ordered) :
    tag = 5 := by
  unfold parseCollectionMode at accepted
  by_cases orderedTag : tag = 5
  · exact orderedTag
  · simp only [orderedTag, ↓reduceIte] at accepted
    by_cases unorderedTag : tag = 6
    · simp [unorderedTag] at accepted
    · simp [unorderedTag] at accepted

private theorem parse_collection_mode_unordered_decode
    {tag : Nat}
    (accepted : parseCollectionMode tag = .ok .unordered) :
    tag = 6 := by
  unfold parseCollectionMode at accepted
  by_cases orderedTag : tag = 5
  · simp [orderedTag] at accepted
  · simp only [orderedTag, ↓reduceIte] at accepted
    by_cases unorderedTag : tag = 6
    · exact unorderedTag
    · simp [unorderedTag] at accepted

private def parseCollection
    (schema : GraphKindSchema) (bytes : GraphBytes) :
    DecodeM (Parsed (EdgeCollection schema (ExternalRef schema))) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  let mode ← parseCollectionMode tag
  let parsedLabel ← parseLabel payload
  let label := parsedLabel.1
  let afterLabel := parsedLabel.2
  let parsedDirection ← parseDirection afterLabel
  let direction := parsedDirection.1
  let afterDirection := parsedDirection.2
  let parsedKind ← parseKind schema afterDirection
  let expectedKind := parsedKind.1
  let afterKind := parsedKind.2
  let parsedTargets ← parseList (parseRef schema) afterKind
  let targets := parsedTargets.1
  let afterTargets := parsedTargets.2
  if afterTargets ≠ [] then
    throw .malformedLength
  match mode with
  | .ordered => pure (.ordered label direction expectedKind targets, suffix)
  | .unordered => pure (.unordered label direction expectedKind targets, suffix)

private def parseNode
    (schema : GraphKindSchema) (bytes : GraphBytes) :
    DecodeM (Parsed (CanonicalNode schema)) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag ≠ 3 then
    throw .unknownTag
  let framedPayload ← readTlv payload
  let payloadTag := framedPayload.1.1
  let payloadBytes := framedPayload.1.2
  let afterPayload := framedPayload.2
  if payloadTag ≠ 4 then
    throw .unknownTag
  let nodePayload ←
    match parseExactNat payloadBytes with
    | .ok value => pure value
    | .error residue => throw residue
  let parsedCollections ← parseList (parseCollection schema) afterPayload
  let collections := parsedCollections.1
  let afterCollections := parsedCollections.2
  if afterCollections ≠ [] then
    throw .malformedLength
  pure ({ payload := nodePayload, edgeCollections := collections }, suffix)

private def parseBlock
    (schema : GraphKindSchema) (kind : schema.Kind)
    (bytes : GraphBytes) :
    DecodeM (Parsed (CanonicalBlock schema kind)) := do
  let framed ← readTlv bytes
  let tag := framed.1.1
  let payload := framed.1.2
  let suffix := framed.2
  if tag = 1 then
      let parsedNode ← parseNode schema payload
      let node := parsedNode.1
      let nodeSuffix := parsedNode.2
      if nodeSuffix ≠ [] then
        throw .malformedLength
      pure (.dagSingleton node, suffix)
  else if tag = 2 then
      let parsedNodes ← parseList (parseNode schema) payload
      let nodes := parsedNodes.1
      let nodesSuffix := parsedNodes.2
      if nodesSuffix ≠ [] then
        throw .malformedLength
      pure (.cyclic nodes, suffix)
  else
    throw .unknownTag

private theorem parse_collection_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes}
    {collection : EdgeCollection schema (ExternalRef schema)}
    {suffix : GraphBytes}
    (accepted :
      parseCollection schema bytes = .ok (collection, suffix)) :
    encodeCollection schema collection ++ suffix = bytes := by
  simp only [parseCollection] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      cases modeResult : parseCollectionMode tag with
      | error residue =>
          rw [modeResult] at accepted
          contradiction
      | ok mode =>
          rw [modeResult] at accepted
          dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
          cases labelResult : parseLabel payload with
          | error residue =>
              rw [labelResult] at accepted
              contradiction
          | ok parsedLabel =>
              rw [labelResult] at accepted
              dsimp only [Bind.bind, Except.instMonad, Except.bind]
                at accepted
              rcases parsedLabel with ⟨label, afterLabel⟩
              cases directionResult : parseDirection afterLabel with
              | error residue =>
                  rw [directionResult] at accepted
                  contradiction
              | ok parsedDirection =>
                  rw [directionResult] at accepted
                  dsimp only [Bind.bind, Except.instMonad, Except.bind]
                    at accepted
                  rcases parsedDirection with
                    ⟨direction, afterDirection⟩
                  cases kindResult : parseKind schema afterDirection with
                  | error residue =>
                      rw [kindResult] at accepted
                      contradiction
                  | ok parsedKind =>
                      rw [kindResult] at accepted
                      dsimp only [Bind.bind, Except.instMonad, Except.bind]
                        at accepted
                      rcases parsedKind with ⟨expectedKind, afterKind⟩
                      cases targetsResult :
                          parseList (parseRef schema) afterKind with
                      | error residue =>
                          rw [targetsResult] at accepted
                          contradiction
                      | ok parsedTargets =>
                          rw [targetsResult] at accepted
                          dsimp only [
                            Bind.bind, Except.instMonad, Except.bind
                          ] at accepted
                          rcases parsedTargets with
                            ⟨targets, afterTargets⟩
                          by_cases hasRemainder : afterTargets ≠ []
                          · simp [hasRemainder] at accepted
                          · have emptyRemainder : afterTargets = [] :=
                              Decidable.not_not.mp hasRemainder
                            subst afterTargets
                            simp only [
                              ne_eq, not_true_eq_false, ↓reduceIte
                            ] at accepted
                            have labelExact :=
                              parse_label_decode labelResult
                            have directionExact :=
                              parse_direction_decode directionResult
                            have kindExact :=
                              parse_kind_decode schema kindResult
                            have targetsExact :=
                              (by
                                simpa only [List.append_nil] using
                                  parse_list_decode
                                    (encodeRef schema) (parseRef schema)
                                    (parse_ref_decode schema) targetsResult)
                            have framedExact :=
                              read_tlv_decode framedResult
                            cases mode with
                            | ordered =>
                                have tagExact :=
                                  parse_collection_mode_ordered_decode
                                    modeResult
                                subst tag
                                cases accepted
                                simp only [
                                  encodeCollection, EdgeCollection.mode,
                                  EdgeCollection.labelText,
                                  EdgeCollection.direction,
                                  EdgeCollection.expectedTargetKind,
                                  EdgeCollection.targets
                                ]
                                simp only [List.append_assoc]
                                rw [
                                  targetsExact, kindExact,
                                  directionExact, labelExact, framedExact
                                ]
                            | unordered =>
                                have tagExact :=
                                  parse_collection_mode_unordered_decode
                                    modeResult
                                subst tag
                                cases accepted
                                simp only [
                                  encodeCollection, EdgeCollection.mode,
                                  EdgeCollection.labelText,
                                  EdgeCollection.direction,
                                  EdgeCollection.expectedTargetKind,
                                  EdgeCollection.targets
                                ]
                                simp only [List.append_assoc]
                                rw [
                                  targetsExact, kindExact,
                                  directionExact, labelExact, framedExact
                                ]

private theorem parse_node_decode
    (schema : GraphKindSchema)
    {bytes : GraphBytes} {node : CanonicalNode schema}
    {suffix : GraphBytes}
    (accepted : parseNode schema bytes = .ok (node, suffix)) :
    encodeNode schema node ++ suffix = bytes := by
  simp only [parseNode] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases expectedTag : tag = 3
      · subst tag
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at accepted
        cases payloadFrameResult : readTlv payload with
        | error residue =>
            rw [payloadFrameResult] at accepted
            contradiction
        | ok payloadFrame =>
            rw [payloadFrameResult] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind]
              at accepted
            rcases payloadFrame with
              ⟨⟨payloadTag, payloadBytes⟩, afterPayload⟩
            by_cases expectedPayloadTag : payloadTag = 4
            · subst payloadTag
              simp only [
                not_true_eq_false, ↓reduceIte
              ] at accepted
              cases payloadResult : parseExactNat payloadBytes with
              | error residue =>
                  rw [payloadResult] at accepted
                  contradiction
              | ok nodePayload =>
                  rw [payloadResult] at accepted
                  dsimp only [
                    Bind.bind, Except.instMonad, Except.bind
                  ] at accepted
                  cases collectionsResult :
                      parseList (parseCollection schema) afterPayload with
                  | error residue =>
                      rw [collectionsResult] at accepted
                      contradiction
                  | ok parsedCollections =>
                      rw [collectionsResult] at accepted
                      dsimp only [
                        Bind.bind, Except.instMonad, Except.bind
                      ] at accepted
                      rcases parsedCollections with
                        ⟨collections, afterCollections⟩
                      by_cases hasRemainder : afterCollections ≠ []
                      · simp [hasRemainder] at accepted
                        change
                          Except.error BlockDecodeResidue.malformedLength =
                            Except.ok (node, suffix) at accepted
                        contradiction
                      · have emptyRemainder : afterCollections = [] :=
                          Decidable.not_not.mp hasRemainder
                        subst afterCollections
                        simp only [
                          not_true_eq_false, ↓reduceIte
                        ] at accepted
                        cases accepted
                        have payloadExact :=
                          parse_exact_nat_decode payloadResult
                        have collectionsExact :
                            encodeList (encodeCollection schema)
                                collections =
                              afterPayload := by
                          simpa only [List.append_nil] using
                            parse_list_decode
                              (encodeCollection schema)
                              (parseCollection schema)
                              (parse_collection_decode schema)
                              collectionsResult
                        have payloadFrameExact :=
                          read_tlv_decode payloadFrameResult
                        have framedExact :=
                          read_tlv_decode framedResult
                        simp only [encodeNode]
                        rw [
                          collectionsExact, payloadExact,
                          payloadFrameExact, framedExact
                        ]
            · simp [expectedPayloadTag] at accepted
              change
                Except.error BlockDecodeResidue.unknownTag =
                  Except.ok (node, suffix) at accepted
              contradiction
      · simp [expectedTag] at accepted

private theorem parse_block_decode
    (schema : GraphKindSchema) (kind : schema.Kind)
    {bytes : GraphBytes} {block : CanonicalBlock schema kind}
    {suffix : GraphBytes}
    (accepted : parseBlock schema kind bytes = .ok (block, suffix)) :
    encodeCanonicalBlock block ++ suffix = bytes := by
  simp only [parseBlock] at accepted
  cases framedResult : readTlv bytes with
  | error residue =>
      rw [framedResult] at accepted
      contradiction
  | ok framed =>
      rw [framedResult] at accepted
      dsimp only [Bind.bind, Except.instMonad, Except.bind] at accepted
      rcases framed with ⟨⟨tag, payload⟩, parsedSuffix⟩
      by_cases singletonTag : tag = 1
      · subst tag
        simp only [↓reduceIte] at accepted
        cases nodeResult : parseNode schema payload with
        | error residue =>
            rw [nodeResult] at accepted
            contradiction
        | ok parsedNode =>
            rw [nodeResult] at accepted
            dsimp only [Bind.bind, Except.instMonad, Except.bind]
              at accepted
            rcases parsedNode with ⟨node, nodeSuffix⟩
            by_cases hasRemainder : nodeSuffix ≠ []
            · simp [hasRemainder] at accepted
            · have emptyRemainder : nodeSuffix = [] :=
                Decidable.not_not.mp hasRemainder
              subst nodeSuffix
              simp only [
                ne_eq, not_true_eq_false, ↓reduceIte
              ] at accepted
              cases accepted
              have nodeExact : encodeNode schema node = payload := by
                simpa only [List.append_nil] using
                  parse_node_decode schema nodeResult
              have framedExact := read_tlv_decode framedResult
              simp only [encodeCanonicalBlock]
              rw [nodeExact, framedExact]
      · simp only [singletonTag, ↓reduceIte] at accepted
        by_cases cyclicTag : tag = 2
        · subst tag
          simp only [↓reduceIte] at accepted
          cases nodesResult : parseList (parseNode schema) payload with
          | error residue =>
              rw [nodesResult] at accepted
              contradiction
          | ok parsedNodes =>
              rw [nodesResult] at accepted
              dsimp only [Bind.bind, Except.instMonad, Except.bind]
                at accepted
              rcases parsedNodes with ⟨nodes, nodesSuffix⟩
              by_cases hasRemainder : nodesSuffix ≠ []
              · simp [hasRemainder] at accepted
              · have emptyRemainder : nodesSuffix = [] :=
                  Decidable.not_not.mp hasRemainder
                subst nodesSuffix
                simp only [
                  ne_eq, not_true_eq_false, ↓reduceIte
                ] at accepted
                cases accepted
                have nodesExact :
                    encodeList (encodeNode schema) nodes = payload := by
                  simpa only [List.append_nil] using
                    parse_list_decode
                      (encodeNode schema) (parseNode schema)
                      (parse_node_decode schema) nodesResult
                have framedExact := read_tlv_decode framedResult
                simp only [encodeCanonicalBlock]
                rw [nodesExact, framedExact]
        · simp [cyclicTag] at accepted

def decodeCanonicalBlockPrefix
    (schema : GraphKindSchema) (kind : schema.Kind)
    (bytes : GraphBytes) :
    DecodeM (Parsed (CanonicalBlock schema kind)) :=
  parseBlock schema kind bytes

def decodeCanonicalBlockDetailed
    (schema : GraphKindSchema) (kind : schema.Kind)
    (bytes : GraphBytes) :
    Except BlockDecodeResidue (CanonicalBlock schema kind) :=
  match decodeCanonicalBlockPrefix schema kind bytes with
  | .error residue => .error residue
  | .ok (block, []) => .ok block
  | .ok (_, _ :: _) => .error .trailingData

private theorem parse_chars_encode (characters : List Char) :
    parseChars (characters.map Char.toNat) = .ok characters := by
  induction characters with
  | nil => rfl
  | cons character rest inductionHypothesis =>
      have valid :
          (Char.ofNat character.toNat).toNat = character.toNat :=
        congrArg Char.toNat (Char.ofNat_toNat character)
      simp only [List.map_cons, parseChars, charOfCanonicalNat]
      rw [if_pos valid, Char.ofNat_toNat, inductionHypothesis]
      change Except.ok (character :: rest) = Except.ok (character :: rest)
      rfl

private theorem parse_text_encode
    (value : GraphText) (suffix : GraphBytes) :
    parseText (encodeText value ++ suffix) = .ok (value, suffix) := by
  cases value with
  | mk scalars =>
    simp [
      parseText, encodeText, takeCells, List.length_map,
      parse_chars_encode
    ]

private theorem parse_kind_encode
    (schema : GraphKindSchema) (kind : schema.Kind) (suffix : GraphBytes) :
    parseKind schema (encodeKind schema kind ++ suffix) = .ok (kind, suffix) := by
  simp [
    parseKind, encodeKind, tlv, readTlv, parseExactNat
  ]
  change
    (match decodeKindCode schema (schema.kindCode kind) with
      | some decoded => Except.ok (decoded, suffix)
      | none => Except.error BlockDecodeResidue.invalidKindCode) =
      Except.ok (kind, suffix)
  rw [decode_kind_code_encode]

private theorem parse_address_encode
    (schema : GraphKindSchema) (kind : schema.Kind)
    (address : GraphWireAddress (schema.toAddressKind kind))
    (suffix : GraphBytes) :
    parseAddressAfterKind schema kind
        (encodeText address.algorithm ++
          encodeText address.domainQ ++
          encodeText address.schemaQ ++
          encodeText address.digest ++ suffix) =
      .ok (address, suffix) := by
  cases address
  simp only [parseAddressAfterKind]
  simp only [List.append_assoc]
  rw [parse_text_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  rw [parse_text_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  rw [parse_text_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  rw [parse_text_encode]
  rfl

private theorem parse_typed_address_encode
    (schema : GraphKindSchema) (kind : schema.Kind)
    (address : GraphWireAddress (schema.toAddressKind kind))
    (suffix : GraphBytes) :
    parseTypedAddress schema
        (encodeTypedAddress schema kind address ++ suffix) =
      .ok ({ kind := kind, address := address }, suffix) := by
  simp only [parseTypedAddress, encodeTypedAddress]
  rw [read_tlv_encode]
  simp only [List.append_assoc]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  rw [parse_kind_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  have parsedAddress := parse_address_encode schema kind address []
  simp only [List.append_nil] at parsedAddress
  have parsedAddressRight :
      parseAddressAfterKind schema kind
          (encodeText address.algorithm ++
            (encodeText address.domainQ ++
              (encodeText address.schemaQ ++
                encodeText address.digest))) =
        .ok (address, []) := by
    simpa only [List.append_assoc] using parsedAddress
  rw [parsedAddressRight]
  simp
  rfl

private theorem parse_external_payload_encode
    (schema : GraphKindSchema) (kind : schema.Kind)
    (address : GraphWireAddress (schema.toAddressKind kind))
    (index : Nat) :
    parseExternalPayload schema
        (encodeTypedAddress schema kind address ++ tlv 12 [index]) =
      .ok
        { kind := kind
          target := { blockQ := address, canonicalLocalIndex := index } } := by
  simp only [parseExternalPayload]
  rw [parse_typed_address_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  have framed :
      readTlv (tlv 12 [index]) = .ok ((12, [index]), []) := by
    simpa using read_tlv_encode 12 [index] []
  rw [framed]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  simp [parseExactNat]
  rfl

private theorem parse_ref_encode
    (schema : GraphKindSchema)
    (reference : GraphRef (ExternalRef schema))
    (suffix : GraphBytes) :
    parseRef schema (encodeRef schema reference ++ suffix) =
      .ok (reference, suffix) := by
  cases reference
  · rename_i external
    cases external with
    | mk kind target =>
        cases target with
        | mk address index =>
            simp only [parseRef, encodeRef, encodeExternal]
            rw [read_tlv_encode]
            dsimp only [Bind.bind, Except.instMonad, Except.bind]
            rw [parse_external_payload_encode]
            rfl
  · rename_i index
    simp [parseRef, encodeRef, read_tlv_encode, parseExactNat]
    rfl

private theorem parse_framed_elements_encode
    (encode : α → GraphBytes)
    (parse : GraphBytes → DecodeM (Parsed α))
    (roundtrip :
      ∀ value suffix, parse (encode value ++ suffix) = .ok (value, suffix))
    (values : List α) :
    parseFramedElements parse values.length
        (values.flatMap fun value =>
          let encoded := encode value
          encoded.length :: encoded) =
      .ok values := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      change
        parseFramedElements parse (Nat.succ rest.length)
            ((encode value).length ::
              (encode value ++
                rest.flatMap fun item =>
                  let encoded := encode item
                  encoded.length :: encoded)) =
          .ok (value :: rest)
      simp only [parseFramedElements]
      have parsedValue : parse (encode value) = .ok (value, []) := by
        simpa using roundtrip value []
      simp [parsedValue, inductionHypothesis]
      rfl

private theorem parse_list_encode
    (encode : α → GraphBytes)
    (parse : GraphBytes → DecodeM (Parsed α))
    (roundtrip :
      ∀ value suffix, parse (encode value ++ suffix) = .ok (value, suffix))
    (values : List α) (suffix : GraphBytes) :
    parseList parse (encodeList encode values ++ suffix) =
      .ok (values, suffix) := by
  simp only [parseList, encodeList]
  rw [read_tlv_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  rw [parse_framed_elements_encode encode parse roundtrip values]
  rfl

private theorem parse_label_encode
    (label : GraphLabel) (suffix : GraphBytes) :
    parseLabel (tlv 7 (encodeText label) ++ suffix) =
      .ok (label, suffix) := by
  simp only [parseLabel]
  rw [read_tlv_encode]
  dsimp only [Bind.bind, Except.instMonad, Except.bind]
  have parsed := parse_text_encode label []
  simp only [List.append_nil] at parsed
  rw [parsed]
  simp
  rfl

private theorem parse_direction_encode
    (direction : EdgeDirection) (suffix : GraphBytes) :
    parseDirection (encodeDirection direction ++ suffix) =
      .ok (direction, suffix) := by
  cases direction <;>
    simp [parseDirection, encodeDirection, read_tlv_encode] <;>
    rfl

private theorem parse_collection_encode
    (schema : GraphKindSchema)
    (collection : EdgeCollection schema (ExternalRef schema))
    (suffix : GraphBytes) :
    parseCollection schema (encodeCollection schema collection ++ suffix) =
      .ok (collection, suffix) := by
  cases collection with
  | ordered label direction expectedKind targets =>
      simp only [parseCollection, encodeCollection, EdgeCollection.mode,
        EdgeCollection.labelText, EdgeCollection.direction,
        EdgeCollection.expectedTargetKind, EdgeCollection.targets]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      simp only [List.append_assoc]
      rw [parse_label_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      rw [parse_direction_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      rw [parse_kind_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      have parsedTargets :=
        parse_list_encode (encodeRef schema) (parseRef schema)
          (parse_ref_encode schema) targets []
      simp only [List.append_nil] at parsedTargets
      rw [parsedTargets]
      simp
      rfl
  | unordered label direction expectedKind targets =>
      simp only [parseCollection, encodeCollection, EdgeCollection.mode,
        EdgeCollection.labelText, EdgeCollection.direction,
        EdgeCollection.expectedTargetKind, EdgeCollection.targets]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      simp only [List.append_assoc]
      rw [parse_label_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      rw [parse_direction_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      rw [parse_kind_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      have parsedTargets :=
        parse_list_encode (encodeRef schema) (parseRef schema)
          (parse_ref_encode schema) targets []
      simp only [List.append_nil] at parsedTargets
      rw [parsedTargets]
      simp
      rfl

private theorem parse_node_encode
    (schema : GraphKindSchema) (node : CanonicalNode schema)
    (suffix : GraphBytes) :
    parseNode schema (encodeNode schema node ++ suffix) =
      .ok (node, suffix) := by
  cases node with
  | mk payload collections =>
      simp only [parseNode, encodeNode]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      have parsedCollections :=
        parse_list_encode (encodeCollection schema) (parseCollection schema)
          (parse_collection_encode schema) collections []
      simp only [List.append_nil] at parsedCollections
      rw [parsedCollections]
      simp [parseExactNat]
      rfl

private theorem parse_block_encode
    (schema : GraphKindSchema) (kind : schema.Kind)
    (block : CanonicalBlock schema kind) (suffix : GraphBytes) :
    parseBlock schema kind (encodeCanonicalBlock block ++ suffix) =
      .ok (block, suffix) := by
  cases block with
  | dagSingleton node =>
      simp only [parseBlock, encodeCanonicalBlock]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      have parsedNode := parse_node_encode schema node []
      simp only [List.append_nil] at parsedNode
      rw [parsedNode]
      simp
      rfl
  | cyclic nodes =>
      simp only [parseBlock, encodeCanonicalBlock]
      rw [read_tlv_encode]
      dsimp only [Bind.bind, Except.instMonad, Except.bind]
      have parsedNodes :=
        parse_list_encode (encodeNode schema) (parseNode schema)
          (parse_node_encode schema) nodes []
      simp only [List.append_nil] at parsedNodes
      rw [parsedNodes]
      simp
      rfl

theorem decode_encode_canonical_block
    (schema : GraphKindSchema) (kind : schema.Kind)
    (block : CanonicalBlock schema kind) :
    decodeCanonicalBlockDetailed schema kind
      (encodeCanonicalBlock block) = .ok block := by
  unfold decodeCanonicalBlockDetailed decodeCanonicalBlockPrefix
  have parsed := parse_block_encode schema kind block []
  simp only [List.append_nil] at parsed
  rw [parsed]

theorem encode_decode_canonical_block_prefix
    (accepted :
      decodeCanonicalBlockPrefix schema kind bytes =
        .ok (block, suffix)) :
    encodeCanonicalBlock block ++ suffix = bytes := by
  exact parse_block_decode schema kind accepted

theorem encode_decode_canonical_block
    (accepted :
      decodeCanonicalBlockDetailed schema kind bytes = .ok block) :
    encodeCanonicalBlock block = bytes := by
  unfold decodeCanonicalBlockDetailed at accepted
  cases parsed : decodeCanonicalBlockPrefix schema kind bytes with
  | error residue =>
      rw [parsed] at accepted
      contradiction
  | ok result =>
      cases result with
      | mk decoded suffix =>
          cases suffix with
          | nil =>
              rw [parsed] at accepted
              cases accepted
              simpa only [List.append_nil] using
                encode_decode_canonical_block_prefix parsed
          | cons first rest =>
              simp [parsed] at accepted

def constructiveBlockCodec
    (schema : GraphKindSchema) (kind : schema.Kind) :
    ExactCanonicalCodec (CanonicalBlock schema kind) GraphBytes where
  encode := encodeCanonicalBlock
  decode := fun bytes =>
    match decodeCanonicalBlockDetailed schema kind bytes with
    | .ok block => some block
    | .error _ => none
  decode_encode := by
    intro block
    simp [decode_encode_canonical_block schema kind block]
  encode_decode_canonical := by
    intro bytes block accepted
    cases decoded :
        decodeCanonicalBlockDetailed schema kind bytes with
    | error residue =>
        simp [decoded] at accepted
    | ok decodedBlock =>
        simp [decoded] at accepted
        cases accepted
        exact encode_decode_canonical_block decoded

structure GraphCodecContext where
  kindSchema : GraphKindSchema
  BlockWire : Type
  RootWire : Type
  blockBinding :
    ∀ kind,
      DigestBinding (kindSchema.toAddressKind kind) GraphBytes BlockWire
  blockWireAddress :
    ∀ kind,
      GraphBytes → GraphWireAddress (kindSchema.toAddressKind kind)
  blockWireAddressRefines :
    ∀ kind bytes,
      (blockWireAddress kind bytes).toAddress =
        (blockBinding kind).address bytes
  rootBinding : DigestBinding .implementation GraphBytes RootWire

structure GraphDigestInjective (context : GraphCodecContext) : Prop where
  block :
    ∀ kind,
      DigestInjectiveOnCanonicalRange (context.blockBinding kind)
  root : DigestInjectiveOnCanonicalRange context.rootBinding

structure RawIngestProfile (context : GraphCodecContext) where
  blockRuntimeCodec :
    ∀ kind,
      RuntimeCanonicalCodec
        (CanonicalBlock context.kindSchema kind) GraphBytes
  blockRuntimeRefines :
    ∀ kind,
      (blockRuntimeCodec kind).RefinesExact
        (constructiveBlockCodec context.kindSchema kind)
  blockStore :
    ∀ kind,
      AddressedStore
        (context.kindSchema.toAddressKind kind) GraphBytes

end Residua.RCC.Addressing.AddressedGraph.Foundation

namespace Residua.RCC.Addressing

export AddressedGraph.Foundation
  (GraphBytes GraphText GraphLabel GraphWireAddress GraphKindSchema
    BlockNodeAddress ExternalRef GraphRef
    EdgeDirection EdgeCollectionMode EdgeCollection GraphNode CanonicalNode
    CanonicalBlock CanonicalBlockForm BlockDecodeResidue
    encodeTypedAddress encodeCanonicalBlock decodeCanonicalBlockDetailed
    decode_encode_canonical_block encode_decode_canonical_block
    constructiveBlockCodec GraphCodecContext GraphDigestInjective
    RawIngestProfile)

end Residua.RCC.Addressing


import RCC.AddressedGraphClosure

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph.Closure

namespace Residua.RCC.Addressing.AddressedGraph.Closure.Tests

set_option maxRecDepth 8192

/-! AK-6A lawful raw-ingest fixtures.  No fixture chooses its own decoder. -/

inductive FixtureKind
  | syntax
  | judgment
  deriving DecidableEq, Repr

def fixtureKinds : List FixtureKind := [.syntax, .judgment]

def fixtureSchema : GraphKindSchema where
  Kind := FixtureKind
  decideKindEq := fun left right =>
    inferInstanceAs (Decidable (left = right))
  enumerate := fixtureKinds
  enumerateNoDuplicates := by
    intro leftIndex rightIndex leftBound rightBound equalKinds
    have leftCases : leftIndex = 0 ∨ leftIndex = 1 := by
      simp [fixtureKinds] at leftBound
      omega
    have rightCases : rightIndex = 0 ∨ rightIndex = 1 := by
      simp [fixtureKinds] at rightBound
      omega
    rcases leftCases with rfl | rfl <;>
      rcases rightCases with rfl | rfl <;>
      simp [fixtureKinds] at equalKinds ⊢
  enumerateComplete := by
    intro kind
    cases kind <;> simp [fixtureKinds]
  kindCode := fun
    | .syntax => 0
    | .judgment => 1
  kindCodeInjective := by
    intro left right equalCode
    cases left <;> cases right <;> simp_all
  toAddressKind := fun
    | .syntax => .syntax
    | .judgment => .judgment
  toAddressKindInjective := by
    intro left right equalKind
    cases left <;> cases right <;> simp_all

/-! The graph-kind index rejects judgment data at a syntax-only use site. -/
def syntaxKindConsumer
    (kind : fixtureSchema.Kind) (_ : kind = FixtureKind.syntax) :=
  kind

#check_failure
  syntaxKindConsumer FixtureKind.judgment rfl

def text (scalars : List Char) : GraphText := ⟨scalars⟩

theorem text_value_asString (scalars : List Char) :
    (text scalars).value = scalars.asString := by
  rfl

def exactFrame :
    ExactFrame GraphBytes (DigestPreimage GraphBytes) where
  encode := fun preimage => preimage
  encode_injective := fun equality => equality

/-!
The fixture digest is intentionally executable rather than postulated
injective.  A finite ASCII token alphabet gives every natural a prefix /
remainder cell.  The token decoder is a left inverse, while the UTF-8 lemma
below observes `GraphText.value` through its explicit byte representation.
-/
inductive DigestToken
  | prefix
  | remainder
  | separator
  | syntaxTag
  | judgmentTag
  | colon
  deriving DecidableEq

def digestTokenChar : DigestToken → Char
  | .prefix => 'q'
  | .remainder => 'r'
  | .separator => ';'
  | .syntaxTag => 's'
  | .judgmentTag => 'j'
  | .colon => ':'

def digestTokenByte : DigestToken → UInt8
  | .prefix => 113
  | .remainder => 114
  | .separator => 59
  | .syntaxTag => 115
  | .judgmentTag => 106
  | .colon => 58

theorem digest_token_utf8_flatMap : ∀ tokens : List DigestToken,
    (tokens.map digestTokenChar).flatMap String.utf8EncodeChar =
      tokens.map digestTokenByte := by
  intro tokens
  induction tokens with
  | nil => rfl
  | cons token rest inductionHypothesis =>
      cases token <;>
        simp [digestTokenChar, digestTokenByte, String.utf8EncodeChar,
          inductionHypothesis] <;> decide

theorem digest_token_toUTF8_data (tokens : List DigestToken) :
    (String.toUTF8 (tokens.map digestTokenChar).asString).data.toList =
      tokens.map digestTokenByte := by
  rw [← digest_token_utf8_flatMap tokens]
  first
  | rfl
  | (change
        (String.ofList (tokens.map digestTokenChar)).toByteArray.data.toList =
          _
     rw [String.toByteArray_ofList]
     simp [List.utf8Encode, List.toList_data_toByteArray])

def byteTokenCell (value : Nat) : List DigestToken :=
  List.replicate (value / 16) .prefix ++ [.separator] ++
    List.replicate (value % 16) .remainder ++ [.separator]

def decodePrefix : List DigestToken → Option (Nat × List DigestToken)
  | [] => none
  | .prefix :: rest =>
      match decodePrefix rest with
      | none => none
      | some (value, suffix) => some (value + 1, suffix)
  | .separator :: rest => some (0, rest)
  | _ => none

def decodeRemainder : List DigestToken → Option (Nat × List DigestToken)
  | [] => none
  | .remainder :: rest =>
      match decodeRemainder rest with
      | none => none
      | some (value, suffix) => some (value + 1, suffix)
  | .separator :: rest => some (0, rest)
  | _ => none

def decodeByteTokenCell (tokens : List DigestToken) :
    Option (Nat × List DigestToken) :=
  match decodePrefix tokens with
  | none => none
  | some (quotient, remainderTokens) =>
      match decodeRemainder remainderTokens with
      | none => none
      | some (remainder, suffix) =>
          some (remainder + quotient * 16, suffix)

theorem decode_replicate_prefix
    (count : Nat) (suffix : List DigestToken) :
    decodePrefix
        (List.replicate count DigestToken.prefix ++
          DigestToken.separator :: suffix) =
      some (count, suffix) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, List.append_assoc]
      simp [decodePrefix, inductionHypothesis]

theorem decode_replicate_remainder
    (count : Nat) (suffix : List DigestToken) :
    decodeRemainder
        (List.replicate count DigestToken.remainder ++
          DigestToken.separator :: suffix) =
      some (count, suffix) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [List.replicate_succ, List.append_assoc]
      simp [decodeRemainder, inductionHypothesis]

theorem decode_byte_token_cell (value : Nat) (suffix : List DigestToken) :
    decodeByteTokenCell (byteTokenCell value ++ suffix) =
      some (value, suffix) := by
  simp only [byteTokenCell, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append]
  have prefixDecoded :=
    decode_replicate_prefix (value / 16)
      (List.replicate (value % 16) DigestToken.remainder ++
        DigestToken.separator :: suffix)
  rw [decodeByteTokenCell, prefixDecoded]
  simp only
  rw [decode_replicate_remainder]
  congr 2
  simpa [Nat.mul_comm] using Nat.mod_add_div value 16

def byteTokens : GraphBytes → List DigestToken
  | [] => []
  | byte :: rest => byteTokenCell byte ++ byteTokens rest

theorem byte_tokens_injective :
    ∀ {left right}, byteTokens left = byteTokens right → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons value rest =>
          simp [byteTokens, byteTokenCell] at equal
  | cons value rest inductionHypothesis =>
      intro right equal
      cases right with
      | nil =>
          simp [byteTokens, byteTokenCell] at equal
      | cons other tail =>
          have decoded := congrArg decodeByteTokenCell equal
          simp only [byteTokens] at decoded
          rw [decode_byte_token_cell, decode_byte_token_cell] at decoded
          have pairEqual :
              (value, byteTokens rest) = (other, byteTokens tail) :=
            Option.some.inj decoded
          have valueEqual : value = other :=
            congrArg Prod.fst pairEqual
          have restEqual : byteTokens rest = byteTokens tail :=
            congrArg Prod.snd pairEqual
          cases valueEqual
          exact
            congrArg (List.cons value) (inductionHypothesis restEqual)

theorem digest_token_byte_injective
    {left right : DigestToken}
    (equalByte : digestTokenByte left = digestTokenByte right) :
    left = right := by
  cases left <;> cases right <;> simp [digestTokenByte] at equalByte ⊢

theorem digest_token_bytes_injective :
    ∀ {left right : List DigestToken},
      left.map digestTokenByte = right.map digestTokenByte → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right <;> simp_all
  | cons token rest inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp at equality
      | cons other tail =>
          simp only [List.map] at equality
          injection equality with headEquality tailEquality
          cases digest_token_byte_injective headEquality
          exact congrArg (List.cons token) (inductionHypothesis tailEquality)

def blockTokens (kind : FixtureKind) (bytes : GraphBytes) :
    List DigestToken :=
  (match kind with
    | .syntax => [.syntaxTag, .colon]
    | .judgment => [.judgmentTag, .colon]) ++
    byteTokens bytes

def byteScalars (bytes : GraphBytes) : List Char :=
  (byteTokens bytes).map digestTokenChar

def blockDomain : FixtureKind → GraphText
  | .syntax => text ['s']
  | .judgment => text ['j']

def blockDigest (kind : FixtureKind) (bytes : GraphBytes) : GraphText :=
  text ((blockTokens kind bytes).map digestTokenChar)

def blockBinding (kind : FixtureKind) :
    DigestBinding
      (fixtureSchema.toAddressKind kind)
      GraphBytes
      (DigestPreimage GraphBytes) where
  algorithm := ⟨"fixture"⟩
  domainQ := ⟨(blockDomain kind).value⟩
  schemaQ := ⟨"ak6-closure-fixture-v1"⟩
  frame := exactFrame
  hash := fun preimage =>
    ⟨(blockDigest kind preimage.canonicalBytes).value⟩

def blockWireAddress (kind : FixtureKind) (bytes : GraphBytes) :
    GraphWireAddress (fixtureSchema.toAddressKind kind) where
  algorithm := text ['f', 'i', 'x', 't', 'u', 'r', 'e']
  domainQ := blockDomain kind
  schemaQ :=
    text ['a', 'k', '6', '-', 'c', 'l', 'o', 's', 'u', 'r', 'e', '-',
      'f', 'i', 'x', 't', 'u', 'r', 'e', '-', 'v', '1']
  digest := blockDigest kind bytes

theorem block_wire_address_refines (kind : FixtureKind) (bytes : GraphBytes) :
    (blockWireAddress kind bytes).toAddress =
      (blockBinding kind).address bytes := by
  rfl

def rootBinding :
    DigestBinding .implementation GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"fixture"⟩
  domainQ := ⟨"ak6-closure-root"⟩
  schemaQ := ⟨"ak6-closure-root-v1"⟩
  frame := exactFrame
  hash := fun preimage =>
    ⟨(text ((byteTokens preimage.canonicalBytes).map digestTokenChar)).value⟩

def fixtureContext : GraphCodecContext where
  kindSchema := fixtureSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := blockBinding
  blockWireAddress := blockWireAddress
  blockWireAddressRefines := block_wire_address_refines
  rootBinding := rootBinding

theorem block_digest_injective (kind : FixtureKind) :
    DigestInjectiveOnCanonicalRange (blockBinding kind) := by
  intro left right equalDigest
  have equalString := congrArg Digest.value equalDigest
  simp only [blockBinding, DigestBinding.framedWire, DigestBinding.preimage,
    exactFrame, blockDigest] at equalString
  rw [text_value_asString, text_value_asString] at equalString
  have equalUTF8 := congrArg String.toUTF8 equalString
  have equalData :=
    congrArg (fun bytes : ByteArray => bytes.data.toList) equalUTF8
  change
    (String.toUTF8
        ((blockTokens kind left).map digestTokenChar).asString).data.toList =
      (String.toUTF8
        ((blockTokens kind right).map digestTokenChar).asString).data.toList
    at equalData
  rw [digest_token_toUTF8_data, digest_token_toUTF8_data] at equalData
  have equalTokens := digest_token_bytes_injective equalData
  cases kind <;> simp only [blockTokens] at equalTokens
  all_goals
    have equalByteTokens :
        byteTokens left = byteTokens right :=
      List.append_cancel_left equalTokens
    have equalBytes := byte_tokens_injective equalByteTokens
    cases equalBytes
    rfl

theorem root_digest_injective :
    DigestInjectiveOnCanonicalRange rootBinding := by
  intro left right equalDigest
  have equalString := congrArg Digest.value equalDigest
  simp only [rootBinding, DigestBinding.framedWire, DigestBinding.preimage,
    exactFrame] at equalString
  rw [text_value_asString, text_value_asString] at equalString
  have equalUTF8 := congrArg String.toUTF8 equalString
  have equalData :=
    congrArg (fun bytes : ByteArray => bytes.data.toList) equalUTF8
  change
    (String.toUTF8
        ((byteTokens left).map digestTokenChar).asString).data.toList =
      (String.toUTF8
        ((byteTokens right).map digestTokenChar).asString).data.toList
    at equalData
  rw [digest_token_toUTF8_data, digest_token_toUTF8_data] at equalData
  have equalTokens := digest_token_bytes_injective equalData
  have equalBytes := byte_tokens_injective equalTokens
  cases equalBytes
  rfl

def fixtureInjective : GraphDigestInjective fixtureContext where
  block := block_digest_injective
  root := root_digest_injective

def honestRuntimeCodec (kind : FixtureKind) :
    RuntimeCanonicalCodec (CanonicalBlock fixtureSchema kind) GraphBytes where
  encode := (constructiveBlockCodec fixtureSchema kind).encode
  decode := (constructiveBlockCodec fixtureSchema kind).decode

def honestRuntimeRefines (kind : FixtureKind) :
    (honestRuntimeCodec kind).RefinesExact
      (constructiveBlockCodec fixtureSchema kind) where
  encode_eq := rfl
  decode_eq := rfl

def canonicalStore
    (kind : FixtureKind)
    (blocks : List (CanonicalBlock fixtureSchema kind)) :
    AddressedStore (fixtureSchema.toAddressKind kind) GraphBytes :=
  blocks.foldl
    (fun store block =>
      let bytes := encodeCanonicalBlock block
      updateAddressedStore store ((blockBinding kind).address bytes) bytes)
    emptyAddressedStore

def ingestWith
    (syntaxStore : AddressedStore .syntax GraphBytes)
    (judgmentStore : AddressedStore .judgment GraphBytes) :
    RawIngestProfile fixtureContext where
  blockRuntimeCodec := honestRuntimeCodec
  blockRuntimeRefines := honestRuntimeRefines
  blockStore := fun
    | .syntax => syntaxStore
    | .judgment => judgmentStore

def canonicalDag (kind : FixtureKind) (payload : Nat) :
    CanonicalBlock fixtureSchema kind :=
  .dagSingleton { payload := payload, edgeCollections := [] }

def sourceCanonical : CanonicalBlock fixtureSchema .syntax :=
  canonicalDag .syntax 10

def targetCanonical : CanonicalBlock fixtureSchema .syntax :=
  canonicalDag .syntax 20

def wrongCanonical : CanonicalBlock fixtureSchema .syntax :=
  canonicalDag .syntax 21

def judgmentCanonical : CanonicalBlock fixtureSchema .judgment :=
  canonicalDag .judgment 30

def canonicalTwo : CanonicalBlock fixtureSchema .syntax :=
  .cyclic
    [{ payload := 40
       edgeCollections :=
         [.ordered (text ['n']) .outgoing .syntax [.local 1]] },
     { payload := 41
       edgeCollections :=
         [.ordered (text ['n']) .outgoing .syntax [.local 0]] }]

def sourceBytes : GraphBytes := encodeCanonicalBlock sourceCanonical
def targetBytes : GraphBytes := encodeCanonicalBlock targetCanonical
def wrongBytes : GraphBytes := encodeCanonicalBlock wrongCanonical
def malformedBytes : GraphBytes := [99, 0]

def keyFromBytes (kind : FixtureKind) (bytes : GraphBytes) :
    RawRegistryKey fixtureSchema kind :=
  ⟨blockWireAddress kind bytes⟩

def sourceKey : RawRegistryKey fixtureSchema .syntax :=
  keyFromBytes .syntax sourceBytes

def targetRefFromBytes (bytes : GraphBytes) :
    RawInRegistryRef fixtureSchema where
  kind := .syntax
  targetKey := keyFromBytes .syntax bytes
  rawTargetMemberIndex := 0

def sourceNodeFor (target : RawInRegistryRef fixtureSchema) :
    RawNode fixtureSchema where
  payload := 10
  edgeCollections :=
    [.ordered (text ['e']) .outgoing .syntax [.external target]]

def sourceEntryFor (target : RawInRegistryRef fixtureSchema) :
    RawBlockEntry fixtureSchema .syntax where
  claimedBlockQ := sourceKey.claimedBlockQ
  dependencyRank := 1
  candidate := .dagSingleton (sourceNodeFor target)

def rawGraphFor (target : RawInRegistryRef fixtureSchema) :
    RawRootedGraph fixtureSchema where
  blockRegistry := [⟨.syntax, sourceEntryFor target⟩]
  root :=
    { kind := .syntax
      targetKey := sourceKey
      rawTargetMemberIndex := 0 }

def sourceStore : AddressedStore .syntax GraphBytes :=
  canonicalStore .syntax [sourceCanonical]

def notFoundIngest : RawIngestProfile fixtureContext :=
  ingestWith sourceStore emptyAddressedStore

def rehashStore : AddressedStore .syntax GraphBytes :=
  updateAddressedStore sourceStore
    ((blockBinding .syntax).address targetBytes)
    wrongBytes

def rehashIngest : RawIngestProfile fixtureContext :=
  ingestWith rehashStore emptyAddressedStore

def decodeRefusingStore : AddressedStore .syntax GraphBytes :=
  updateAddressedStore sourceStore
    ((blockBinding .syntax).address malformedBytes)
    malformedBytes

def decodeRefusingIngest : RawIngestProfile fixtureContext :=
  ingestWith decodeRefusingStore emptyAddressedStore

def notFoundGraph : RawRootedGraph fixtureSchema :=
  rawGraphFor (targetRefFromBytes targetBytes)

def rehashMismatchGraph : RawRootedGraph fixtureSchema :=
  rawGraphFor (targetRefFromBytes targetBytes)

def decodeRefusedGraph : RawRootedGraph fixtureSchema :=
  rawGraphFor (targetRefFromBytes malformedBytes)

/-! Registry/block-form/connectivity fixtures share only public constructors. -/
def keyForBlock (kind : FixtureKind)
    (block : CanonicalBlock fixtureSchema kind) :
    RawRegistryKey fixtureSchema kind :=
  keyFromBytes kind (encodeCanonicalBlock block)

def refForBlock (kind : FixtureKind)
    (block : CanonicalBlock fixtureSchema kind) (index : Nat) :
    RawInRegistryRef fixtureSchema where
  kind := kind
  targetKey := keyForBlock kind block
  rawTargetMemberIndex := index

def rawEntryFor (kind : FixtureKind)
    (block : CanonicalBlock fixtureSchema kind)
    (rank : Nat)
    (candidate : RawBlockCandidate fixtureSchema kind) :
    RawBlockEntry fixtureSchema kind where
  claimedBlockQ := (keyForBlock kind block).claimedBlockQ
  dependencyRank := rank
  candidate := candidate

def wrappedEntry (kind : FixtureKind)
    (entry : RawBlockEntry fixtureSchema kind) :
    SomeRawBlockEntry fixtureSchema :=
  ⟨kind, entry⟩

def noReferenceNode (payload : Nat) : RawNode fixtureSchema :=
  { payload := payload, edgeCollections := [] }

def sourceNoReferenceEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 1
    (.dagSingleton (noReferenceNode 10))

def targetNoReferenceEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax targetCanonical 0
    (.dagSingleton (noReferenceNode 20))

def judgmentNoReferenceEntry : RawBlockEntry fixtureSchema .judgment :=
  rawEntryFor .judgment judgmentCanonical 0
    (.dagSingleton (noReferenceNode 30))

def sourceRoot : RawInRegistryRef fixtureSchema :=
  refForBlock .syntax sourceCanonical 0

def canonicalTwoRoot : RawInRegistryRef fixtureSchema :=
  refForBlock .syntax canonicalTwo 0

def exactFixtureIngest : RawIngestProfile fixtureContext :=
  ingestWith
    (canonicalStore .syntax [sourceCanonical, targetCanonical, canonicalTwo])
    (canonicalStore .judgment [judgmentCanonical])

def suppliedConnectivity
    (nodes : List (RawNode fixtureSchema)) :
    Option (ConnectivityCertificate nodes) :=
  match buildConnectivityCertificate nodes with
  | .ok certificate => some certificate
  | .error _ => none

def connectedRawNodes : List (RawNode fixtureSchema) :=
  [{ payload := 40
     edgeCollections :=
       [.ordered (text ['n']) .outgoing .syntax [.local 1]] },
   { payload := 41
     edgeCollections :=
       [.ordered (text ['n']) .outgoing .syntax [.local 0]] }]

def disconnectedRawNodes : List (RawNode fixtureSchema) :=
  [noReferenceNode 40, noReferenceNode 41]

def localOutOfBoundsNodes : List (RawNode fixtureSchema) :=
  [{ payload := 40
     edgeCollections :=
       [.ordered (text ['n']) .outgoing .syntax [.local 1]] }]

def emptyRegistryGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [], root := sourceRoot }

def duplicateRegistryGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax sourceNoReferenceEntry,
       wrappedEntry .syntax sourceNoReferenceEntry]
    root := sourceRoot }

def rootNotInRegistryGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax targetNoReferenceEntry]
    root := sourceRoot }

def unreachableRegistryGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax sourceNoReferenceEntry,
       wrappedEntry .judgment judgmentNoReferenceEntry]
    root := sourceRoot }

def localDagEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 0
    (.dagSingleton
      { payload := 10
        edgeCollections :=
          [.ordered (text ['n']) .outgoing .syntax [.local 0]] })

def localRefInDagGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax localDagEntry]
    root := sourceRoot }

def emptyCyclicEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0 (.cyclic [] none)

def emptyCyclicGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax emptyCyclicEntry]
    root := canonicalTwoRoot }

def connectedMissingCertificateEntry :
    RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0 (.cyclic connectedRawNodes none)

def connectedMissingCertificateGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax connectedMissingCertificateEntry]
    root := canonicalTwoRoot }

def disconnectedCyclicEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0 (.cyclic disconnectedRawNodes none)

def disconnectedCyclicGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax disconnectedCyclicEntry]
    root := canonicalTwoRoot }

def localOutOfBoundsEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0
    (.cyclic localOutOfBoundsNodes
      (suppliedConnectivity localOutOfBoundsNodes))

def localOutOfBoundsGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax localOutOfBoundsEntry]
    root := canonicalTwoRoot }

def localKindMismatchNodes : List (RawNode fixtureSchema) :=
  [{ payload := 40
     edgeCollections :=
       [.ordered (text ['n']) .outgoing .judgment [.local 1]] },
   { payload := 41
     edgeCollections :=
       [.ordered (text ['n']) .outgoing .judgment [.local 0]] }]

def localKindMismatchEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0
    (.cyclic localKindMismatchNodes
      (suppliedConnectivity localKindMismatchNodes))

def localKindMismatchGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax localKindMismatchEntry]
    root := canonicalTwoRoot }

def judgmentTargetRef : RawInRegistryRef fixtureSchema :=
  refForBlock .judgment judgmentCanonical 0

def targetKindMismatchSourceEntry :
    RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 1
    (.dagSingleton
      { payload := 10
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external judgmentTargetRef]] })

def targetKindMismatchGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax targetKindMismatchSourceEntry,
       wrappedEntry .judgment judgmentNoReferenceEntry]
    root := sourceRoot }

/-! Final whole-closure fixtures: membership, both bounds, rank, and GREEN. -/
def exactSourceTargetIngest : RawIngestProfile fixtureContext :=
  ingestWith
    (canonicalStore .syntax [sourceCanonical, targetCanonical])
    emptyAddressedStore

def resolvedButUnregisteredGraph : RawRootedGraph fixtureSchema :=
  rawGraphFor (refForBlock .syntax targetCanonical 0)

def grandchildRef : RawInRegistryRef fixtureSchema :=
  refForBlock .syntax wrongCanonical 0

def childWithDanglingGrandchildEntry :
    RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax targetCanonical 1
    (.dagSingleton
      { payload := 20
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external grandchildRef]] })

def sourceToChildEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 2
    (.dagSingleton
      { payload := 10
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external (refForBlock .syntax targetCanonical 0)]] })

def danglingGrandchildGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax sourceToChildEntry,
       wrappedEntry .syntax childWithDanglingGrandchildEntry]
    root := sourceRoot }

def externalDagChainGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax sourceToChildEntry,
       wrappedEntry .syntax targetNoReferenceEntry]
    root := sourceRoot }

def rawOneResolvedTwoEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0
    (.dagSingleton (noReferenceNode 40))

def rawOneResolvedTwoGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax rawOneResolvedTwoEntry]
    root := refForBlock .syntax canonicalTwo 1 }

def rawTwoResolvedOneEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 0
    (.cyclic connectedRawNodes (suppliedConnectivity connectedRawNodes))

def rawTwoResolvedOneGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax rawTwoResolvedOneEntry]
    root := refForBlock .syntax sourceCanonical 1 }

def selfReferenceEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 0
    (.dagSingleton
      { payload := 10
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external sourceRoot]] })

def sameBlockExternalSelfReferenceGraph :
    RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax selfReferenceEntry]
    root := sourceRoot }

def cycleAEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax sourceCanonical 1
    (.dagSingleton
      { payload := 10
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external (refForBlock .syntax targetCanonical 0)]] })

def cycleBEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax targetCanonical 0
    (.dagSingleton
      { payload := 20
        edgeCollections :=
          [.ordered (text ['e']) .outgoing .syntax
            [.external sourceRoot]] })

def twoBlockExternalCycleGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry :=
      [wrappedEntry .syntax cycleAEntry,
       wrappedEntry .syntax cycleBEntry]
    root := sourceRoot }

def acceptedTwoTwoEntry : RawBlockEntry fixtureSchema .syntax :=
  rawEntryFor .syntax canonicalTwo 0
    (.cyclic connectedRawNodes (suppliedConnectivity connectedRawNodes))

def acceptedTwoTwoGraph : RawRootedGraph fixtureSchema :=
  { blockRegistry := [wrappedEntry .syntax acceptedTwoTwoEntry]
    root := refForBlock .syntax canonicalTwo 1 }

def acceptedTwoTwoIngest : RawIngestProfile fixtureContext :=
  ingestWith (canonicalStore .syntax [canonicalTwo]) emptyAddressedStore

def validationSucceeded :
    Except GraphValidationResidue
      (StructurallyClosedRootedGraph fixtureContext acceptedTwoTwoIngest) →
      Bool
  | .ok _ => true
  | .error _ => false

def externalDagValidationSucceeded :
    Except GraphValidationResidue
      (StructurallyClosedRootedGraph fixtureContext
        exactSourceTargetIngest) →
      Bool
  | .ok _ => true
  | .error _ => false

/-! The pure AK-5 adapter is exhaustive, including its defensive branch. -/
theorem map_external_resolved :
    mapExternalResolution (StoreResolveResult.resolved 7) =
      (Except.ok 7 : Except GraphValidationResidue Nat) := by
  rfl

theorem map_external_not_found :
    mapExternalResolution (StoreResolveResult.notFound : StoreResolveResult Nat) =
      .error .externalBlockNotFound := by
  rfl

theorem map_external_rehash_mismatch :
    mapExternalResolution
        (StoreResolveResult.rehashMismatch : StoreResolveResult Nat) =
      .error .externalRehashMismatch := by
  rfl

theorem map_external_decode_refused :
    mapExternalResolution
        (StoreResolveResult.decodeRefused : StoreResolveResult Nat) =
      .error .externalDecodeRefused := by
  rfl

theorem map_external_noncanonical_bytes :
    mapExternalResolution
        (StoreResolveResult.noncanonicalBytes : StoreResolveResult Nat) =
      .error .externalNoncanonicalBytes := by
  rfl

/-!
The exact runtime-refinement profile rules out the defensive noncanonical
branch.  No malicious non-refining codec is installed merely for coverage.
-/
theorem fixture_noncanonical_unreachable
    (ingest : RawIngestProfile fixtureContext)
    (kind : fixtureContext.kindSchema.Kind)
    (requested :
      Address (fixtureContext.kindSchema.toAddressKind kind)) :
    resolveAddressed
        (fixtureContext.blockBinding kind)
        (ingest.blockRuntimeCodec kind)
        (ingest.blockStore kind)
        requested ≠ .noncanonicalBytes :=
  raw_ingest_noncanonical_unreachable fixtureContext ingest kind requested

/-!
These are lawful concrete validator executions.  The raw target is absent
from the registry on purpose: resolution precedes typed registry membership,
so the exact AK-5 failure must be observable first.
-/
theorem validator_maps_not_found :
    validateRawRootedGraph
        fixtureContext fixtureInjective notFoundIngest notFoundGraph =
      .error .externalBlockNotFound := by
  rfl

theorem validator_maps_rehash_mismatch :
    validateRawRootedGraph
        fixtureContext fixtureInjective rehashIngest rehashMismatchGraph =
      .error .externalRehashMismatch := by
  rfl

theorem validator_maps_decode_refused :
    validateRawRootedGraph
        fixtureContext fixtureInjective decodeRefusingIngest decodeRefusedGraph =
      .error .externalDecodeRefused := by
  rfl

/-! Registry checks are executable and precede all lower validation phases. -/
theorem validator_refuses_empty_registry :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest emptyRegistryGraph =
      .error .emptyRegistry := by
  rfl

theorem validator_refuses_duplicate_typed_key :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest duplicateRegistryGraph =
      .error .duplicateBlockKey := by
  rfl

theorem validator_refuses_missing_root :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest rootNotInRegistryGraph =
      .error .rootNotInRegistry := by
  rfl

theorem validator_refuses_unreachable_registry_block :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest unreachableRegistryGraph =
      .error .unreachableRegistryBlock := by
  rfl

/-! Block form and local selectors are validated on the concrete candidates. -/
theorem validator_refuses_local_reference_in_dag :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest localRefInDagGraph =
      .error .localRefInDag := by
  rfl

theorem validator_refuses_empty_cyclic_block :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest emptyCyclicGraph =
      .error .emptyCyclicBlock := by
  rfl

/-!
Computed connectivity runs before supplied provenance: a connected block with
no supplied certificate reaches the missing-evidence residue, while a
disconnected block is refused first.
-/
theorem validator_requires_supplied_connectivity :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest
          connectedMissingCertificateGraph =
      .error .connectivityCertificateMissing := by
  rfl

theorem validator_computes_connectivity_before_evidence :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest disconnectedCyclicGraph =
      .error .localConnectivityRefused := by
  rfl

theorem validator_refuses_local_index_out_of_bounds :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest localOutOfBoundsGraph =
      .error .localIndexOutOfBounds := by
  rfl

theorem validator_refuses_local_expected_kind_mismatch :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest
          localKindMismatchGraph =
      .error .targetKindMismatch := by
  rfl

/-!
The target exists in the registry and exact store.  Its wrong kind is still
refused before AK-5 resolution or any later membership/bound check.
-/
theorem validator_checks_target_kind_first :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactFixtureIngest targetKindMismatchGraph =
      .error .targetKindMismatch := by
  rfl

/-! A successful AK-5 lookup is not a substitute for registry membership. -/
theorem validator_refuses_resolved_unregistered_target :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          resolvedButUnregisteredGraph =
      .error .externalTargetNotInRegistry := by
  rfl

/-! The one-hop and transitive dangling cases both remain AK-5 not-found. -/
theorem validator_refuses_dangling_child :
    validateRawRootedGraph
        fixtureContext fixtureInjective notFoundIngest notFoundGraph =
      .error .externalBlockNotFound := by
  rfl

theorem validator_refuses_dangling_grandchild :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          danglingGrandchildGraph =
      .error .externalBlockNotFound := by
  rfl

/-! The raw and AK-5 canonical selector bounds are independently executable. -/
theorem validator_refuses_raw_one_resolved_two :
    validateRawRootedGraph
        fixtureContext fixtureInjective acceptedTwoTwoIngest
          rawOneResolvedTwoGraph =
      .error .rawTargetMemberIndexOutOfBounds := by
  rfl

theorem validator_refuses_raw_two_resolved_one :
    validateRawRootedGraph
        fixtureContext fixtureInjective
          (ingestWith (canonicalStore .syntax [sourceCanonical])
            emptyAddressedStore)
          rawTwoResolvedOneGraph =
      .error .resolvedCanonicalMemberIndexOutOfBounds := by
  rfl

/-! External ownership dependencies must strictly descend across blocks. -/
theorem validator_refuses_same_block_external_self_reference :
    validateRawRootedGraph
        fixtureContext fixtureInjective
          (ingestWith (canonicalStore .syntax [sourceCanonical])
            emptyAddressedStore)
          sameBlockExternalSelfReferenceGraph =
      .error .crossBlockRankNotStrict := by
  rfl

theorem validator_refuses_two_block_external_cycle :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          twoBlockExternalCycleGraph =
      .error .crossBlockRankNotStrict := by
  rfl

/-!
The corrected cycle is one addressed block with distinct payloads, two
bounded local selectors, supplied provenance, and independently recomputed
connectivity.
-/
theorem validator_accepts_distinct_payload_two_node_local_cycle :
    validationSucceeded
      (validateRawRootedGraph
        fixtureContext fixtureInjective acceptedTwoTwoIngest acceptedTwoTwoGraph) =
      true := by
  rfl

theorem validator_accepts_external_dag_chain :
    externalDagValidationSucceeded
      (validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          externalDagChainGraph) =
      true := by
  rfl

def externalDagClosed :
    StructurallyClosedRootedGraph fixtureContext exactSourceTargetIngest :=
  match accepted :
      validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          externalDagChainGraph with
  | .ok closed => closed
  | .error residue => by
      have succeeded := validator_accepts_external_dag_chain
      rw [accepted] at succeeded
      simp [externalDagValidationSucceeded] at succeeded

theorem external_dag_closed_is_evaluator_result :
    validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          externalDagChainGraph =
      .ok externalDagClosed := by
  rfl

theorem external_dag_chain_exports_resolved_occurrence :
    ∃ closed :
        StructurallyClosedRootedGraph fixtureContext exactSourceTargetIngest,
      validateRawRootedGraph
          fixtureContext fixtureInjective exactSourceTargetIngest
            externalDagChainGraph =
        .ok closed ∧
      ∃ occurs :
          RawReferenceOccurs closed.rawGraph
            (refForBlock .syntax targetCanonical 0),
        let evidence :=
          closed.resolvedTarget
            (refForBlock .syntax targetCanonical 0) occurs
        evidence.target.targetEntryMember.wrapped ∈
            closed.rawGraph.blockRegistry ∧
          evidence.target.targetEntry.claimedBlockQ =
            (refForBlock .syntax targetCanonical 0).targetKey.claimedBlockQ ∧
          RawTargetMemberBound evidence.target ∧
          resolveAddressed
              (fixtureContext.blockBinding
                (refForBlock .syntax targetCanonical 0).kind)
              (exactSourceTargetIngest.blockRuntimeCodec
                (refForBlock .syntax targetCanonical 0).kind)
              (exactSourceTargetIngest.blockStore
                (refForBlock .syntax targetCanonical 0).kind)
              ((refForBlock .syntax targetCanonical 0).targetKey.claimedBlockQ.toAddress) =
            .resolved evidence.resolved.canonicalBlock ∧
          (refForBlock .syntax targetCanonical 0).rawTargetMemberIndex <
            evidence.resolved.canonicalBlock.nodes.length := by
  have occurs :
      RawReferenceOccurs externalDagClosed.rawGraph
        (refForBlock .syntax targetCanonical 0) := by
    change
      (refForBlock .syntax targetCanonical 0) ∈
        [refForBlock .syntax targetCanonical 0]
    simp
  let evidence :=
    externalDagClosed.resolvedTarget
      (refForBlock .syntax targetCanonical 0) occurs
  exact
    ⟨externalDagClosed, external_dag_closed_is_evaluator_result,
      occurs,
      evidence.target.targetEntryMember.wrappedMember,
      evidence.target.targetEntryMember.keyEq,
      evidence.rawBound,
      evidence.resolved.resolvedByAK5,
      evidence.resolved.resolvedCanonicalIndexBound⟩

/-! The closed carrier exports every proof used by downstream AK-6B. -/
def closed_carrier_selector_contract
    {context : GraphCodecContext} {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (ref : RawInRegistryRef context.kindSchema)
    (occurs : RawReferenceOccurs closed.rawGraph ref) :
    ResolvedTargetEvidence context ingest closed.rawGraph ref :=
  closed.resolvedTarget ref occurs

theorem closed_root_retains_both_bounds
    {context : GraphCodecContext} {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    RawTargetMemberBound closed.rootMember ∧
      closed.rawGraph.root.rawTargetMemberIndex <
      closed.rootResolved.canonicalBlock.nodes.length :=
  ⟨closed.rootRawBound, closed.rootResolved.resolvedCanonicalIndexBound⟩

theorem accepted_cycle_exposes_both_root_bounds :
    ∃ closed :
        StructurallyClosedRootedGraph fixtureContext acceptedTwoTwoIngest,
      validateRawRootedGraph
          fixtureContext fixtureInjective acceptedTwoTwoIngest
            acceptedTwoTwoGraph =
        .ok closed ∧
      RawTargetMemberBound closed.rootMember ∧
      closed.rawGraph.root.rawTargetMemberIndex <
        closed.rootResolved.canonicalBlock.nodes.length := by
  cases accepted :
      validateRawRootedGraph
        fixtureContext fixtureInjective acceptedTwoTwoIngest
          acceptedTwoTwoGraph with
  | error residue =>
      have succeeded :=
        validator_accepts_distinct_payload_two_node_local_cycle
      rw [accepted] at succeeded
      simp [validationSucceeded] at succeeded
  | ok closed =>
      exact
        ⟨closed, rfl, closed.rootRawBound,
          closed.rootResolved.resolvedCanonicalIndexBound⟩

theorem resolved_target_retains_ak5_contract
    {context : GraphCodecContext} {ingest : RawIngestProfile context}
    {ref : RawInRegistryRef context.kindSchema}
    (target : ResolvedRawTarget context ingest ref) :
    resolveAddressed
        (context.blockBinding ref.kind)
        (ingest.blockRuntimeCodec ref.kind)
        (ingest.blockStore ref.kind)
        ref.targetKey.claimedBlockQ.toAddress =
        .resolved target.canonicalBlock ∧
      ref.rawTargetMemberIndex < target.canonicalBlock.nodes.length :=
  ⟨target.resolvedByAK5, target.resolvedCanonicalIndexBound⟩

theorem closed_graph_global_controls
    {context : GraphCodecContext} {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    AllLocalReferencesBoundAndTyped closed.rawGraph ∧
      AllCyclicBlocksComputedConnected closed.rawGraph ∧
      AllCrossBlockRanksStrict closed.rawGraph ∧
      EveryRegistryBlockReachable closed.rawGraph :=
  ⟨closed.localBoundsAndKinds, closed.computedConnectivity, closed.strictRank,
    closed.reachable⟩

/-! Scoped toy digest countermodel; no claim is made about a real digest. -/
theorem toy_successor_self_hash_contradiction (left right : Nat)
    (leftEquation : left = Nat.succ right)
    (rightEquation : right = Nat.succ left) :
    False := by
  omega

#print axioms fixture_noncanonical_unreachable
#print axioms fixtureInjective
#print axioms validator_maps_not_found
#print axioms validator_maps_rehash_mismatch
#print axioms validator_maps_decode_refused
#print axioms validator_requires_supplied_connectivity
#print axioms validator_computes_connectivity_before_evidence
#print axioms validator_checks_target_kind_first
#print axioms validator_refuses_raw_one_resolved_two
#print axioms validator_refuses_raw_two_resolved_one
#print axioms validator_refuses_two_block_external_cycle
#print axioms validator_accepts_distinct_payload_two_node_local_cycle
#print axioms validator_accepts_external_dag_chain
#print axioms external_dag_chain_exports_resolved_occurrence
#print axioms accepted_cycle_exposes_both_root_bounds
#print axioms closed_carrier_selector_contract
#print axioms closed_root_retains_both_bounds
#print axioms resolved_target_retains_ak5_contract
#print axioms closed_graph_global_controls
#print axioms toy_successor_self_hash_contradiction
#print axioms validateRawRootedGraph

end Residua.RCC.Addressing.AddressedGraph.Closure.Tests


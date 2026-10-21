/-!
# SHA-256 in pure Lean 4 (no Mathlib)

A concrete, computable SHA-256 used by the slot_eval runtime oracle for
`Expr.contentHash` (#1653 carve 1). This is a RUNTIME hash (the exe computes
the exact digest the wasm engine produces), NOT a theorem-grade model — the
repo's cryptographic-collision stance lives in `Residua.Exe.ContentHash.lean`
(`opaque sha256_hex`). Nothing here is proven about collision-resistance; the
function is trusted lowering, exactly like the rest of the compiled evaluator.

Every definition is structural or fuel-bounded recursion (no `partial`, no
`termination_by`), so the kernel evaluates a digest by reduction alone:
`sha256Hex_empty` / `sha256Hex_abc` below are proved by `decide`, never
`native_decide` (L-H, #6073). Collision-resistance is still not a theorem here.

Standard FIPS 180-4. Verified locally against the known-answer vectors
`sha256("") = e3b0c4...`, `sha256("abc") = ba7816bf...`, and against the wasm
engine's `contentHash(42) = sha256("Num(float:42.0)")`.
-/

namespace Residua.SHA256

/-- Rotate right by `n` (UInt32 shift amount). -/
def rotr (n : UInt32) (x : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< ((32 : UInt32) - n))

/-- Schedule σ0. -/
def s0 (x : UInt32) : UInt32 := rotr 7 x ^^^ rotr 18 x ^^^ (x >>> (3 : UInt32))
/-- Schedule σ1. -/
def s1 (x : UInt32) : UInt32 := rotr 17 x ^^^ rotr 19 x ^^^ (x >>> (10 : UInt32))
/-- Compression Σ0. -/
def bigS0 (x : UInt32) : UInt32 := rotr 2 x ^^^ rotr 13 x ^^^ rotr 22 x
/-- Compression Σ1. -/
def bigS1 (x : UInt32) : UInt32 := rotr 6 x ^^^ rotr 11 x ^^^ rotr 25 x
/-- Ch. -/
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)
/-- Maj. -/
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The 64 round constants. -/
def k : Array UInt32 :=
  #[ (0x428a2f98 : UInt32), 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
   , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
   , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
   , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
   , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
   , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
   , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
   , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- Initial hash values. -/
def hInit : Array UInt32 :=
  #[ (0x6a09e667 : UInt32), 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
   , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-- Big-endian UInt32 from four bytes. -/
def u32be (b0 b1 b2 b3 : UInt8) : UInt32 :=
  ((b0.toUInt32 <<< (24 : UInt32)) ||| (b1.toUInt32 <<< (16 : UInt32))
    ||| (b2.toUInt32 <<< (8 : UInt32)) ||| b3.toUInt32)

/-- First 16 schedule words from a 64-byte block (length 64): big-endian, four
    bytes per word. Counts down 16 words consuming 4 bytes each. -/
def blockWordsAux : Nat → List UInt8 → Array UInt32 → Array UInt32
  | 0, _, acc => acc
  | n + 1, b0 :: b1 :: b2 :: b3 :: rest, acc =>
      blockWordsAux n rest (acc.push (u32be b0 b1 b2 b3))
  | _ + 1, _, acc => acc

def blockWords (block : List UInt8) : Array UInt32 := blockWordsAux 16 block #[]

/-- Extend the 16 seed words to the full 64-entry message schedule.
    Structural recursion on a fuel of `64 - i` (the exact number of
    remaining steps), not well-founded recursion: a `termination_by`
    definition compiles through `WellFounded.fix`, which the kernel cannot
    unfold, so `decide`/`rfl` on a digest got stuck here (#6073 L-H,
    `[rcic_da_sha256_not_kernel_reducible_OPEN]`). Same values on every
    input. -/
def extendAux : Nat → Array UInt32 → Nat → Array UInt32
  | 0, w, _ => w
  | fuel + 1, w, i =>
    if i ≥ 64 then w
    else
      let wi := s1 (w.getD (i - 2) 0) + w.getD (i - 7) 0 + s0 (w.getD (i - 15) 0) + w.getD (i - 16) 0
      extendAux fuel (w.push wi) (i + 1)

def extend (w : Array UInt32) (i : Nat) : Array UInt32 := extendAux (64 - i) w i

/-- One compression pass over the 64 rounds; folds the working state into hash.
    Fuel-structural for the same reason as `extend`. -/
def compressAux (w : Array UInt32) (hash : Array UInt32) :
    Nat → Nat → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → Array UInt32
  | 0, _, a, b, c, d, e, f, g, h =>
    hash.set! 0 (hash.getD 0 0 + a)
      |>.set! 1 (hash.getD 1 0 + b)
      |>.set! 2 (hash.getD 2 0 + c)
      |>.set! 3 (hash.getD 3 0 + d)
      |>.set! 4 (hash.getD 4 0 + e)
      |>.set! 5 (hash.getD 5 0 + f)
      |>.set! 6 (hash.getD 6 0 + g)
      |>.set! 7 (hash.getD 7 0 + h)
  | fuel + 1, i, a, b, c, d, e, f, g, h =>
    if i ≥ 64 then
      hash.set! 0 (hash.getD 0 0 + a)
        |>.set! 1 (hash.getD 1 0 + b)
        |>.set! 2 (hash.getD 2 0 + c)
        |>.set! 3 (hash.getD 3 0 + d)
        |>.set! 4 (hash.getD 4 0 + e)
        |>.set! 5 (hash.getD 5 0 + f)
        |>.set! 6 (hash.getD 6 0 + g)
        |>.set! 7 (hash.getD 7 0 + h)
    else
      let t1 := h + bigS1 e + ch e f g + k.getD i 0 + w.getD i 0
      let t2 := bigS0 a + maj a b c
      compressAux w hash fuel (i + 1) (t1 + t2) a b c (d + t1) e f g

def compress (w : Array UInt32) (hash : Array UInt32)
    (i : Nat) (a b c d e f g h : UInt32) : Array UInt32 :=
  compressAux w hash (64 - i) i a b c d e f g h

/-- Run compression over one 64-byte block, updating the running hash. -/
def processBlock (hash : Array UInt32) (block : List UInt8) : Array UInt32 :=
  let w := extend (blockWords block) 16
  compress w hash 0
    (hash.getD 0 0) (hash.getD 1 0) (hash.getD 2 0) (hash.getD 3 0)
    (hash.getD 4 0) (hash.getD 5 0) (hash.getD 6 0) (hash.getD 7 0)

/-- Fold compression over all 64-byte blocks (structural on the list). -/
def processBlocks (blocks : List (List UInt8)) (hash : Array UInt32) : Array UInt32 :=
  match blocks with
  | [] => hash
  | block :: rest => processBlocks rest (processBlock hash block)

/-- The 8-byte big-endian encoding of a bit length (Nat). -/
def lengthBytes (bitLen : Nat) : List UInt8 :=
  let b (i : Nat) : UInt8 := ((bitLen >>> (i * 8)) &&& 0xff).toUInt8
  [ b 7, b 6, b 5, b 4, b 3, b 2, b 1, b 0 ]

/-- SHA-256 padding: 0x80, zeros to ≡56 mod 64, then 8-byte big-endian bit length. -/
def pad (msg : List UInt8) : List UInt8 :=
  let bitLen := msg.length * 8
  let withMarker := msg ++ [0x80]
  -- (#3115) integer-correct modular padding: Nat subtraction truncates, so
  -- `56 - r` underflows to 0 for r ∈ {57..63} (message len%64 ∈ {56..62}) and
  -- the length field landed off-grid — sha256Hex was NOT SHA-256 on that
  -- 1/64 residue class. Add the modulus before subtracting.
  let zeroCount := (56 + 64 - (withMarker.length % 64)) % 64
  withMarker ++ (List.replicate zeroCount 0) ++ lengthBytes bitLen

/-- Split a message into 64-byte blocks. Structural on a fuel of `xs.length`:
    every step consumes at least one byte, so the fuel never runs out before
    the list does, and the result equals the former `partial` definition on
    every input. (`partial def` is opaque to the kernel and to the logic;
    nothing about `sha256Hex` was provable while it was one.) -/
def chunk64Aux : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | fuel + 1, xs =>
    match xs with
    | [] => []
    | _ => xs.take 64 :: chunk64Aux fuel (xs.drop 64)

def chunk64 (xs : List UInt8) : List (List UInt8) := chunk64Aux xs.length xs

/-- Lowercase hex for a single nibble. -/
def hexDigit (n : UInt8) : String :=
  if n < 10 then toString n.toNat
  else match n with
    | 10 => "a" | 11 => "b" | 12 => "c" | 13 => "d" | 14 => "e" | _ => "f"

/-- Lowercase hex for a single byte. -/
def hexByte (b : UInt8) : String :=
  hexDigit (b >>> (4 : UInt8)) ++ hexDigit (b &&& 0x0f)

/-- UTF-8 bytes of a string as a list, by structure projection only.
    `ByteArray.toList` is well-founded recursion (`termination_by bs.size - i`):
    the elaborator never unfolds it, the kernel only through `Acc` proofs.
    `String.toUTF8 s = ⟨⟨s.data.flatMap utf8EncodeChar⟩⟩` is structural, so this
    path reduces under `decide`. Same bytes, same order. -/
def utf8Bytes (s : String) : List UInt8 :=
  match s.toUTF8 with
  | ⟨⟨bytes⟩⟩ => bytes

/-- SHA-256 of a string's UTF-8 bytes, returned as 64-char lowercase hex. -/
def sha256Hex (input : String) : String :=
  let msg := utf8Bytes input
  let padded := pad msg
  let blocks := chunk64 padded
  let hash := processBlocks blocks hInit
  let words :=
    hash.getD 0 0 :: hash.getD 1 0 :: hash.getD 2 0 :: hash.getD 3 0 ::
    hash.getD 4 0 :: hash.getD 5 0 :: hash.getD 6 0 :: hash.getD 7 0 :: []
  let bytesBE : List UInt8 :=
    words.flatMap (fun w =>
      [ (w >>> (24 : UInt32)).toUInt8, (w >>> (16 : UInt32)).toUInt8
      , (w >>> (8 : UInt32)).toUInt8, w.toUInt8 ])
  String.join (bytesBE.map hexByte)

/-! ## Kernel-reducibility seal (L-H)

`chunk64` was `partial` (opaque to the kernel) and `extend` / `compress` /
`processBlocks` were `termination_by` (well-founded: irreducible to the
elaborator, `Acc`-unfolding in the kernel). All four are now structural or
fuel-bounded and the byte extraction is a projection, so a digest equation is
settled by reduction: `decide` evaluates `sha256Hex` and the kernel re-checks
`of_decide_eq_true (Eq.refl true)`. No `native_decide`, no `Lean.ofReduceBool`.
If any step regresses to an opaque or well-founded form these theorems stop
elaborating — that is the bite. Vectors are FIPS 180-4 external truth. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha256Hex_empty :
    sha256Hex "" = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sha256Hex_abc :
    sha256Hex "abc" = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" := by
  decide

end Residua.SHA256

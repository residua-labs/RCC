import RCC.Support.PatchFabricMWE
import Lean.Elab.Command
import Lean.Modifiers
import Lean.Util.CollectAxioms

/-!
# ResiduaRCCProofTermCompiler — L2 seed: Residua.RCC.* theorem → SCMExpr

Bulk lean→scm emission of **every** Residua.RCC theorem's declaration type + proof
term as content-addressed scm records (the C2 elaborated-proof pattern, generalized).

This is the stage-3 / formal-full path for RCC — not the bridge runtime decision
slice. `closure_claim = 0` until every theorem is either emit_ok or a **named**
outside-fragment refuse (no silent drop).

Expr subset v1: C2 subset + lit / letE / mdata-strip / proj.
Unsupported constructs refuse with `unsupportedExpr` residue.
-/

open Lean Lean.Elab Lean.Elab.Command

namespace Residua.RCC.ProofTerm

open Residua.Algorithms.PatchFabric

inductive CompileError where
  | unsafeSCMString (value : String)
  | unstableConstant (name : Name)
  | looseBVar (index depth : Nat)
  | unknownLevelParam (name : Name)
  | unsupportedLevel (kind : String)
  | unsupportedExpr (kind : String)
  | sorryProof
  | axiomFloor (axioms : List Name)
  deriving Repr, Inhabited

structure CompileContext where
  levelParams : List Name
  binderDepth : Nat := 0
  deriving Inhabited

instance : Inhabited SCMExpr := ⟨.int 0⟩

def unsafeSCMChar (c : Char) : Bool :=
  c == '"' || c == '\\' || c.toNat < 0x20 || c.toNat == 0x7f

def mkSafeSCMStr (value : String) : Except CompileError SCMExpr :=
  if value.toList.any unsafeSCMChar then
    .error (.unsafeSCMString value)
  else
    .ok (.str value)

def validateStableConstName (name : Name) : Except CompileError Unit :=
  if isPrivateName name || name.isInternalDetail then
    .error (.unstableConstant name)
  else
    .ok ()

def levelParamIndex (needle : Name) : List Name → Nat → Option Nat
  | [], _ => none
  | name :: names, index =>
      if name == needle then some index else levelParamIndex needle names (index + 1)

def compileLevel (params : List Name) : Level → Except CompileError SCMExpr
  | .zero => do
      return .record [("level_op", ← mkSafeSCMStr "zero")]
  | .succ level => do
      return .record [
        ("level_op", ← mkSafeSCMStr "succ"),
        ("of", ← compileLevel params level)
      ]
  | .max left right => do
      return .record [
        ("level_op", ← mkSafeSCMStr "max"),
        ("left", ← compileLevel params left),
        ("right", ← compileLevel params right)
      ]
  | .imax left right => do
      return .record [
        ("level_op", ← mkSafeSCMStr "imax"),
        ("left", ← compileLevel params left),
        ("right", ← compileLevel params right)
      ]
  | .param name =>
      match levelParamIndex name params 0 with
      | some index => do
          return .record [
            ("level_op", ← mkSafeSCMStr "param"),
            ("index", .int (Int.ofNat index))
          ]
      | none => .error (.unknownLevelParam name)
  | .mvar _ => .error (.unsupportedLevel "mvar")

def binderInfoName : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict_implicit"
  | .instImplicit => "instance_implicit"

def compileLevels
    (params : List Name) : Nat → List Level → Except CompileError (List (String × SCMExpr))
  | _, [] => .ok []
  | index, level :: levels => do
      let head := ("level_" ++ toString index, ← compileLevel params level)
      return head :: (← compileLevels params (index + 1) levels)

partial def compileExpr (ctx : CompileContext) : Expr → Except CompileError SCMExpr
  | .bvar index =>
      if index < ctx.binderDepth then do
        return .record [
          ("expr_op", ← mkSafeSCMStr "bvar"),
          ("index", .int (Int.ofNat index))
        ]
      else
        .error (.looseBVar index ctx.binderDepth)
  | .sort level => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "sort"),
        ("level", ← compileLevel ctx.levelParams level)
      ]
  | .const name levels => do
      -- Allow private/internal constants in proof terms (auto-generated helpers).
      -- Still refuse unsafe scm string chars in the printed name.
      return .record [
        ("expr_op", ← mkSafeSCMStr "const"),
        ("name", ← mkSafeSCMStr name.toString),
        ("private", .int (if isPrivateName name || name.isInternalDetail then 1 else 0)),
        ("levels", .record (← compileLevels ctx.levelParams 0 levels))
      ]
  | .app fn arg => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "app"),
        ("function", ← compileExpr ctx fn),
        ("argument", ← compileExpr ctx arg)
      ]
  | .lam _ binderType body binderInfo => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "lam"),
        ("binder_info", ← mkSafeSCMStr (binderInfoName binderInfo)),
        ("binder_type", ← compileExpr ctx binderType),
        ("body", ← compileExpr { ctx with binderDepth := ctx.binderDepth + 1 } body)
      ]
  | .forallE _ binderType body binderInfo => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "forall"),
        ("binder_info", ← mkSafeSCMStr (binderInfoName binderInfo)),
        ("binder_type", ← compileExpr ctx binderType),
        ("body", ← compileExpr { ctx with binderDepth := ctx.binderDepth + 1 } body)
      ]
  | .letE _ type value body _nondep => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "let"),
        ("type", ← compileExpr ctx type),
        ("value", ← compileExpr ctx value),
        ("body", ← compileExpr { ctx with binderDepth := ctx.binderDepth + 1 } body)
      ]
  | .lit (.natVal n) => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "lit_nat"),
        ("n", .int (Int.ofNat n))
      ]
  | .lit (.strVal s) => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "lit_str"),
        ("s", ← mkSafeSCMStr s)
      ]
  | .mdata _ e => compileExpr ctx e
  | .proj typeName idx struct => do
      return .record [
        ("expr_op", ← mkSafeSCMStr "proj"),
        ("type_name", ← mkSafeSCMStr typeName.toString),
        ("index", .int (Int.ofNat idx)),
        ("struct", ← compileExpr ctx struct)
      ]
  | .fvar _ => .error (.unsupportedExpr "fvar")
  | .mvar _ => .error (.unsupportedExpr "mvar")

/-- Allowed axioms on emitted RCC theorems (L3 ledger still records them).
House RCC proofs may use propext / Quot.sound / Classical.choice; anything else refuses. -/
def axiomFloorOk (axioms : List Name) : Bool :=
  axioms.all fun n =>
    n == `propext || n == `Quot.sound || n == `Classical.choice

def errorTag : CompileError → String
  | .unsafeSCMString _ => "unsafe_scm_string"
  | .unstableConstant _ => "unstable_constant"
  | .looseBVar _ _ => "loose_bvar"
  | .unknownLevelParam _ => "unknown_level_param"
  | .unsupportedLevel k => "unsupported_level:" ++ k
  | .unsupportedExpr k => "unsupported_expr:" ++ k
  | .sorryProof => "sorry_proof"
  | .axiomFloor _ => "axiom_floor"

def isResiduaRCCName (name : Name) : Bool :=
  let s := name.toString
  -- Exclude this compiler's own namespace (also under Residua.RCC.*).
  (s.startsWith "Residua.RCC." || s.startsWith "Residua.RCC ") &&
    !(s.startsWith "Residua.RCC.ProofTerm")

/-- Theorems we attempt to emit: public Residua.RCC.* excluding Lean-generated
`sizeOf_spec` (private-name proof terms; not authored formal content). -/
def isResiduaRCCEmittableTheorem (name : Name) : Bool :=
  isResiduaRCCName name &&
    !(name.toString.endsWith "sizeOf_spec") &&
    !(name.isInternalDetail)

def isResiduaIECName (name : Name) : Bool :=
  let s := name.toString
  s.startsWith "Residua.IEC." || s.startsWith "Residua.IEC "

def isResiduaIECEmittableTheorem (name : Name) : Bool :=
  isResiduaIECName name &&
    !(name.toString.endsWith "sizeOf_spec") &&
    !(name.isInternalDetail)

/-- One theorem compile attempt — never throws; returns status record. -/
def compileTheoremRow (name : Name) (theoremInfo : TheoremVal) : SCMExpr :=
  let fail (tag : String) (detail : String) : SCMExpr :=
    .record [
      ("status", .str "refuse"),
      ("theorem_name", .str name.toString),
      ("residue", .str tag),
      ("detail", .str detail),
      ("closure_claim", .int 0)
    ]
  if theoremInfo.value.hasSorry then
    fail "sorry_proof" "hasSorry"
  else
    -- axiom floor checked via IO-free path only when we have axioms list from caller
    let ctx : CompileContext := { levelParams := theoremInfo.levelParams }
    match compileExpr ctx theoremInfo.toConstantVal.type with
    | .error err => fail (errorTag err) (toString (repr err))
    | .ok declarationType =>
      match compileExpr ctx theoremInfo.value with
      | .error err => fail (errorTag err) (toString (repr err))
      | .ok proofValue =>
          .record [
            ("status", .str "emit_ok"),
            ("theorem_name", .str name.toString),
            ("declaration_type", declarationType),
            ("proof_value", proofValue),
            ("closure_claim", .int 0)
          ]

/-- Compile with axiom check (CommandElabM for collectAxioms). -/
def compileTheoremRowM (name : Name) : CommandElabM SCMExpr := do
  match (← getEnv).find? name with
  | some (.thmInfo theoremInfo) =>
      if theoremInfo.value.hasSorry then
        return .record [
          ("status", .str "refuse"),
          ("theorem_name", .str name.toString),
          ("residue", .str "sorry_proof"),
          ("detail", .str "hasSorry"),
          ("closure_claim", .int 0)
        ]
      let axioms ← collectAxioms name
      let axList := axioms.toList
      if !(axiomFloorOk axList) then
        return .record [
          ("status", .str "refuse"),
          ("theorem_name", .str name.toString),
          ("residue", .str "axiom_floor"),
          ("detail", .str (toString axList)),
          ("closure_claim", .int 0)
        ]
      let row := compileTheoremRow name theoremInfo
      -- attach axiom_count when emit_ok
      match row with
      | .record fields =>
          if fields.any (fun p => p.1 == "status" && match p.2 with | .str "emit_ok" => true | _ => false) then
            let mut axFields : List (String × SCMExpr) :=
              [("axiom_count", .int (Int.ofNat axList.length))]
            let mut i : Nat := 0
            for n in axList do
              axFields := axFields ++ [("axiom_" ++ toString i, .str n.toString)]
              i := i + 1
            return .record (fields ++ axFields)
          else
            return row
      | other => return other
  | some _ =>
      return .record [
        ("status", .str "refuse"),
        ("theorem_name", .str name.toString),
        ("residue", .str "not_theorem"),
        ("detail", .str "constant is not thmInfo"),
        ("closure_claim", .int 0)
      ]
  | none =>
      return .record [
        ("status", .str "refuse"),
        ("theorem_name", .str name.toString),
        ("residue", .str "theorem_missing"),
        ("detail", .str "not in environment"),
        ("closure_claim", .int 0)
      ]

def collectTheoremNames (pred : Name → Bool) : CommandElabM (Array Name) := do
  let env ← getEnv
  let mut acc : Array Name := #[]
  for (name, info) in env.constants.map₁.toList do
    match info with
    | .thmInfo _ =>
        if pred name then
          acc := acc.push name
    | _ => pure ()
  for (name, info) in env.constants.map₂.toList do
    match info with
    | .thmInfo _ =>
        if pred name && !(acc.contains name) then
          acc := acc.push name
    | _ => pure ()
  return acc.qsort (fun a b => a.toString < b.toString)

def collectResiduaRCCTheoremNames : CommandElabM (Array Name) :=
  collectTheoremNames isResiduaRCCEmittableTheorem

def collectResiduaIECTheoremNames : CommandElabM (Array Name) :=
  collectTheoremNames isResiduaIECEmittableTheorem

def rowIsEmitOk (row : SCMExpr) : Bool :=
  match row with
  | .record fields =>
      fields.any (fun p => p.1 == "status" && match p.2 with | .str "emit_ok" => true | _ => false)
  | _ => false

def compileRows (names : Array Name) : CommandElabM (Array (String × SCMExpr) × Nat × Nat) := do
  let mut rows : Array (String × SCMExpr) := #[]
  let mut nOk : Nat := 0
  let mut nRefuse : Nat := 0
  for i in [:names.size] do
    let name := names[i]!
    let row ← compileTheoremRowM name
    if rowIsEmitOk row then
      nOk := nOk + 1
    else
      nRefuse := nRefuse + 1
    rows := rows.push ("row_" ++ toString i, row)
  return (rows, nOk, nRefuse)

/-- Sanitize theorem name for a filesystem shard path. -/
def shardFileName (name : Name) : String :=
  String.mk <| name.toString.toList.map fun c =>
    if c.isAlphanum || c == '_' || c == '.' then c else '_'

def residueOfRow : SCMExpr → String
  | .record (("residue", .str s) :: _) => s
  | .record (_ :: rest) => residueOfRow (.record rest)
  | _ => ""

/-- Emit each theorem as its own scm shard + line summary (avoids one giant record). -/
def emitFormalEmissionShardedWith
    (pred : Name → Bool)
    (familyLabel : String)
    (summaryPath : System.FilePath) (shardDir : System.FilePath) : CommandElabM Unit := do
  let names ← collectTheoremNames pred
  liftIO <| IO.FS.createDirAll shardDir
  let mut nOk : Nat := 0
  let mut nRefuse : Nat := 0
  let mut lines : Array String := #[]
  for name in names do
    let row ← compileTheoremRowM name
    let ok := rowIsEmitOk row
    if ok then
      nOk := nOk + 1
      let scm := renderSCM row ++ "\n"
      liftIO <| IO.FS.writeFile (shardDir.join (shardFileName name ++ ".scm")) scm
    else
      nRefuse := nRefuse + 1
    let status := if ok then "emit_ok" else "refuse"
    let residue := residueOfRow row
    lines := lines.push s!"{status}\t{name.toString}\t{residue}"
  let total := names.size
  let closed := total > 0 && nRefuse == 0 && nOk == total
  let header : Array String := #[
    s!"theorem_total={total}",
    s!"emit_ok={nOk}",
    s!"refuse={nRefuse}",
    s!"closure_claim=0",
    s!"stage3_closed={if closed then 1 else 0}",
    s!"family={familyLabel}",
    s!"shard_dir={toString shardDir}"
  ]
  let body := "\n".intercalate (header ++ lines).toList ++ "\n"
  liftIO <| IO.FS.writeFile summaryPath body
  let statusScm := renderSCM (.record [
    ("verdict", .int (if closed then 0 else 1)),
    ("residue_code", .int (if closed then 0 else 1)),
    ("formal_proof_term_emission", .int 1),
    ("theorem_total", .int (Int.ofNat total)),
    ("emit_ok", .int (Int.ofNat nOk)),
    ("refuse", .int (Int.ofNat nRefuse)),
    ("stage3_closed", .int (if closed then 1 else 0)),
    ("closure_claim", .int 0)
  ]) ++ "\n"
  liftIO <| IO.FS.writeFile (shardDir.join "_status.scm") statusScm

def emitFormalEmissionSharded
    (summaryPath : System.FilePath) (shardDir : System.FilePath) : CommandElabM Unit :=
  emitFormalEmissionShardedWith isResiduaRCCEmittableTheorem "Residua.RCC"
    summaryPath shardDir

def emitIECFormalEmissionSharded
    (summaryPath : System.FilePath) (shardDir : System.FilePath) : CommandElabM Unit :=
  emitFormalEmissionShardedWith isResiduaIECEmittableTheorem "Residua.IEC"
    summaryPath shardDir

/-- Pilot helper. -/
def emitFormalEmissionSummary (path : System.FilePath) : CommandElabM Unit := do
  emitFormalEmissionSharded path ⟨"scm/rcc/formal/terms_pilot"⟩

def emitFormalEmissionManifest (path : System.FilePath) : CommandElabM Unit := do
  emitFormalEmissionSharded
    ⟨"conformance/rcc/formal_emission_summary_pilot.txt"⟩
    ⟨"scm/rcc/formal/terms_pilot"⟩
  liftIO <| IO.FS.writeFile path "see scm/rcc/formal/terms_pilot/_status.scm\n"

end Residua.RCC.ProofTerm

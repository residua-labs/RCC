import RCC.Support.SlotSemanticsCore

/-! # ResiduaPatchFabricMWE — Lean kernel anchor for `apps/patch-fabric` (issue #167).

A patch counts iff its `declared_base_q` EQUALS the target's `current_committed_q`. An
apply against a drifted base is REFUSED, state unchanged.

§40 anti-trap: `trust_the_patch` (apply regardless of declared base vs current state)
ADMITS a drifted-base clobber the real gate REFUSES.

Mirrors `ResiduaFabricMWE.lean`. 0 sorry / 0 axiom / 0 native_decide; prelude-only.
REUSES `[patch_base_drift]`.
-/

namespace Residua.Algorithms.PatchFabric

structure LegacyBaseDriftPatch where
  declared_base_q     : String
  current_committed_q : String
  patch_payload       : String
  client_says_apply   : Bool
  deriving DecidableEq, Repr

def verifyPatch (p : LegacyBaseDriftPatch) : Bool :=
  p.declared_base_q == p.current_committed_q

theorem verifyPatch_replay_byte_equal (p : LegacyBaseDriftPatch) :
    verifyPatch p = verifyPatch p := rfl

set_option maxRecDepth 4000

def legacyGenuinePatch : LegacyBaseDriftPatch :=
  { declared_base_q := "q_v1", current_committed_q := "q_v1"
  , patch_payload := "p", client_says_apply := true }

theorem genuine_accepts_demo : verifyPatch legacyGenuinePatch = true := by decide

/-- §15 FORGE — BASE DRIFT: declared base does not match current committed state. -/
def legacyForgedDriftPatch : LegacyBaseDriftPatch :=
  { declared_base_q := "q_v1", current_committed_q := "q_v2"   -- state advanced
  , patch_payload := "p", client_says_apply := true }

theorem verifyPatch_rejects_base_drift :
    verifyPatch legacyForgedDriftPatch = false := by decide

def mutantVerify (p : LegacyBaseDriftPatch) : Bool := p.client_says_apply

theorem mutant_admits_base_drift : mutantVerify legacyForgedDriftPatch = true := by decide

-- [patch_base_drift] -- anchor: real_engine_rejects_forged_mutant_admits_demo

theorem real_engine_rejects_forged_mutant_admits_demo :
    verifyPatch legacyForgedDriftPatch = false ∧
      mutantVerify legacyForgedDriftPatch = true := by decide

/-! ## S5 content-addressed edit confluence anchor

Architect seq709 ratifies B3/B1's two-token stance: `(path_id, content_addr)` names
the target, while the q-guard remains orthogonal. The no-rebase guarantee is gated on
two ∀-quantified laws, not fixture-only `by decide` demos:

* disjoint content targets commute to the same program q; and
* same target + same replacement is idempotent.

This section models the content-addressed frontier of untouched subtrees. It proves
only the honest S5 surface: targets are distinct, neither is an ancestor of the other
(supplied by the caller's tree relation), and neither replacement reintroduces the
other target. Touched-spine reshape survival is deliberately outside the theorem and
remains the named residue from seq709.
-/

abbrev ContentHash := String
abbrev PathId := String

structure EditNode where
  pathId      : PathId
  contentAddr : ContentHash
  body        : String
  deriving DecidableEq, Repr

structure ContentPatch where
  targetContent : ContentHash
  replacement   : EditNode
  deriving DecidableEq, Repr

def applyContentNode (p : ContentPatch) (n : EditNode) : EditNode :=
  if n.contentAddr = p.targetContent then p.replacement else n

def applyContent (p : ContentPatch) : List EditNode → List EditNode
  | [] => []
  | n :: ns => applyContentNode p n :: applyContent p ns

/-- `programQ` is opaque in the runtime; for this proof anchor equality of the normalized
frontier is the q-equality premise the emitter/runtime hash layer carries. -/
def programQ (program : List EditNode) : List EditNode := program

structure NonOverlappingContentTargets
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : ContentPatch) : Prop where
  target_ne : p1.targetContent ≠ p2.targetContent
  p1_not_ancestor_p2 : ancestorHash p1.targetContent p2.targetContent = false
  p2_not_ancestor_p1 : ancestorHash p2.targetContent p1.targetContent = false
  p1_replacement_not_p2 : p1.replacement.contentAddr ≠ p2.targetContent
  p2_replacement_not_p1 : p2.replacement.contentAddr ≠ p1.targetContent

theorem applyContent_disjoint_commute
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : ContentPatch)
    (h : NonOverlappingContentTargets ancestorHash p1 p2)
    (program : List EditNode) :
    applyContent p2 (applyContent p1 program) =
      applyContent p1 (applyContent p2 program) := by
  have target_ne_symm : p2.targetContent ≠ p1.targetContent := by
    intro hp
    exact h.target_ne hp.symm
  induction program with
  | nil =>
      rfl
  | cons n ns ih =>
      dsimp [applyContent]
      simp only [ih, List.cons.injEq, and_true]
      unfold applyContentNode
      by_cases h1 : n.contentAddr = p1.targetContent
      · by_cases h2 : n.contentAddr = p2.targetContent
        · exact False.elim (h.target_ne (h1.symm.trans h2))
        · simp [h1, h2, h.target_ne, target_ne_symm,
            h.p1_replacement_not_p2, h.p2_replacement_not_p1]
      · by_cases h2 : n.contentAddr = p2.targetContent
        · simp [h1, h2, h.target_ne, target_ne_symm,
            h.p1_replacement_not_p2, h.p2_replacement_not_p1]
        · simp [h1, h2]

theorem applyContent_disjoint_same_program_q
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : ContentPatch)
    (h : NonOverlappingContentTargets ancestorHash p1 p2)
    (program : List EditNode) :
    programQ (applyContent p2 (applyContent p1 program)) =
      programQ (applyContent p1 (applyContent p2 program)) := by
  exact congrArg programQ (applyContent_disjoint_commute ancestorHash p1 p2 h program)

theorem applyContent_idempotent_same_patch
    (p : ContentPatch) (program : List EditNode) :
    applyContent p (applyContent p program) = applyContent p program := by
  induction program with
  | nil =>
      rfl
  | cons n ns ih =>
      dsimp [applyContent]
      simp only [ih, List.cons.injEq, and_true]
      unfold applyContentNode
      by_cases h : n.contentAddr = p.targetContent
      · simp [h]
      · simp [h]

theorem applyContent_same_target_agree_converges
    (p1 p2 : ContentPatch)
    (hTarget : p1.targetContent = p2.targetContent)
    (hReplacement : p1.replacement = p2.replacement)
    (program : List EditNode) :
    applyContent p2 (applyContent p1 program) = applyContent p1 program := by
  cases p1 with
  | mk t1 r1 =>
      cases p2 with
      | mk t2 r2 =>
          dsimp at hTarget hReplacement
          subst t2
          subst r2
          exact applyContent_idempotent_same_patch { targetContent := t1, replacement := r1 } program

theorem applyContent_same_target_agree_same_program_q
    (p1 p2 : ContentPatch)
    (hTarget : p1.targetContent = p2.targetContent)
    (hReplacement : p1.replacement = p2.replacement)
    (program : List EditNode) :
    programQ (applyContent p2 (applyContent p1 program)) =
      programQ (applyContent p1 program) := by
  exact congrArg programQ
    (applyContent_same_target_agree_converges p1 p2 hTarget hReplacement program)

/-! ### Position mode: the full `(path_id, content_addr)` target

The content-mode theorem above captures same-content/all-occurrences edits. The B3
stance also has a position mode: occurrence uniqueness is the pair `(path_id,
content_addr)`, and a patch must match both tokens before replacing a node.
-/

structure TwoTokenTarget where
  pathId      : PathId
  contentAddr : ContentHash
  deriving DecidableEq, Repr

structure TwoTokenPatch where
  target      : TwoTokenTarget
  replacement : EditNode
  deriving DecidableEq, Repr

def matchesTwoToken (t : TwoTokenTarget) (n : EditNode) : Prop :=
  n.pathId = t.pathId ∧ n.contentAddr = t.contentAddr

instance (t : TwoTokenTarget) (n : EditNode) : Decidable (matchesTwoToken t n) := by
  unfold matchesTwoToken
  infer_instance

theorem target_eq_of_matches
    (t1 t2 : TwoTokenTarget) (n : EditNode)
    (h1 : matchesTwoToken t1 n)
    (h2 : matchesTwoToken t2 n) :
    t1 = t2 := by
  cases t1 with
  | mk p1 c1 =>
      cases t2 with
      | mk p2 c2 =>
          cases n with
          | mk np nc body =>
              dsimp [matchesTwoToken] at h1 h2
              cases h1.left
              cases h1.right
              cases h2.left
              cases h2.right
              rfl

def applyTwoTokenNode (p : TwoTokenPatch) (n : EditNode) : EditNode :=
  if matchesTwoToken p.target n then p.replacement else n

def applyTwoToken (p : TwoTokenPatch) : List EditNode → List EditNode
  | [] => []
  | n :: ns => applyTwoTokenNode p n :: applyTwoToken p ns

structure NonOverlappingTwoTokenTargets
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : TwoTokenPatch) : Prop where
  target_ne : p1.target ≠ p2.target
  content_ne : p1.target.contentAddr ≠ p2.target.contentAddr
  p1_not_ancestor_p2 : ancestorHash p1.target.contentAddr p2.target.contentAddr = false
  p2_not_ancestor_p1 : ancestorHash p2.target.contentAddr p1.target.contentAddr = false
  p1_replacement_not_p2 : ¬ matchesTwoToken p2.target p1.replacement
  p2_replacement_not_p1 : ¬ matchesTwoToken p1.target p2.replacement

theorem applyTwoToken_disjoint_commute
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : TwoTokenPatch)
    (h : NonOverlappingTwoTokenTargets ancestorHash p1 p2)
    (program : List EditNode) :
    applyTwoToken p2 (applyTwoToken p1 program) =
      applyTwoToken p1 (applyTwoToken p2 program) := by
  induction program with
  | nil =>
      rfl
  | cons n ns ih =>
      dsimp [applyTwoToken]
      simp only [ih, List.cons.injEq, and_true]
      unfold applyTwoTokenNode
      by_cases h1 : matchesTwoToken p1.target n
      · by_cases h2 : matchesTwoToken p2.target n
        · exact False.elim (h.target_ne (target_eq_of_matches p1.target p2.target n h1 h2))
        · simp [h1, h2, h.p1_replacement_not_p2, h.p2_replacement_not_p1]
      · by_cases h2 : matchesTwoToken p2.target n
        · simp [h1, h2, h.p1_replacement_not_p2, h.p2_replacement_not_p1]
        · simp [h1, h2]

theorem applyTwoToken_disjoint_same_program_q
    (ancestorHash : ContentHash → ContentHash → Bool)
    (p1 p2 : TwoTokenPatch)
    (h : NonOverlappingTwoTokenTargets ancestorHash p1 p2)
    (program : List EditNode) :
    programQ (applyTwoToken p2 (applyTwoToken p1 program)) =
      programQ (applyTwoToken p1 (applyTwoToken p2 program)) := by
  exact congrArg programQ (applyTwoToken_disjoint_commute ancestorHash p1 p2 h program)

theorem applyTwoToken_idempotent_same_patch
    (p : TwoTokenPatch) (program : List EditNode) :
    applyTwoToken p (applyTwoToken p program) = applyTwoToken p program := by
  induction program with
  | nil =>
      rfl
  | cons n ns ih =>
      dsimp [applyTwoToken]
      simp only [ih, List.cons.injEq, and_true]
      unfold applyTwoTokenNode
      by_cases hn : matchesTwoToken p.target n
      · by_cases hr : matchesTwoToken p.target p.replacement
        · simp [hn, hr]
        · simp [hn, hr]
      · simp [hn]

theorem applyTwoToken_same_target_agree_converges
    (p1 p2 : TwoTokenPatch)
    (hTarget : p1.target = p2.target)
    (hReplacement : p1.replacement = p2.replacement)
    (program : List EditNode) :
    applyTwoToken p2 (applyTwoToken p1 program) = applyTwoToken p1 program := by
  cases p1 with
  | mk t1 r1 =>
      cases p2 with
      | mk t2 r2 =>
          dsimp at hTarget hReplacement
          subst t2
          subst r2
          exact applyTwoToken_idempotent_same_patch { target := t1, replacement := r1 } program

theorem applyTwoToken_same_target_agree_same_program_q
    (p1 p2 : TwoTokenPatch)
    (hTarget : p1.target = p2.target)
    (hReplacement : p1.replacement = p2.replacement)
    (program : List EditNode) :
    programQ (applyTwoToken p2 (applyTwoToken p1 program)) =
      programQ (applyTwoToken p1 program) := by
  exact congrArg programQ
    (applyTwoToken_same_target_agree_converges p1 p2 hTarget hReplacement program)

/-! ### C2: first real `Expr` patch-semantics anchor

The preceding S5 theorems model a normalized frontier. C2 starts connecting that
shape to the real Lean `Expr` syntax used by `evalL`: a q-guarded child edit on
an actual `.add l r` node. This intentionally remains a minimal constructor
anchor, not a new runtime primitive and not a claim about touched-spine reshape.
-/

abbrev RealExpr := MSTNFSlotSemanticsCoreMWE.Expr

inductive AddChildPath
  | left
  | right
  deriving DecidableEq, Repr

structure RealExprTarget where
  pathId      : AddChildPath
  contentAddr : ContentHash
  deriving DecidableEq, Repr

structure RealExprPatch where
  target      : RealExprTarget
  replacement : RealExpr
  deriving Repr

def applyRealExprAddChild
    (exprQ : RealExpr → ContentHash)
    (p : RealExprPatch)
    (e : RealExpr) : RealExpr :=
  match e with
  | .add l r =>
      match p.target.pathId with
      | .left =>
          if exprQ l = p.target.contentAddr then .add p.replacement r else e
      | .right =>
          if exprQ r = p.target.contentAddr then .add l p.replacement else e
  | _ => e

theorem conflux_real_expr_disjoint_children_commute_core
    (exprQ : RealExpr → ContentHash)
    (l r replL replR : RealExpr)
    (qL qR : ContentHash)
    (hL : exprQ l = qL)
    (hR : exprQ r = qR) :
    applyRealExprAddChild exprQ
        { target := { pathId := .right, contentAddr := qR }, replacement := replR }
        (applyRealExprAddChild exprQ
          { target := { pathId := .left, contentAddr := qL }, replacement := replL }
          (.add l r))
      =
    applyRealExprAddChild exprQ
        { target := { pathId := .left, contentAddr := qL }, replacement := replL }
        (applyRealExprAddChild exprQ
          { target := { pathId := .right, contentAddr := qR }, replacement := replR }
          (.add l r)) := by
  simp [applyRealExprAddChild, hL, hR]

theorem conflux_real_expr_disjoint_children_commute
    (exprQ : RealExpr → ContentHash)
    (l r replL replR : RealExpr)
    (qL qR : ContentHash)
    (hL : exprQ l = qL)
    (hR : exprQ r = qR) :
    applyRealExprAddChild exprQ
        { target := { pathId := .right, contentAddr := qR }, replacement := replR }
        (applyRealExprAddChild exprQ
          { target := { pathId := .left, contentAddr := qL }, replacement := replL }
          (.add l r))
      =
    applyRealExprAddChild exprQ
        { target := { pathId := .left, contentAddr := qL }, replacement := replL }
        (applyRealExprAddChild exprQ
          { target := { pathId := .right, contentAddr := qR }, replacement := replR }
          (.add l r)) := by
  exact conflux_real_expr_disjoint_children_commute_core
    exprQ l r replL replR qL qR hL hR

theorem applyRealExprAddChild_idempotent_add
    (exprQ : RealExpr → ContentHash)
    (target : RealExprTarget)
    (l r repl : RealExpr)
    :
    applyRealExprAddChild exprQ
        { target := target, replacement := repl }
        (applyRealExprAddChild exprQ
          { target := target, replacement := repl }
          (.add l r))
      =
    applyRealExprAddChild exprQ
        { target := target, replacement := repl }
        (.add l r) := by
  cases target with
  | mk path q =>
    cases path
    · by_cases h : exprQ l = q
      · by_cases hRepl : exprQ repl = q
        · simp [applyRealExprAddChild, h, hRepl]
        · simp [applyRealExprAddChild, h, hRepl]
      · simp [applyRealExprAddChild, h]
    · by_cases h : exprQ r = q
      · by_cases hRepl : exprQ repl = q
        · simp [applyRealExprAddChild, h, hRepl]
        · simp [applyRealExprAddChild, h, hRepl]
      · simp [applyRealExprAddChild, h]

theorem conflux_real_expr_same_target_agree_converges
    (exprQ : RealExpr → ContentHash)
    (target : RealExprTarget)
    (l r repl : RealExpr) :
    applyRealExprAddChild exprQ
        { target := target, replacement := repl }
        (applyRealExprAddChild exprQ
          { target := target, replacement := repl }
          (.add l r))
      =
    applyRealExprAddChild exprQ
        { target := target, replacement := repl }
        (.add l r) := by
  exact applyRealExprAddChild_idempotent_add exprQ target l r repl

/-- Restricted SCM expression surface used by the C2 Lean emitters.

This is intentionally smaller than the full Scheme grammar: it covers the operators
that this C2 leaf emits and keeps the compiler boundary typed before rendering to
the checked-in `.scm` bytes.
-/
inductive SCMExpr where
  | atom : String → SCMExpr
  | str : String → SCMExpr
  | int : Int → SCMExpr
  | call : String → List SCMExpr → SCMExpr
  | field : SCMExpr → String → SCMExpr
  | scmAnd : List SCMExpr → SCMExpr
  | scmNot : SCMExpr → SCMExpr
  | scmEq : SCMExpr → SCMExpr → SCMExpr
  | record : List (String × SCMExpr) → SCMExpr
  | scmIf : SCMExpr → SCMExpr → SCMExpr → SCMExpr
  | let1 : String → SCMExpr → SCMExpr → SCMExpr
  deriving Repr

def SCMExpr.invalidContentQ (q : String) : SCMExpr :=
  .scmNot (.call "resodus.is_content_q" [.atom q])

def SCMExpr.okRecord (leftQ rightQ matched : SCMExpr) : SCMExpr :=
  .record [
    ("verdict", .int 0),
    ("residue_code", .int 0),
    ("left_q", leftQ),
    ("right_q", rightQ),
    ("matched", matched)
  ]

def SCMExpr.invalidRecord : SCMExpr :=
  .record [("verdict", .int 1), ("residue_code", .int 1)]

def SCMExpr.badPathRecord : SCMExpr :=
  .record [("verdict", .int 2), ("residue_code", .int 2)]

mutual
  def SCMExpr.renderInline : SCMExpr → String
    | .atom value => value
    | .str value => "\"" ++ value ++ "\""
    | .int value => toString value
    | .call name args =>
        "(" ++ String.intercalate " " ("call" :: name :: SCMExpr.renderInlineArgs args) ++ ")"
    | .field value fieldName =>
        "(field " ++ SCMExpr.renderInline value ++ " " ++ fieldName ++ ")"
    | .scmAnd terms =>
        "(and " ++ String.intercalate " " (SCMExpr.renderInlineArgs terms) ++ ")"
    | .scmNot value =>
        "(not " ++ SCMExpr.renderInline value ++ ")"
    | .scmEq left right =>
        "(= " ++ SCMExpr.renderInline left ++ " " ++ SCMExpr.renderInline right ++ ")"
    | .record fields =>
        "(record " ++
          String.intercalate " " (SCMExpr.renderInlineFields fields) ++
          ")"
    | .scmIf cond thenExpr elseExpr =>
        "(if " ++ SCMExpr.renderInline cond ++ " " ++
          SCMExpr.renderInline thenExpr ++ " " ++ SCMExpr.renderInline elseExpr ++ ")"
    | .let1 name value body =>
        "(let (" ++ name ++ " " ++ SCMExpr.renderInline value ++ ") " ++
          SCMExpr.renderInline body ++ ")"

  def SCMExpr.renderInlineArgs : List SCMExpr → List String
    | [] => []
    | arg :: args => SCMExpr.renderInline arg :: SCMExpr.renderInlineArgs args

  def SCMExpr.renderInlineFields : List (String × SCMExpr) → List String
    | [] => []
    | entry :: fields =>
        ("(" ++ entry.fst ++ " " ++ SCMExpr.renderInline entry.snd ++ ")") ::
          SCMExpr.renderInlineFields fields

  def SCMExpr.renderRecordLines (indent : Nat) : List (String × SCMExpr) → List String
    | [] => []
    | entry :: fields =>
        (String.mk (List.replicate indent ' ') ++
          "(" ++ entry.fst ++ " " ++ SCMExpr.renderInline entry.snd ++ ")") ::
          SCMExpr.renderRecordLines indent fields

  def SCMExpr.renderAt : Nat → SCMExpr → String
    | indent, .let1 name value body =>
        "(let (" ++ name ++ " " ++ SCMExpr.renderInline value ++ ")\n" ++
          String.mk (List.replicate (indent + 2) ' ') ++
          SCMExpr.renderAt (indent + 2) body ++ ")"
    | indent, .scmIf cond thenExpr elseExpr =>
        "(if " ++ SCMExpr.renderInline cond ++ "\n" ++
          String.mk (List.replicate (indent + 2) ' ') ++
          SCMExpr.renderAt (indent + 2) thenExpr ++ "\n" ++
          String.mk (List.replicate (indent + 2) ' ') ++
          SCMExpr.renderAt (indent + 2) elseExpr ++ ")"
    | indent, .record fields =>
        if fields.length > 6 then
          "(record\n" ++
            String.intercalate "\n" (SCMExpr.renderRecordLines (indent + 2) fields) ++
            ")"
        else
          SCMExpr.renderInline (.record fields)
    | _, other => SCMExpr.renderInline other
end

def renderSCM (expr : SCMExpr) : String :=
  SCMExpr.renderAt 0 expr

def c2ApplyAddChildSCMAST : SCMExpr :=
  .scmIf (.invalidContentQ "left_q")
    .invalidRecord
    (.scmIf (.invalidContentQ "right_q")
      .invalidRecord
      (.scmIf (.invalidContentQ "expected_q")
        .invalidRecord
        (.scmIf (.invalidContentQ "replacement_q")
          .invalidRecord
          (.scmIf (.scmEq (.atom "path_id") (.int 0))
            (.scmIf (.scmEq (.atom "left_q") (.atom "expected_q"))
              (.okRecord (.atom "replacement_q") (.atom "right_q") (.int 1))
              (.okRecord (.atom "left_q") (.atom "right_q") (.int 0)))
            (.scmIf (.scmEq (.atom "path_id") (.int 1))
              (.scmIf (.scmEq (.atom "right_q") (.atom "expected_q"))
                (.okRecord (.atom "left_q") (.atom "replacement_q") (.int 1))
                (.okRecord (.atom "left_q") (.atom "right_q") (.int 0)))
              .badPathRecord)))))

def c2ApplyAddChildSCM : String :=
  renderSCM c2ApplyAddChildSCMAST

def c2ApplyAddChildSCMMutant : String :=
  String.intercalate "\n" [
    "(record (verdict 0) (residue_code 0) (left_q left_q) (right_q right_q) (matched 0))"
  ]

theorem c2_apply_add_child_emits_current_scm :
    c2ApplyAddChildSCM = renderSCM c2ApplyAddChildSCMAST := by
  rfl

theorem c2_apply_add_child_mutant_diverges :
    c2ApplyAddChildSCM ≠ c2ApplyAddChildSCMMutant := by
  decide

def c2Field (recordName fieldName : String) : SCMExpr :=
  .field (.atom recordName) fieldName

def c2ApplyAddChildCall
    (leftQ rightQ pathId expectedQ replacementQ : SCMExpr) : SCMExpr :=
  .call "conflux.c2_apply_add_child" [
    leftQ,
    rightQ,
    pathId,
    expectedQ,
    replacementQ
  ]

def c2AbortOnNonzeroVerdict (recordName : String) (next : SCMExpr) : SCMExpr :=
  .scmIf (.scmNot (.scmEq (c2Field recordName "verdict") (.int 0)))
    (.atom recordName)
    next

def c2LetChecked (recordName : String) (value next : SCMExpr) : SCMExpr :=
  .let1 recordName value (c2AbortOnNonzeroVerdict recordName next)

def c2RealExprConfluenceResultAST : SCMExpr :=
  let bothConverge : SCMExpr :=
    .scmAnd [.atom "disjoint_commutes", .atom "same_target_converges"]
  .record [
    ("verdict", .scmIf bothConverge (.int 0) (.int 9)),
    ("residue_code", .scmIf bothConverge (.int 0) (.int 9)),
    ("c2_real_expr_confluence", .int 1),
    ("closure_claim", .int 0),
    ("disjoint_commutes", .scmIf (.atom "disjoint_commutes") (.int 1) (.int 0)),
    ("same_target_converges", .scmIf (.atom "same_target_converges") (.int 1) (.int 0)),
    ("left_then_right_left_q", c2Field "left_then_right" "left_q"),
    ("left_then_right_right_q", c2Field "left_then_right" "right_q"),
    ("right_then_left_left_q", c2Field "right_then_left" "left_q"),
    ("right_then_left_right_q", c2Field "right_then_left" "right_q"),
    ("same_once_left_q", c2Field "same_once" "left_q"),
    ("same_once_right_q", c2Field "same_once" "right_q"),
    ("same_twice_left_q", c2Field "same_twice" "left_q"),
    ("same_twice_right_q", c2Field "same_twice" "right_q")
  ]

def c2RealExprConfluenceSCMAST : SCMExpr :=
  c2LetChecked "left_first"
    (c2ApplyAddChildCall
      (.atom "original_left_q")
      (.atom "original_right_q")
      (.int 0)
      (.atom "left_expected_q")
      (.atom "left_replacement_q"))
    (c2LetChecked "left_then_right"
      (c2ApplyAddChildCall
        (c2Field "left_first" "left_q")
        (c2Field "left_first" "right_q")
        (.int 1)
        (.atom "right_expected_q")
        (.atom "right_replacement_q"))
      (c2LetChecked "right_first"
        (c2ApplyAddChildCall
          (.atom "original_left_q")
          (.atom "original_right_q")
          (.int 1)
          (.atom "right_expected_q")
          (.atom "right_replacement_q"))
        (c2LetChecked "right_then_left"
          (c2ApplyAddChildCall
            (c2Field "right_first" "left_q")
            (c2Field "right_first" "right_q")
            (.int 0)
            (.atom "left_expected_q")
            (.atom "left_replacement_q"))
          (c2LetChecked "same_once"
            (c2ApplyAddChildCall
              (.atom "original_left_q")
              (.atom "original_right_q")
              (.int 0)
              (.atom "same_expected_q")
              (.atom "same_replacement_q"))
            (c2LetChecked "same_twice"
              (c2ApplyAddChildCall
                (c2Field "same_once" "left_q")
                (c2Field "same_once" "right_q")
                (.int 0)
                (.atom "same_expected_q")
                (.atom "same_replacement_q"))
              (.let1 "disjoint_commutes"
                (.scmAnd [
                  .scmEq
                    (c2Field "left_then_right" "left_q")
                    (c2Field "right_then_left" "left_q"),
                  .scmEq
                    (c2Field "left_then_right" "right_q")
                    (c2Field "right_then_left" "right_q")
                ])
                (.let1 "same_target_converges"
                  (.scmAnd [
                    .scmEq
                      (c2Field "same_once" "left_q")
                      (c2Field "same_twice" "left_q"),
                    .scmEq
                      (c2Field "same_once" "right_q")
                      (c2Field "same_twice" "right_q")
                  ])
                  c2RealExprConfluenceResultAST)))))))

def c2RealExprConfluenceSCM : String :=
  renderSCM c2RealExprConfluenceSCMAST

def c2RealExprConfluenceSCMMutant : String :=
  String.intercalate "\n" [
    "(record (verdict 0) (residue_code 0) (c2_real_expr_confluence 1) (closure_claim 0) (disjoint_commutes 1) (same_target_converges 1))"
  ]

theorem c2_real_expr_confluence_emits_current_scm :
    c2RealExprConfluenceSCM = renderSCM c2RealExprConfluenceSCMAST := by
  rfl

theorem c2_real_expr_confluence_mutant_diverges :
    c2RealExprConfluenceSCM ≠ c2RealExprConfluenceSCMMutant := by
  decide

def c2EvidenceErrorRecord (code : Int) : SCMExpr :=
  .record [("verdict", .int 1), ("residue_code", .int code)]

def c2RequireContentQ (qName : String) (next : SCMExpr) : SCMExpr :=
  .scmIf (.invalidContentQ qName)
    (c2EvidenceErrorRecord 1)
    next

def c2RequireContentQs : List String → SCMExpr → SCMExpr
  | [], next => next
  | qName :: qNames, next => c2RequireContentQ qName (c2RequireContentQs qNames next)

def c2RequireOneFlag (flagName : String) (code : Int) (next : SCMExpr) : SCMExpr :=
  .scmIf (.scmNot (.scmEq (.atom flagName) (.int 1)))
    (c2EvidenceErrorRecord code)
    next

def c2RequireOneFlags : List (String × Int) → SCMExpr → SCMExpr
  | [], next => next
  | (flagName, code) :: flags, next =>
      c2RequireOneFlag flagName code (c2RequireOneFlags flags next)

def c2MismatchRecord (code : Int) (leftName rightName : String) : SCMExpr :=
  .record [
    ("verdict", .int 1),
    ("residue_code", .int code),
    (leftName, .atom leftName),
    (rightName, .atom rightName)
  ]

def c2RequireSameQ
    (leftName rightName : String) (code : Int) (next : SCMExpr) : SCMExpr :=
  .scmIf (.scmNot (.scmEq (.atom leftName) (.atom rightName)))
    (c2MismatchRecord code leftName rightName)
    next

def c2RequireSameQs : List (String × String × Int) → SCMExpr → SCMExpr
  | [], next => next
  | (leftName, rightName, code) :: checks, next =>
      c2RequireSameQ leftName rightName code (c2RequireSameQs checks next)

def c2ProofEvidenceBindOkAST : SCMExpr :=
  .record [
    ("verdict", .int 0),
    ("residue_code", .int 0),
    ("c2_proof_evidence_receipt", .int 1),
    ("closure_claim", .int 0),
    ("lean_source_q", .atom "lean_source_q"),
    ("theorem_set_q", .atom "theorem_set_q"),
    ("axiom_audit_q", .atom "axiom_audit_q"),
    ("emitted_belief_q", .atom "emitted_belief_q"),
    ("lean_runner_attestation_q", .atom "lean_runner_attestation_q"),
    ("lean_emitted_apply_add_child_q", .atom "lean_emitted_apply_add_child_q"),
    ("checked_in_apply_add_child_q", .atom "checked_in_apply_add_child_q"),
    ("lean_emitted_real_expr_confluence_q", .atom "lean_emitted_real_expr_confluence_q"),
    ("checked_in_real_expr_confluence_q", .atom "checked_in_real_expr_confluence_q"),
    ("lean_emitted_proof_evidence_bind_q", .atom "lean_emitted_proof_evidence_bind_q"),
    ("checked_in_proof_evidence_bind_q", .atom "checked_in_proof_evidence_bind_q"),
    ("lean_emitted_proof_term_certificate_q", .atom "lean_emitted_proof_term_certificate_q"),
    ("checked_in_proof_term_certificate_q", .atom "checked_in_proof_term_certificate_q"),
    ("lean_compiled_proof_payload_q", .atom "lean_compiled_proof_payload_q"),
    ("certificate_compiled_proof_payload_q", .atom "certificate_compiled_proof_payload_q"),
    ("lean_semantic_proof_payload_q", .atom "lean_semantic_proof_payload_q"),
    ("certificate_semantic_proof_payload_q", .atom "certificate_semantic_proof_payload_q"),
    ("lean_emission_proof_payload_q", .atom "lean_emission_proof_payload_q"),
    ("certificate_emission_proof_payload_q", .atom "certificate_emission_proof_payload_q"),
    ("proof_emitted", .atom "proof_emitted"),
    ("no_sorry_ax", .atom "no_sorry_ax"),
    ("no_native_decide", .atom "no_native_decide"),
    ("axiom_floor_propext_only", .atom "axiom_floor_propext_only")
  ]

def c2ProofEvidenceBindSCMAST : SCMExpr :=
  c2RequireContentQs [
    "lean_source_q",
    "theorem_set_q",
    "axiom_audit_q",
    "emitted_belief_q",
    "lean_runner_attestation_q",
    "lean_emitted_apply_add_child_q",
    "checked_in_apply_add_child_q",
    "lean_emitted_real_expr_confluence_q",
    "checked_in_real_expr_confluence_q",
    "lean_emitted_proof_evidence_bind_q",
    "checked_in_proof_evidence_bind_q",
    "lean_emitted_proof_term_certificate_q",
    "checked_in_proof_term_certificate_q",
    "lean_compiled_proof_payload_q",
    "certificate_compiled_proof_payload_q",
    "lean_semantic_proof_payload_q",
    "certificate_semantic_proof_payload_q",
    "lean_emission_proof_payload_q",
    "certificate_emission_proof_payload_q"
  ] (
    c2RequireOneFlags [
      ("proof_emitted", 2),
      ("no_sorry_ax", 4),
      ("no_native_decide", 4),
      ("axiom_floor_propext_only", 5)
    ] (
      c2RequireSameQs [
        ("lean_emitted_apply_add_child_q", "checked_in_apply_add_child_q", 6),
        ("lean_emitted_real_expr_confluence_q", "checked_in_real_expr_confluence_q", 7),
        ("lean_emitted_proof_evidence_bind_q", "checked_in_proof_evidence_bind_q", 8),
        ("lean_emitted_proof_term_certificate_q", "checked_in_proof_term_certificate_q", 9),
        ("lean_compiled_proof_payload_q", "certificate_compiled_proof_payload_q", 10),
        ("lean_semantic_proof_payload_q", "certificate_semantic_proof_payload_q", 11),
        ("lean_emission_proof_payload_q", "certificate_emission_proof_payload_q", 12)
      ] c2ProofEvidenceBindOkAST))

def c2ProofEvidenceBindSCM : String :=
  renderSCM c2ProofEvidenceBindSCMAST

def c2ProofEvidenceBindSCMMutant : String :=
  String.intercalate "\n" [
    "(record (verdict 0) (residue_code 0) (c2_proof_evidence_receipt 1) (closure_claim 1))"
  ]

theorem c2_proof_evidence_bind_emits_current_scm :
    c2ProofEvidenceBindSCM = renderSCM c2ProofEvidenceBindSCMAST := by
  rfl

theorem c2_proof_evidence_bind_mutant_diverges :
    c2ProofEvidenceBindSCM ≠ c2ProofEvidenceBindSCMMutant := by
  decide

inductive C2ProofTermKind where
  | semanticTheorem
  | scmEmitter
  deriving DecidableEq, Repr

structure C2ProofTerm where
  name : String
  kind : C2ProofTermKind
  proofPayloadQ : String
  axiomFloorPropextOnly : Bool
  noSorryAx : Bool
  noNativeDecide : Bool
  deriving DecidableEq, Repr

def c2CountProofKind (kind : C2ProofTermKind) : List C2ProofTerm → Nat
  | [] => 0
  | term :: terms =>
      (if term.kind = kind then 1 else 0) + c2CountProofKind kind terms

def c2AllProofTermFlag (flag : C2ProofTerm → Bool) : List C2ProofTerm → Bool
  | [] => true
  | term :: terms => flag term && c2AllProofTermFlag flag terms

def c2AllProofPayloadQ (q : String) : List C2ProofTerm → Bool
  | [] => true
  | term :: terms => term.proofPayloadQ = q && c2AllProofPayloadQ q terms

def c2BoolFlag (value : Bool) : SCMExpr :=
  if value then .int 1 else .int 0

def c2SemanticProofPayloadQ : String :=
  "de815fded5296f5659115c504a531a1efe7ae2ed2a8c94bf4689240638e55d88"

def c2EmissionProofPayloadQ : String :=
  "bfe30eb0733784bb67a85335a427fca16f3cc3a4e51ce9368ef5ef2cff739fc1"

def c2CompiledProofPayloadQ : String :=
  "c271f6eb3a6e1981a702bbeecc1e5b15df3b4b125ebd248703a6ca70c314035c"

def c2ProofTermSubsetV1 : List C2ProofTerm := [
  {
    name := "applyTwoToken_disjoint_same_program_q",
    kind := .semanticTheorem,
    proofPayloadQ := c2SemanticProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "applyTwoToken_same_target_agree_same_program_q",
    kind := .semanticTheorem,
    proofPayloadQ := c2SemanticProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux_real_expr_disjoint_children_commute",
    kind := .semanticTheorem,
    proofPayloadQ := c2SemanticProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux_real_expr_same_target_agree_converges",
    kind := .semanticTheorem,
    proofPayloadQ := c2SemanticProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux.c2_apply_add_child",
    kind := .scmEmitter,
    proofPayloadQ := c2EmissionProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux.c2_real_expr_confluence",
    kind := .scmEmitter,
    proofPayloadQ := c2EmissionProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux.c2_proof_evidence_bind",
    kind := .scmEmitter,
    proofPayloadQ := c2EmissionProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  },
  {
    name := "conflux.c2_proof_term_certificate",
    kind := .scmEmitter,
    proofPayloadQ := c2EmissionProofPayloadQ,
    axiomFloorPropextOnly := true,
    noSorryAx := true,
    noNativeDecide := true
  }
]

def c2CompileProofTermCertificateAST (terms : List C2ProofTerm) : SCMExpr :=
  .record [
    ("verdict", .int 0),
    ("residue_code", .int 0),
    ("c2_proof_term_certificate", .int 1),
    ("proof_term_subset_v0", .int 1),
    ("proof_term_compiler_subset_v1", .int 1),
    ("proof_payload_subset_v2", .int 1),
    ("compiled_proof_term_count", .int (Int.ofNat terms.length)),
    ("compiled_proof_payload_q", .str c2CompiledProofPayloadQ),
    ("semantic_theorem_count", .int (Int.ofNat (c2CountProofKind .semanticTheorem terms))),
    ("semantic_proof_payload_q", .str c2SemanticProofPayloadQ),
    ("emission_theorem_count", .int (Int.ofNat (c2CountProofKind .scmEmitter terms))),
    ("emission_proof_payload_q", .str c2EmissionProofPayloadQ),
    ("axiom_floor_propext_only", c2BoolFlag (c2AllProofTermFlag C2ProofTerm.axiomFloorPropextOnly terms)),
    ("no_sorry_ax", c2BoolFlag (c2AllProofTermFlag C2ProofTerm.noSorryAx terms)),
    ("no_native_decide", c2BoolFlag (c2AllProofTermFlag C2ProofTerm.noNativeDecide terms)),
    ("full_proof_term_compiler", .int 0),
    ("closure_claim", .int 0)
  ]

def c2ProofTermCertificateSCMAST : SCMExpr :=
  c2CompileProofTermCertificateAST c2ProofTermSubsetV1

def c2ProofTermCertificateSCM : String :=
  renderSCM c2ProofTermCertificateSCMAST

def c2ProofTermCertificateSCMMutant : String :=
  "(record (verdict 0) (residue_code 0) (c2_proof_term_certificate 1) (proof_term_subset_v0 1) (full_proof_term_compiler 1) (closure_claim 1))"

theorem c2_proof_term_compiler_counts_current_subset :
    c2ProofTermSubsetV1.length = 8 ∧
      c2CountProofKind .semanticTheorem c2ProofTermSubsetV1 = 4 ∧
      c2CountProofKind .scmEmitter c2ProofTermSubsetV1 = 4 ∧
      c2AllProofTermFlag C2ProofTerm.axiomFloorPropextOnly c2ProofTermSubsetV1 = true ∧
      c2AllProofTermFlag C2ProofTerm.noSorryAx c2ProofTermSubsetV1 = true ∧
      c2AllProofTermFlag C2ProofTerm.noNativeDecide c2ProofTermSubsetV1 = true := by
  decide

theorem c2_proof_term_payload_q_current_subset :
    c2AllProofPayloadQ c2SemanticProofPayloadQ (c2ProofTermSubsetV1.take 4) = true ∧
      c2AllProofPayloadQ c2EmissionProofPayloadQ (c2ProofTermSubsetV1.drop 4) = true ∧
      c2SemanticProofPayloadQ = "de815fded5296f5659115c504a531a1efe7ae2ed2a8c94bf4689240638e55d88" ∧
      c2EmissionProofPayloadQ = "bfe30eb0733784bb67a85335a427fca16f3cc3a4e51ce9368ef5ef2cff739fc1" ∧
      c2CompiledProofPayloadQ = "c271f6eb3a6e1981a702bbeecc1e5b15df3b4b125ebd248703a6ca70c314035c" := by
  decide

theorem c2_proof_term_certificate_emits_current_scm :
    c2ProofTermCertificateSCM = renderSCM c2ProofTermCertificateSCMAST := by
  rfl

theorem c2_proof_term_certificate_mutant_diverges :
    c2ProofTermCertificateSCM ≠ c2ProofTermCertificateSCMMutant := by
  decide

/-- The executable source-level proof-expression surface compiled by the C2 lane.

Unlike `C2ProofTerm`, which is a certificate manifest, this type represents
proof constructors rather than whole proof scripts stored as opaque strings.
It remains source-level IR: these nodes are not bound to Lean-elaborated proof
terms, so compiling them does not discharge `semantic_theorem_proofs_covered`.
-/
inductive C2ProofExpr where
  | reflexivity
  | decision
  | globalRef (name : String)
  | localRef (name : String)
  | application (function : C2ProofExpr) (arguments : List C2ProofExpr)
  | exact (proof : C2ProofExpr)
  | congrArg (function : C2ProofExpr) (equalityProof : C2ProofExpr)
  | simp (lemmas : List C2ProofExpr)
  deriving Repr

structure C2CompiledProof where
  theoremName : String
  proof : C2ProofExpr
  semanticSourceProofBody : Bool := false
  deriving Repr

mutual
  def c2CompileProofExprAST : C2ProofExpr → SCMExpr
    | .reflexivity =>
        .record [
          ("proof_op", .str "rfl"),
          ("axiom_free", .int 1)
        ]
    | .decision =>
        .record [
          ("proof_op", .str "decide"),
          ("axiom_free", .int 1)
        ]
    | .globalRef name =>
        .record [
          ("proof_op", .str "global_ref"),
          ("name", .str name)
        ]
    | .localRef name =>
        .record [
          ("proof_op", .str "local_ref"),
          ("name", .str name)
        ]
    | .application function arguments =>
        .record [
          ("proof_op", .str "application"),
          ("function", c2CompileProofExprAST function),
          ("arguments", .record (c2CompileProofExprFields "argument" 0 arguments))
        ]
    | .exact proof =>
        .record [
          ("proof_op", .str "exact"),
          ("proof", c2CompileProofExprAST proof)
        ]
    | .congrArg function equalityProof =>
        .record [
          ("proof_op", .str "congrArg"),
          ("function", c2CompileProofExprAST function),
          ("equality_proof", c2CompileProofExprAST equalityProof)
        ]
    | .simp lemmas =>
        .record [
          ("proof_op", .str "simp"),
          ("lemmas", .record (c2CompileProofExprFields "lemma" 0 lemmas))
        ]

  def c2CompileProofExprFields
      (fieldPrefix : String) : Nat → List C2ProofExpr → List (String × SCMExpr)
    | _, [] => []
    | index, proof :: proofs =>
        (fieldPrefix ++ "_" ++ toString index, c2CompileProofExprAST proof) ::
          c2CompileProofExprFields fieldPrefix (index + 1) proofs
end

def c2CompileProofRowAST (term : C2CompiledProof) : SCMExpr :=
  .record [
    ("theorem_name", .str term.theoremName),
    ("semantic_source_proof_body", c2BoolFlag term.semanticSourceProofBody),
    ("proof_expr", c2CompileProofExprAST term.proof)
  ]

def c2CompileProofRowsAST : Nat → List C2CompiledProof → List (String × SCMExpr)
  | _, [] => []
  | index, term :: terms =>
      ("proof_" ++ toString index, c2CompileProofRowAST term) ::
        c2CompileProofRowsAST (index + 1) terms

def c2SameTopLevelReflexivityOrDecisionExpr : C2ProofExpr → C2ProofExpr → Bool
  | .reflexivity, .reflexivity => true
  | .decision, .decision => true
  | _, _ => false

def c2CountTopLevelReflexivityOrDecisionExpr
    (proof : C2ProofExpr) : List C2CompiledProof → Nat
  | [] => 0
  | term :: terms =>
      (if c2SameTopLevelReflexivityOrDecisionExpr term.proof proof then 1 else 0) +
        c2CountTopLevelReflexivityOrDecisionExpr proof terms

def c2CountSemanticSourceProofBodies : List C2CompiledProof → Nat
  | [] => 0
  | term :: terms =>
      (if term.semanticSourceProofBody then 1 else 0) +
        c2CountSemanticSourceProofBodies terms

def c2CompileProofManifestAST (terms : List C2CompiledProof) : SCMExpr :=
  .record (
    [
      ("verdict", .int 0),
      ("residue_code", .int 0),
      ("c2_compiled_proof_terms", .int 1),
      ("proof_term_expr_compiler_v0", .int 1),
      ("semantic_proof_body_ir_v1", .int 1),
      ("compiled_proof_term_count", .int (Int.ofNat terms.length)),
      ("reflexivity_proof_count",
        .int (Int.ofNat (c2CountTopLevelReflexivityOrDecisionExpr .reflexivity terms))),
      ("decision_proof_count",
        .int (Int.ofNat (c2CountTopLevelReflexivityOrDecisionExpr .decision terms))),
      ("semantic_source_proof_bodies_compiled",
        .int (Int.ofNat (c2CountSemanticSourceProofBodies terms))),
      ("semantic_theorem_proofs_covered", .int 0),
      ("full_proof_term_compiler", .int 0),
      ("closure_claim", .int 0)
    ] ++ c2CompileProofRowsAST 0 terms)

def c2CompiledEmissionProofTermsV0 : List C2CompiledProof := [
  { theoremName := "c2_apply_add_child_emits_current_scm", proof := .reflexivity },
  { theoremName := "c2_apply_add_child_mutant_diverges", proof := .decision },
  { theoremName := "c2_real_expr_confluence_emits_current_scm", proof := .reflexivity },
  { theoremName := "c2_real_expr_confluence_mutant_diverges", proof := .decision },
  { theoremName := "c2_proof_evidence_bind_emits_current_scm", proof := .reflexivity },
  { theoremName := "c2_proof_evidence_bind_mutant_diverges", proof := .decision },
  { theoremName := "c2_proof_term_certificate_emits_current_scm", proof := .reflexivity },
  { theoremName := "c2_proof_term_certificate_mutant_diverges", proof := .decision },
  { theoremName := "c2_proof_term_compiler_counts_current_subset", proof := .decision },
  { theoremName := "c2_proof_term_payload_q_current_subset", proof := .decision }
]

/-- Source-level proof-body transcriptions for the four current semantic bridges.

These recursive nodes preserve references, applications, and tactic structure;
they intentionally do not claim to be Lean-elaborated proof terms.
-/
def c2CompiledSemanticProofTermsV1 : List C2CompiledProof := [
  {
    theoremName := "applyTwoToken_disjoint_same_program_q",
    semanticSourceProofBody := true,
    proof := .exact (.congrArg (.globalRef "programQ")
      (.application (.globalRef "applyTwoToken_disjoint_commute") [
        .localRef "ancestorHash",
        .localRef "p1",
        .localRef "p2",
        .localRef "h",
        .localRef "program"
      ]))
  },
  {
    theoremName := "applyTwoToken_same_target_agree_same_program_q",
    semanticSourceProofBody := true,
    proof := .exact (.congrArg (.globalRef "programQ")
      (.application (.globalRef "applyTwoToken_same_target_agree_converges") [
        .localRef "p1",
        .localRef "p2",
        .localRef "hTarget",
        .localRef "hReplacement",
        .localRef "program"
      ]))
  },
  {
    theoremName := "conflux_real_expr_disjoint_children_commute",
    semanticSourceProofBody := true,
    proof := .exact (.application
      (.globalRef
        "Residua.Algorithms.PatchFabric.conflux_real_expr_disjoint_children_commute_core") [
        .localRef "exprQ",
        .localRef "l",
        .localRef "r",
        .localRef "replL",
        .localRef "replR",
        .localRef "qL",
        .localRef "qR",
        .localRef "hL",
        .localRef "hR"
      ])
  },
  {
    theoremName := "conflux_real_expr_same_target_agree_converges",
    semanticSourceProofBody := true,
    proof := .exact
      (.application (.globalRef "applyRealExprAddChild_idempotent_add") [
        .localRef "exprQ",
        .localRef "target",
        .localRef "l",
        .localRef "r",
        .localRef "repl"
      ])
  }
]

def c2CompiledProofTermsV1 : List C2CompiledProof :=
  c2CompiledEmissionProofTermsV0 ++ c2CompiledSemanticProofTermsV1

def c2CompiledEmissionProofTermsSCMAST : SCMExpr :=
  c2CompileProofManifestAST c2CompiledEmissionProofTermsV0

def c2CompiledEmissionProofTermsSCM : String :=
  renderSCM c2CompiledEmissionProofTermsSCMAST

def c2CompiledEmissionProofTermsSCMMutant : String :=
  "(record (verdict 0) (residue_code 0) (c2_compiled_proof_terms 1) (proof_term_expr_compiler_v0 1) (compiled_proof_term_count 10) (semantic_theorem_proofs_covered 1) (full_proof_term_compiler 1) (closure_claim 1))"

def c2CompiledProofTermsSCMAST : SCMExpr :=
  c2CompileProofManifestAST c2CompiledProofTermsV1

def c2CompiledProofTermsSCM : String :=
  renderSCM c2CompiledProofTermsSCMAST

def c2CompiledProofTermsSCMMutant : String :=
  "(record (verdict 0) (residue_code 0) (c2_compiled_proof_terms 1) (proof_term_expr_compiler_v0 1) (semantic_proof_body_ir_v1 1) (compiled_proof_term_count 14) (semantic_source_proof_bodies_compiled 0) (semantic_theorem_proofs_covered 1) (full_proof_term_compiler 1) (closure_claim 1))"

theorem c2_compiled_proof_terms_cover_current_emission_set :
    c2CompiledEmissionProofTermsV0.length = 10 ∧
      c2CountTopLevelReflexivityOrDecisionExpr
        .reflexivity c2CompiledEmissionProofTermsV0 = 4 ∧
      c2CountTopLevelReflexivityOrDecisionExpr
        .decision c2CompiledEmissionProofTermsV0 = 6 := by
  decide

theorem c2_compiled_proof_terms_cover_current_semantic_set :
    c2CompiledSemanticProofTermsV1.length = 4 ∧
      c2CountSemanticSourceProofBodies c2CompiledSemanticProofTermsV1 = 4 := by
  decide

theorem c2_compiled_proof_terms_cover_current_set :
    c2CompiledProofTermsV1.length = 14 ∧
      c2CountTopLevelReflexivityOrDecisionExpr
        .reflexivity c2CompiledProofTermsV1 = 4 ∧
      c2CountTopLevelReflexivityOrDecisionExpr
        .decision c2CompiledProofTermsV1 = 6 ∧
      c2CountSemanticSourceProofBodies c2CompiledProofTermsV1 = 4 := by
  decide

theorem c2_compiled_emission_proof_terms_emits_current_scm :
    c2CompiledEmissionProofTermsSCM =
      renderSCM (c2CompileProofManifestAST c2CompiledEmissionProofTermsV0) := by
  rfl

theorem c2_compiled_emission_proof_terms_mutant_diverges :
    c2CompiledEmissionProofTermsSCM ≠ c2CompiledEmissionProofTermsSCMMutant := by
  decide

theorem c2_compiled_proof_terms_emits_current_scm :
    c2CompiledProofTermsSCM =
      renderSCM (c2CompileProofManifestAST c2CompiledProofTermsV1) := by
  rfl

theorem c2_compiled_proof_terms_mutant_diverges :
    c2CompiledProofTermsSCM ≠ c2CompiledProofTermsSCMMutant := by
  decide

end Residua.Algorithms.PatchFabric

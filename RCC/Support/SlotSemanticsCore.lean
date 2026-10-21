import RCC.Support.SHA256

/-!
# Slot semantics core in Lean (#1028, E1.1)

The slot evaluator's MEANING, moved into Lean. Python `interp.eval_` becomes
a removable spoke, not the authority — its conformance to this Lean `evalL`
is the seal.

## Scope

The decidable total CORE fragment only:
  `num, boollit, var, add, sub, mul, neg, lt, lte, gt, gte,
   eqE, andE, orE, notE, ifE, letE`.

Defer to E1.2+ (`[E1_core_only]`): `BoundedFold`, `FindFirst`, temporal,
`MakeRecord`, list/option/result ops, `Call`.

## The float hazard — handled by Int+Bool core ([E1_float_OPEN])

The slot core's `Num.value` is a Python float. Cross-language `native_decide`
on IEEE floats is fragile (repr / rounding / NaN). The architect's spec
recommends an Int+Bool `Val` for E1.1; the Python emitter restricts
conformance fixtures to integer-valued arithmetic (`Num n` where
`n.is_integer()` maps to `Int n`). NO TOLERANCE is introduced to force
float agreement (R2 red line §15). Float-valued semantics is a later
brick: needs a rational/float Lean model + a tolerance-free exact-repr
argument.

## Role isolation (Klaus 2026-06-07)

I (local cc) author the Lean semantics here. The architect authors the
Python conformance emitter `slot_semantics_core_fixtures.py` (running the
REAL `interp.eval_` per fixture, `--lean`-emitting
`MSTNFSlotSemanticsCoreFixturesGen.lean` with `theorem
allFixturesEvalAgree : allFixturesEval fixtures = true := by
native_decide`). Neither side audits its own; the machine decides.

The frozen public interface (so the emitter builds against it in parallel):
  * `inductive Val { int : Int → Val ; bool : Bool → Val }`
  * `abbrev Env := List (String × Val)`
  * `inductive Expr { num, boollit, var, add, sub, mul, neg, lt, lte, gt,
                      gte, eqE, andE, orE, notE, ifE, letE }`
  * `def evalL : Expr → Env → Option Val`
  * `structure GenFixture { name : String, expr : Expr, env : Env,
                            pythonVal : Option Val }`
  * `def checkFixture, allFixturesEval`
-/

namespace MSTNFSlotSemanticsCoreMWE

/-! ## §1 — Values and environments -/

/-- Slot core values. E1.1 had `int + bool`; E1.2 (#1030) extends with `list`
    and `opt` so the list fragment's residual values (`ListFirst []` /
    `ListLast []` return Option in the host) are well-typed. `opt` is used
    by the list-residue path even though Option-Expr nodes (`SomeE`,
    `NoneLit`, `IsNoneE`, etc.) are deferred to E1.3+ (`[E1_core_only]`). -/
inductive Val
  | int    : Int → Val
  | bool   : Bool → Val
  | list   : List Val → Val
  | opt    : Option Val → Val
  -- E1.6 (#1038): record — an ordered list of (field-name, value) pairs.
  -- Records are dedup'd by `insertField` during construction so a field
  -- appears at most once (matching host Python dict's last-write-wins on
  -- key collision, while preserving insertion order).
  | record : List (String × Val) → Val
  -- E1.7 (#1040): Result — two constructors mirror the host's
  -- `('ok', v)` / `('err', v)` tuple tags (interp.eval_). Both carry a `Val`
  -- payload; the tag-as-constructor encoding avoids an indirection layer.
  | ok    : Val → Val
  | err   : Val → Val
  -- E1.15 (#1057): first-class Residue ρ — the MST-NF root concept as a
  -- value. Mirrors `ok`/`err` shape; host tuple form `('residue', payload)`.
  -- This is a NAMED residue (legitimate terminal output), distinct from
  -- Err ("something went wrong").
  | residue : Val → Val
  -- E1.str (#1653 carve 1): the string fragment. `intToStr`/`strLit`/
  -- `strCharAt`/`strSubstring` produce strings; the wasm runtime tags them
  -- `{"tag":"str","s":...}`. Mirrors the host's `('str', s)` tuple form.
  | str : String → Val
  deriving Repr

-- Recursive Bool equality on `Val`. `DecidableEq` cannot be auto-derived on
-- a recursive inductive with a `List Self` constructor in current Lean 4;
-- we mutually-define beq and use it inside `evalL` for `.eqE`.
mutual
def beqVal : Val → Val → Bool
  | .int x,         .int y         => x == y
  | .bool x,        .bool y        => x == y
  | .list xs,       .list ys       => beqValList xs ys
  | .opt none,      .opt none      => true
  | .opt (some x),  .opt (some y)  => beqVal x y
  | .record xs,     .record ys     => beqRecord xs ys
  | .ok x,          .ok y          => beqVal x y
  | .err x,         .err y         => beqVal x y
  | .residue x,     .residue y     => beqVal x y
  | .str x,         .str y         => x == y
  | _, _ => false
def beqValList : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => beqVal x y && beqValList xs ys
  | _, _ => false
def beqRecord : List (String × Val) → List (String × Val) → Bool
  | [], [] => true
  | (k1, v1) :: xs, (k2, v2) :: ys => (k1 == k2) && beqVal v1 v2 && beqRecord xs ys
  | _, _ => false
end

instance : BEq Val := ⟨beqVal⟩

/-- An environment: a list of `(name, value)` bindings. Newer bindings
    shadow older ones via `lookup`. `String → Option Val` would also work;
    `List` is convenient for `Repr` and emitter output. -/
abbrev Env := List (String × Val)

/-- Look up `x` in `env`; `none` is the typed residue for an unbound name
    (never silent). The most recent binding shadows earlier ones. -/
def lookup (env : Env) (x : String) : Option Val :=
  match env with
  | []              => none
  | (y, v) :: rest  => if x = y then some v else lookup rest x

/-! ## §2 — The core expression language -/

/-- The CORE total fragment of the slot expression language.
    Decidable; no list / option / result / temporal / call operators. -/
inductive Expr
  | num     : Int → Expr
  | boollit : Bool → Expr
  | var     : String → Expr
  | add     : Expr → Expr → Expr
  | sub     : Expr → Expr → Expr
  | mul     : Expr → Expr → Expr
  -- E1.11 (#1053, revised): only `mod` lands in evalLF (host `Div` stays float;
  -- evalLF has no Float so Div is outside the conformance domain). `mod` is
  -- floor mod (matches Python `%` = `Int.fmod`). Mod-by-zero ⇒ `none`
  -- (typed residue `[E1.11_mod_by_zero]` host-side).
  | mod     : Expr → Expr → Expr
  -- E1.11b (#1059): Div (TRUE division, host Python `/`), AbsE, MinE, MaxE.
  -- Div returns Int ONLY on EXACT division (`x % y = 0`); non-exact ⇒
  -- `none` (the `[E1_float_OPEN]` boundary — host returns non-int float).
  -- Div-by-zero ⇒ `none`. AbsE/MinE/MaxE are total integer ops.
  | div     : Expr → Expr → Expr
  | absE    : Expr → Expr
  | minE    : Expr → Expr → Expr
  | maxE    : Expr → Expr → Expr
  | neg     : Expr → Expr
  | lt      : Expr → Expr → Expr
  | lte     : Expr → Expr → Expr
  | gt      : Expr → Expr → Expr
  | gte     : Expr → Expr → Expr
  | eqE     : Expr → Expr → Expr
  | andE    : Expr → Expr → Expr
  | orE     : Expr → Expr → Expr
  | notE    : Expr → Expr
  | ifE     : Expr → Expr → Expr → Expr
  | letE    : String → Expr → Expr → Expr
  -- E1.2 (#1030): the list fragment. Mirror interp.eval_ exactly.
  -- Deferred (E1.4+): ListWindow / ListDrop / ListIndexed / BoundedFold /
  -- FindFirst (`[E1_core_only]` shrinks tier by tier).
  | emptyList     : Expr
  | listSingleton : Expr → Expr
  | listAppend    : Expr → Expr → Expr
  | listLen       : Expr → Expr
  | listFirst     : Expr → Expr
  | listLast      : Expr → Expr
  -- E1.3 (#1032): the Option fragment. `Val.opt` already exists (added in E1.2
  -- for the ListFirst/ListLast residue path); here we add the Option-Expr nodes
  -- that produce / inspect / unwrap it. Host (interp.eval_):
  --   NoneLit()       → None                                → opt none
  --   SomeE v         → ('some', ev v)                      → opt (some <v>)
  --   IsNoneE opt     → ev(opt) is None                     → bool
  --   IsSomeE opt     → tuple-shape (... = 'some')          → bool
  --   UnwrapSome opt  → x  if ('some',x);  raise on None;
  --                     else return ev unchanged (bare-value passthrough quirk)
  -- evalL is type-strict (typed residue on type mismatch). Architect commits
  -- fixtures stay well-typed; we honor the host's only-on-Option behavior on
  -- well-typed inputs and emit `none` (typed residue) on non-Option arguments
  -- — naming the divergence rather than weakening evalL (§15).
  | noneLit    : Expr
  | someE      : Expr → Expr
  | isNoneE    : Expr → Expr
  | isSomeE    : Expr → Expr
  | unwrapSome : Expr → Expr
  -- E1.4 (#1034): BoundedFold — the core's ONLY looping node. All loops are
  -- bounded by list length; `evalL` stays total. Host:
  --   BoundedFold lst init accVar itemVar body =>
  --     acc := ev init
  --     for item in ev lst: acc := eval_ body { ..env, accVar:acc, itemVar:item }
  --     return acc
  -- Termination shape (see `termination_by` block below): mutual evalL/evalFold
  -- with a lex measure `(sizeOf body-or-Expr, sizeOf xs + 1)` — the outer
  -- structural-on-Expr arm hands off to a structural-on-List inner arm where
  -- `body` is fixed.
  | boundedFold : Expr → Expr → String → String → Expr → Expr
  -- E1.5 (#1036): the remaining CLEAN list ops — no new `Val` needed.
  -- Host (interp.eval_):
  --   ListDrop lst n   → ev(lst)[int(ev n):]                    -- → list
  --   ListWindow lst k → [xs[i:i+k] for i in range(len(xs)-k+1)] -- → list of lists
  -- Note: `listWindow`'s `k` is a **literal Nat on the node**, not an Expr
  -- (matches the host's `ListWindow.k : int`). `listDrop`'s `n` IS an Expr
  -- (evaluated to a `.int`). On negative `n`, Python's `[neg:]` gives the
  -- tail-N elements; Lean's `Int.toNat` collapses to 0 (whole list). This
  -- is a NAMED divergence ([E1_listdrop_neg_OPEN]) — architect commits
  -- fixtures stay n ≥ 0; weakening evalL is NOT on the table (§15).
  | listDrop   : Expr → Expr → Expr
  | listWindow : Expr → Nat → Expr
  -- E1.6 (#1038): the record fragment. Host:
  --   MakeRecord fields   → {k: ev v for (k, v) in fields}     -- ordered dict
  --   FieldAccess rec f   → ev(rec)[f]                          -- KeyError if miss
  -- `makeRecord` carries fields as `List (String × Expr)` (key + value-expr).
  -- `fieldAccess` carries a literal `String` field name.
  -- evalL:
  --   * makeRecord builds via `evalFields` (mutual member) + `insertField`
  --     dedup (host last-write-wins on duplicate keys); per-field residue
  --     aborts with `none`.
  --   * fieldAccess: rec must be `.record kvs`; missing key → `none` (typed
  --     residue; host raises KeyError); non-record → `none`.
  | makeRecord  : List (String × Expr) → Expr
  | fieldAccess : Expr → String → Expr
  -- E1.7a (#1040): ListIndexed — `[{slot_idx: i, slot_item: x} for i,x in enumerate(lst)]`.
  | listIndexed : Expr → Expr
  -- E1.7b (#1040): Result fragment. Host (`interp.eval_`):
  --   OkE v   → ('ok', ev v)                      → .ok v
  --   ErrE v  → ('err', ev v)                     → .err v
  --   IsOkE r → tuple-shape (r[0] = 'ok')         → .bool
  --   GetOk r → r[1] if 'ok' else raise           → typed residue on non-Ok
  -- evalL is type-strict (typed residue `none` on non-Result arguments)
  -- — same discipline as Option (E1.3). Architect's fixtures stay
  -- well-typed; weakening evalL is NOT on the table (§15).
  | okE         : Expr → Expr
  | errE        : Expr → Expr
  | isOkE       : Expr → Expr
  | getOk       : Expr → Expr
  -- E1.15 (#1057): first-class Residue ρ Expr ops, mirror okE/isOkE/getOk.
  | residueE    : Expr → Expr   -- construct a `Val.residue payload`.
  | isResidueE  : Expr → Expr   -- → `.bool` (true iff arg is `.residue _`).
  | getResidue  : Expr → Expr   -- project payload; residue if not `.residue`.
  -- E1.8 (#1042): the last core nodes — folds binding a record per item.
  -- All three are bounded folds: structural-on-list with `pred`/`mapE`/`stop`
  -- sub-Exprs fixed across iterations (same shape as BoundedFold). Termination
  -- discharged by the same lex `(sizeOf <sub-Expr-sum>, list-len + 1)` measure.
  --
  -- FindFirst(lst, idxVar, itemVar, pred, mapE):
  --   for i,x in enumerate(lst):
  --     env' = {**env, itemVar: {slot_idx: i, slot_item: x}}
  --     if eval pred env': return ('some', eval mapE env')
  --   return None
  -- NOTE: `idxVar` is in the AST (matches host) but the host does NOT bind it
  -- in `new_env` — only `itemVar` is bound (to the slot_indexed record). Lean
  -- mirrors this dead-AST-field for fidelity.
  | findFirst       : Expr → String → String → Expr → Expr → Expr
  -- AlwaysUntil(lst, fromT, itemVar, pred, stop):
  --   for item in lst:
  --     t := item.t (or 0); skip if t ≤ from_t
  --     env' = {**env, itemVar: item}
  --     if eval stop env': return True (stop fired, pred held to here)
  --     if not eval pred env': return False
  --   return True
  | alwaysUntil     : Expr → Expr → String → Expr → Expr → Expr
  -- EventuallyAfter(lst, fromT, itemVar, pred):
  --   for item in lst:
  --     t := item.t (or 0); skip if t ≤ from_t
  --     env' = {**env, itemVar: item}
  --     if eval pred env': return True
  --   return False
  | eventuallyAfter : Expr → Expr → String → Expr → Expr
  -- E1.10 (#1047): BoundedFix — bounded fixpoint iteration. Grows from the
  -- machine-exhibited residue `[DSL_no_bounded_fixpoint]` (the
  -- collision_fixpoint_probe.py finding): iterate-a-state-until-a-predicate
  -- can NOT be expressed with the existing 38-node fragment (BoundedFold has
  -- no stop predicate; AlwaysUntil/EventuallyAfter return Bool, not state).
  --
  -- Semantics (fuel-bounded ⇒ evalL stays TOTAL — the property that makes
  -- it the clean authority):
  --   s := eval state0
  --   for i in 0..<fuel:
  --     if stopPred (env with stepVar↦s) is true: return converged
  --     s := stepBody (env with stepVar↦s)
  --   -- post-loop check: stopPred on the post-final-step state
  --   converged := stopPred (env with stepVar↦s)
  --   return .record [("converged", bool), ("state", s), ("steps", Nat)]
  --
  -- The named return shape exposes the typed residue of fuel exhaustion:
  -- `converged = false` means "fuel ran out, state did not satisfy stopPred".
  -- Caller (Python adapter / runtime) sees the residue, not a silent failure.
  --
  -- BoundedFold relationship: BoundedFold is BoundedFix specialised to
  -- `stopPred = false`, `fuel = list.length`, state threaded as acc. Kept
  -- as a separate node (not merged) — distinct shapes for distinct ρ-bricks.
  | boundedFix : Expr → String → Expr → Expr → Nat → Expr
  -- E1.9 (#1045): Call — named application against the Programs table.
  -- Host (`interp.py:158`):
  --   case Call(fn_name, args):
  --     check progs[fn_name] exists  (else SlotError)
  --     check len(args) == len(param_names)  (else SlotError)
  --     call_env = {p: ev(a) for p, a in zip(param_names, args)}
  --     return eval_(fn_expr, call_env, progs)        ← progs threaded → recursion permitted
  -- Klaus's decision: PATH A (fuel-bound): evalLF threads `programs + fuel`; Call
  -- consumes 1 fuel; fuel = 0 → typed residue `[E1.9_fuel_exhausted]`.
  -- Lex termination measure `(fuel, sizeOf e)` — Call drops fuel, every
  -- other node drops sizeOf. Wrapper `evalL e env := evalLF e env [] N`
  -- keeps existing 60+ non-Call tests' signatures unchanged.
  | call : String → List Expr → Expr
  -- E1.12 (#1054): GroupBy — the quotient q as a first-class node.
  -- `groupBy list itemVar keyBody`: evaluate list, bind itemVar per item,
  -- evaluate keyBody → key; partition items by `beqVal`-equality of key;
  -- return `.list` of `.record [("key", k), ("items", .list items)]` in
  -- first-seen key order. Residue (`none`) if list isn't `.list` or
  -- keyBody residues on any item.
  | groupBy : Expr → String → Expr → Expr
  -- E1.13 (#1055): OrderBy — total stable sort by int key.
  -- `orderBy list itemVar keyBody descending`: pre-evaluate `keyBody` per
  -- item (must be `.int`; non-int ⇒ `none`); sort items stably by key
  -- (ascending, or descending if flag). Stable = ties keep input order.
  -- Residue (`none`) if list isn't `.list` or keyBody non-int on any item.
  | orderBy : Expr → String → Expr → Bool → Expr
  -- E1.14 (#1056): ListTake — prefix slice, dual of `listDrop`.
  -- `listTake list n`: return first `min(n.toNat, length)` elements;
  -- clamps n ≤ 0 → `[]` (via `Int.toNat`), n ≥ len → whole list.
  | listTake : Expr → Expr → Expr
  -- E1.16 (#1063): sheaf-gluing operator — the #6 spatial axis as DSL
  -- primitive. Closes `[spatial_axis_OPEN]`.
  --   `glue sections`: sections must evaluate to `Val.list` of `Val.record`
  --   (partial maps). Fold into the consistent union: each overlapping key
  --   must AGREE (via `beqVal`); the first conflicting overlap surfaces as
  --   the residue
  --     `Val.residue (Val.record [(k, Val.record [("a", va), ("b", vb)])])`
  --   — k is the conflicting key (encoded as the outer record's field-name
  --   because Val has no `.str` ctor; the inner record carries the
  --   conflicting payloads). Non-list / non-record arg ⇒ `none`. Mirrors
  --   the host `Glue` node in `tools/mstspec/ir/slot/slot_ast.py`.
  | glue : Expr → Expr
  -- E1.17 (#1064): RDC discharge-propagation operator — runtime instance
  -- of `RDCUnifiedFramework.ResidueImplication`.
  --   `dischargeProp residuesE edgesE`: residues = list of records
  --   `{"id": Int, "discharged": Bool}`; edges = list of records
  --   `{"from": Int, "to": Int}` (the implication DAG).
  --   Monotone discharge-closure to fixpoint. Pinned residue shape:
  --     * all discharged → `.record [("discharged", .list ids), ("present", .list [])]`
  --     * some present   → `.residue (.record [("present", .list ids)])`
  --     * type error / dangling id ⇒ `none`.
  --   Insertion order on ids (no sort) — matches host. Integer-core (no
  --   `Val.str`). Mirrors host `DischargeProp` in slot_ast.py.
  | dischargeProp : Expr → Expr → Expr
  -- E1.18 (#1065): substructural use-count operator — the #7 linear axis
  -- as a DSL primitive. Runtime instance of `SubstructuralUseCountNF`.
  --   `useCountCheck usagesE`: usages = list of resource-id ints (trace).
  --   Tally per-id; linearity gate = `count ≤ 1` per resource.
  --   Pinned shape (integer-core, insertion order on first-seen):
  --     * all linear  → `.record [("linear", .list ids), ("overused", .list [])]`
  --     * some over   → `.residue (.record [("overused", .list witnesses)])`
  --         witness = `.record [("resource", .int id), ("count", .int n)]`
  --     * non-int element ⇒ `none`.
  --   Mirrors host `UseCountCheck` in slot_ast.py.
  | useCountCheck : Expr → Expr
  -- E1.19 (#1070): closed-tag exhaustive match — control-flow checkability
  -- via INTEGER-CORE tag dispatch (NO `Val.str`). Runtime semantics: scrut
  -- evaluates to an `.int` tag; first-match the `arms` list; if no arm
  -- matches, evaluate `default` (which the emitter pins to a `ResidueE` for
  -- never-silent residue surfacing). `universe` = declared closed tag-set,
  -- NOT consulted at runtime — checked by the decidable `matchExhaustive`
  -- admission predicate. Non-int scrut → `none` (type residue).
  --   `matchTag scrut universe arms default`:
  --     scrut    : Expr           — evaluated to `.int tag`
  --     universe : List Int       — admission metadata (declared tag set)
  --     arms     : List (Int × Expr) — first-match arm list (tag → body)
  --     default  : Expr           — residue-pinned fall-through
  | matchTag : Expr → List Int → List (Int × Expr) → Expr → Expr
  -- E1.str (#1653 carve 1): the string fragment. All ops operate on CODE POINTS
  -- (Unicode scalars), matching the wasm engine's code-point floor — NOT UTF-8
  -- bytes. `café` has length 4, `café[3] = é` (U+00E9), `Ωλ[0]` code = 937.
  -- Indices are code-point indices; OOB / negative / type-mismatch ⇒ `none`.
  -- `strSubstring i j` is a total clamped half-open slice (Python-clamp):
  -- start = max(0,i), end = clamp(j,0,len), empty if start ≥ end.
  | strLit       : String → Expr
  | strLen       : Expr → Expr
  | strCharAt    : Expr → Expr → Expr
  | strCodeAt    : Expr → Expr → Expr
  | strSubstring : Expr → Expr → Expr → Expr
  | intToStr     : Expr → Expr
  -- E1.str (#1653 carve 1): contentHash = sha256_hex ∘ reifyVal. Produces a
  -- `.str` holding 64 lowercase hex chars, identical to the wasm engine.
  | contentHash  : Expr → Expr
  deriving Repr

/-- E1.9 (#1045): a `Programs` table maps program names to
    `(param-names, body-Expr)` pairs. `Call` resolves names via this table.
    Recursive / mutual programs are supported (host permits this); evalLF
    threads a fuel parameter to keep totality. -/
abbrev Programs := List (String × (List String × Expr))

/-- Look up a program by name. -/
def progLookup : Programs → String → Option (List String × Expr)
  | [],               _    => none
  | (n, prog) :: rest, name => if name = n then some prog else progLookup rest name

/-- Build a fresh env from parallel param-name and arg-value lists. Returns
    `none` on arity mismatch. Matches host's
    `{p: ev(a) for p, a in zip(param_names, args)}` — fresh scope, NOT
    closure over caller env. -/
def buildCallEnv : List String → List Val → Option Env
  | [],       []         => some []
  | p :: ps,  v :: vs    =>
      match buildCallEnv ps vs with
      | some rest => some ((p, v) :: rest)
      | none      => none
  | _, _ => none

/-- Insert `(k, v)` into a record-shaped list, preserving insertion order and
    OVERWRITING any prior binding for `k`. Mirrors Python's dict
    last-write-wins: `{a: 1, b: 2, a: 3}` ⇒ `{a: 3, b: 2}` (key 'a' keeps its
    first-insertion position, value becomes 3). Used by `evalFields` so that
    `Val.record` always carries at most one entry per key. -/
def insertField (k : String) (v : Val) : List (String × Val) → List (String × Val)
  | []              => [(k, v)]
  | (k', v') :: rest =>
      if k = k' then (k, v) :: rest
      else (k', v') :: insertField k v rest

/-- E1.8 (#1042): extract the `t` field from a record-shaped item; mirrors
    host `item.get('t', 0) if isinstance(item, dict) else 0`. Used by
    `AlwaysUntil` and `EventuallyAfter` for the `from_t` time-gate. Returns
    `0` for non-record items OR records lacking a `t` field OR records
    where the `t` field is non-`.int`. Architect commits items to be
    well-typed records with `t : .int`; the default-`0` quirk is named
    here, not papered over (§12). -/
def itemT (v : Val) : Int :=
  match v with
  | .record kvs =>
      match kvs.find? (·.1 = "t") with
      | some (_, .int t) => t
      | _                => 0
  | _ => 0

/-- E1.7a (#1040): build the list of `{slot_idx: i, slot_item: x}` records
    that mirrors host `[{"slot_idx": i, "slot_item": x} for i, x in
    enumerate(xs)]`. Field names + position match the host record shape
    exactly (slot_idx FIRST then slot_item, both required for FindFirst /
    AlwaysUntil / EventuallyAfter binding patterns in E1.8). -/
def indexedRecords : Nat → List Val → List Val
  | _, []          => []
  | i, x :: rest   =>
      (Val.record [("slot_idx", .int (Int.ofNat i)), ("slot_item", x)])
        :: indexedRecords (i + 1) rest

/-- Size-`k` windows of `xs`, mirroring host
    `[xs[i:i+k] for i in range(len(xs)-k+1)]`. Returns `[]` when `k > len xs`
    (the host's `range(negative)` is empty). Note `k = 0` gives `n+1` empty
    windows (one for each starting position), matching the host. -/
def windowsOfSize (k : Nat) (xs : List Val) : List (List Val) :=
  let n := xs.length
  if k > n then []
  else (List.range (n - k + 1)).map (fun i => (xs.drop i).take k)

/-- E1.12 (#1054): `addToGroupKey k x acc` — find bucket for key `k` in
    `acc` (using `beqVal` for structural equality); if found, append `x` to
    that bucket's items (preserving item order); if not found, append a new
    bucket `(k, [x])` at the END of `acc` (preserving first-seen key order).
    Pure list-walk; structurally recursive on `acc`. -/
def addToGroupKey (k : Val) (x : Val) :
    List (Val × List Val) → List (Val × List Val)
  | []                  => [(k, [x])]
  | (k', items) :: rest =>
      if beqVal k k'
      then (k', items ++ [x]) :: rest
      else (k', items) :: addToGroupKey k x rest

/-- E1.13 (#1055): `insertByKey asc k v acc` — insert `(k, v)` into the
    sorted-by-key `acc`. For `asc = true`: ascending sort. For `asc = false`:
    descending. **Stable**: when inserting a new pair with key equal to some
    existing pair, the new pair goes AFTER the existing (since the predicate
    is strict). -/
def insertByKey (asc : Bool) (k : Int) (v : Val) :
    List (Int × Val) → List (Int × Val)
  | [] => [(k, v)]
  | (k', v') :: rest =>
      let goBefore := if asc then k < k' else k > k'
      if goBefore then (k, v) :: (k', v') :: rest
      else (k', v') :: insertByKey asc k v rest

/-- E1.13 helper: build sorted list by processing input left-to-right,
    inserting each (key, value) into the sorted prefix via `insertByKey`. -/
def stableSortByKey (asc : Bool) :
    List (Int × Val) → List (Int × Val) → List (Int × Val)
  | acc, []             => acc
  | acc, (k, v) :: rest => stableSortByKey asc (insertByKey asc k v acc) rest

/-! ## §3 — `evalL`: the Lean semantics

Total, decidable. Type mismatches and unbound names yield `none` (typed
residue: a value cannot be produced, never silently produced a wrong one).
Order of arg evaluation is left-then-right; `letE x e body` evaluates `e`
first, then `body` in the extended environment. -/

/-- E1.16 (#1063): the gluing-conflict result. `.ok` carries the updated
    accumulator (no conflict so far); `.conflict k va vb` carries the first
    overlap mismatch (the key plus the two conflicting Val payloads). Used
    by `mergeSectionInto` / `evalGlue` inside the evalLF mutual block. -/
inductive GlueStep
  | ok       : List (String × Val) → GlueStep
  | conflict : String → Val → Val → GlueStep

/-! ## §3a — i64 range floor (wasm |= Lean parity, #1653 carve 2)

The wasm runtime stores every `Num` as a signed i64. An arithmetic result that
falls outside `[-2^63, 2^63-1]` saturates to `none` (typed residue) on the wasm
side; Lean's `Int` is arbitrary-precision, so without this guard evalLF would
return the out-of-range bignum and DIVERGE from wasm (e.g. `add(2^63-1,1)`:
wasm `none` vs Lean `2^63`). The guard makes the two engines agree. `minE`/
`maxE` only SELECT an operand (no new value) so they never overflow. -/

def i64Min : Int := -9223372036854775808
def i64Max : Int := 9223372036854775807

/-- Membership in the signed i64 range — the saturation boundary the wasm
    engine enforces on every arithmetic op (add/sub/mul/neg/absE). -/
def inI64Range (n : Int) : Bool := i64Min ≤ n ∧ n ≤ i64Max

/-! ## §3a' — `reifyVal` (wasm `reify_val` parity, #1653 carve 1 contentHash)

The wasm `contentHash` op is `sha256_hex ∘ reify_val` over a canonical string
form. This Lean `reifyVal` reproduces the wasm `$reify_val` byte-for-byte so
`Expr.contentHash` agrees with the wasm engine to the SHA-256 digit. `Num` uses
the wasm float/int split at ±2^53 (`Num(float:<n>.0)` vs `Num(int:<n>)`); str/
record lengths are CODE-POINT counts. This is a runtime serialization, not the
theorem-grade `canonical_repr` of `Residua.Exe.ContentHash.lean`.

#3357 tier 3: TOTAL. Was `partial def` because `kvs.map reifyField` hid the
recursive call from the structural checker (same wall as `valToJson` in
`SlotEval.lean` #1049). Mutual block + structural-on-list helpers
(`reifyList`, `reifyFields`) make the recursion visible. Output bytes are
identical to the prior `partial` (intercalate+map on fields is the same
join). Kernel can now δ-reduce it; equation lemmas exist. -/

def floatMax : Int := 9007199254740992   -- 2^53, the wasm float/int reify split

mutual
def reifyVal : Val → String
  | .int n =>
      if -floatMax ≤ n ∧ n ≤ floatMax then "Num(float:" ++ toString n ++ ".0)"
      else "Num(int:" ++ toString n ++ ")"
  | .bool b => "BoolLit(bool:" ++ (if b then "True" else "False") ++ ")"
  | .str s => "StrLit(str:" ++ toString s.length ++ ":" ++ s ++ ")"
  | .opt none => "NoneLit()"
  | .opt (some v) => "SomeE(" ++ reifyVal v ++ ")"
  | .list xs => reifyList xs
  | .record kvs => "MakeRecord([" ++ reifyFields kvs ++ "])"
  | .ok v => "OkE(" ++ reifyVal v ++ ")"
  | .err v => "ErrE(" ++ reifyVal v ++ ")"
  | .residue v => "ResidueE(" ++ reifyVal v ++ ")"

/-- Structural-on-list helper for `Val.list`. -/
def reifyList : List Val → String
  | [] => "EmptyListE()"
  | v :: rest => "ListAppend(ListSingleton(" ++ reifyVal v ++ ")," ++ reifyList rest ++ ")"

/-- Structural-on-list helper for `Val.record`. Same join as
    `String.intercalate "," (kvs.map reifyField)` — the recursive call is
    now a constructor split Lean can see. -/
def reifyFields : List (String × Val) → String
  | [] => ""
  | (k, v) :: [] => "[str:" ++ toString k.length ++ ":" ++ k ++ "," ++ reifyVal v ++ "]"
  | (k, v) :: rest =>
      "[str:" ++ toString k.length ++ ":" ++ k ++ "," ++ reifyVal v ++ "],"
        ++ reifyFields rest
end

set_option maxHeartbeats 1000000 in
mutual

/-- E1.9 (#1045): fueled evalL core. Threads `Programs` (the name→body table)
    and `Nat` fuel (decrements only at `.call`, matching the host's recursive
    Call semantics). Lex termination measure `(fuel, sizeOf e, 0)` — Call drops
    fuel; every other node drops sizeOf. The 2-arg wrapper `evalL` below
    fixes programs := [] and fuel := defaultEvalFuel so existing non-Call
    tests use it unchanged.

    Fuel=0 ⇒ `none` (M-PA-FUEL-EXHAUST-AS-VALUE, #1653 carve 3): a request that
    enters with ZERO budget may not fabricate a value — the first arm below
    refuses before any computation. (Internal Call still consumes 1 fuel via its
    own `0 ⇒ none` arm; this entry-guard covers the no-budget-at-all case.) -/
def evalLF : Expr → Env → Programs → Nat → Option Val
  | _, _, _, 0 => none
  | .num n,     _,   _, _ => some (.int n)
  | .boollit b, _,   _, _ => some (.bool b)
  | .var x,     env, _, _ => lookup env x
  -- WP0 [E1.arith_nonint]: non-Int operands already refuse with `none` (named in catalog).
  -- Authority path — no vint→0 coercion. Keep total Option Val (residue-as-none).
  | .add a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => if inI64Range (x + y) then some (.int (x + y)) else none
      | _, _                          => none  -- [E1.arith_nonint]
  | .sub a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => if inI64Range (x - y) then some (.int (x - y)) else none
      | _, _                          => none
  | .mul a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => if inI64Range (x * y) then some (.int (x * y)) else none
      | _, _                          => none
  | .mod a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) =>
          if y = 0 then none else some (.int (Int.fmod x y))
      | _, _                          => none
  -- E1.11b (#1059): Div — TRUE division on exact-integer inputs only.
  | .div a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) =>
          if y = 0 then none
          else if x % y = 0 then some (.int (x / y))
          else none   -- non-exact ⇒ [E1_float_OPEN] boundary; residue
      | _, _                          => none
  | .absE a,    env, p, f =>
      match evalLF a env p f with
      | some (.int x) => let r := Int.ofNat x.natAbs; if inI64Range r then some (.int r) else none
      | _             => none
  | .minE a b,  env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.int (min x y))
      | _, _                          => none
  | .maxE a b,  env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.int (max x y))
      | _, _                          => none
  | .neg a,     env, p, f =>
      match evalLF a env p f with
      | some (.int x) => if inI64Range (-x) then some (.int (-x)) else none
      | _             => none
  | .lt a b,    env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.bool (decide (x < y)))
      | _, _                          => none
  | .lte a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.bool (decide (x ≤ y)))
      | _, _                          => none
  | .gt a b,    env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.bool (decide (x > y)))
      | _, _                          => none
  | .gte a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.int x), some (.int y) => some (.bool (decide (x ≥ y)))
      | _, _                          => none
  | .eqE a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some v1, some v2 => some (.bool (beqVal v1 v2))
      | _, _              => none
  | .andE a b,  env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.bool x), some (.bool y) => some (.bool (x && y))
      | _, _                            => none
  | .orE a b,   env, p, f =>
      match evalLF a env p f, evalLF b env p f with
      | some (.bool x), some (.bool y) => some (.bool (x || y))
      | _, _                            => none
  | .notE a,    env, p, f =>
      match evalLF a env p f with
      | some (.bool x) => some (.bool (!x))
      | _              => none
  | .ifE c t e, env, p, f =>
      match evalLF c env p f with
      | some (.bool true)  => evalLF t env p f
      | some (.bool false) => evalLF e env p f
      | _                  => none
  | .letE x e body, env, p, f =>
      match evalLF e env p f with
      | some v => evalLF body ((x, v) :: env) p f
      | none   => none
  -- E1.2 (#1030): list fragment. Mirrors interp.eval_:
  --   EmptyListE       → []
  --   ListSingleton e  → [ev e]
  --   ListAppend l r   → l ++ r (where both eval to lists; else residue)
  --   ListLen lst      → Int len(lst)        (residue if not a list)
  --   ListFirst []     → opt none            (host: None — a value, not failure)
  --   ListFirst (x::_) → opt (some x)        (host: ('some', x))
  --   ListLast  []     → opt none
  --   ListLast  xs     → opt (some xs.last)  (when nonempty)
  | .emptyList, _, _, _ => some (.list [])
  | .listSingleton e, env, p, f =>
      match evalLF e env p f with
      | some v => some (.list [v])
      | none   => none
  | .listAppend l r, env, p, f =>
      match evalLF l env p f, evalLF r env p f with
      | some (.list xs), some (.list ys) => some (.list (xs ++ ys))
      | _, _ => none
  | .listLen lst, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) => some (.int (Int.ofNat xs.length))
      | _               => none
  | .listFirst lst, env, p, f =>
      match evalLF lst env p f with
      | some (.list [])        => some (.opt none)
      | some (.list (x :: _))  => some (.opt (some x))
      | _                      => none
  | .listLast lst, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) =>
          match xs.getLast? with
          | some x => some (.opt (some x))
          | none   => some (.opt none)
      | _ => none
  -- E1.3 (#1032): Option fragment.
  | .noneLit, _, _, _ => some (.opt none)
  | .someE e, env, p, f =>
      match evalLF e env p f with
      | some v => some (.opt (some v))
      | none   => none
  | .isNoneE e, env, p, f =>
      match evalLF e env p f with
      | some (.opt none)     => some (.bool true)
      | some (.opt (some _)) => some (.bool false)
      | _                    => none
  | .isSomeE e, env, p, f =>
      match evalLF e env p f with
      | some (.opt none)     => some (.bool false)
      | some (.opt (some _)) => some (.bool true)
      | _                    => none
  | .unwrapSome e, env, p, f =>
      match evalLF e env p f with
      | some (.opt (some v)) => some v
      | some (.opt none)     => none
      | _                    => none
  -- E1.4 (#1034): BoundedFold. Eval `lst` (must be a list) and `init`, then
  -- hand off to the inner `evalFold` over the list with `body` fixed. Typed
  -- residue (`none`) if `lst` doesn't evaluate to a list or `init` residues.
  | .boundedFold lst init accVar itemVar body, env, p, f =>
      match evalLF lst env p f, evalLF init env p f with
      | some (.list xs), some initV =>
          evalFold body accVar itemVar env initV p f xs
      | _, _ => none
  | .listDrop lst nE, env, p, f =>
      match evalLF lst env p f, evalLF nE env p f with
      | some (.list xs), some (.int n) => some (.list (xs.drop n.toNat))
      | _, _ => none
  | .listWindow lst k, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) => some (.list ((windowsOfSize k xs).map Val.list))
      | _               => none
  | .makeRecord fields, env, p, f => evalFields fields env [] p f
  | .fieldAccess rec field, env, p, f =>
      match evalLF rec env p f with
      | some (.record kvs) => (kvs.find? (·.1 = field)).map (·.2)
      | _ => none
  | .listIndexed lst, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) => some (.list (indexedRecords 0 xs))
      | _               => none
  | .okE e, env, p, f =>
      match evalLF e env p f with
      | some v => some (.ok v)
      | none   => none
  | .errE e, env, p, f =>
      match evalLF e env p f with
      | some v => some (.err v)
      | none   => none
  | .isOkE e, env, p, f =>
      match evalLF e env p f with
      | some (.ok  _) => some (.bool true)
      | some (.err _) => some (.bool false)
      | _             => none
  | .getOk e, env, p, f =>
      match evalLF e env p f with
      | some (.ok v)  => some v
      | some (.err _) => none
      | _             => none
  -- E1.15 (#1057): Residue ρ Expr ops.
  | .residueE e, env, p, f =>
      match evalLF e env p f with
      | some v => some (.residue v)
      | none   => none
  | .isResidueE e, env, p, f =>
      match evalLF e env p f with
      | some (.residue _) => some (.bool true)
      | some _            => some (.bool false)
      | none              => none
  | .getResidue e, env, p, f =>
      match evalLF e env p f with
      | some (.residue v) => some v
      | _                 => none
  | .findFirst lst idxVar itemVar pred mapE, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) => evalFindFirst idxVar itemVar pred mapE env p f 0 xs
      | _               => none
  | .alwaysUntil lst fromT itemVar pred stopE, env, p, f =>
      match evalLF lst env p f, evalLF fromT env p f with
      | some (.list xs), some (.int t0) =>
          evalAlwaysUntil itemVar pred stopE env t0 p f xs
      | _, _ => none
  | .eventuallyAfter lst fromT itemVar pred, env, p, f =>
      match evalLF lst env p f, evalLF fromT env p f with
      | some (.list xs), some (.int t0) =>
          evalEventuallyAfter itemVar pred env t0 p f xs
      | _, _ => none
  | .boundedFix state0 stepVar stepBody stopPred bfFuel, env, p, f =>
      match evalLF state0 env p f with
      | some s0 => evalFix stepVar stepBody stopPred env s0 0 p f bfFuel
      | none    => none
  -- E1.9 (#1045): Call — named application against the Programs table.
  | .call name args, env, p, f =>
      match evalArgs args env p f with
      | none         => none   -- residue from arg evaluation
      | some argVals =>
          match progLookup p name with
          | none => none          -- unknown program name (host SlotError)
          | some (paramNames, body) =>
              match buildCallEnv paramNames argVals with
              | none         => none   -- arity mismatch (host SlotError)
              | some callEnv =>
                  match f with
                  | 0      => none   -- [E1.9_fuel_exhausted] typed residue
                  | f' + 1 => evalLF body callEnv p f'
  -- E1.12 (#1054): GroupBy — quotient q as first-class.
  | .groupBy lst itemVar keyBody, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) =>
          match evalGroupBy keyBody itemVar env p f xs [] with
          | none        => none   -- key-residue
          | some groups =>
              some (.list (groups.map (fun ⟨k, items⟩ =>
                .record [("key", k), ("items", .list items)])))
      | _ => none
  -- E1.13 (#1055): OrderBy — total stable sort by int key.
  | .orderBy lst itemVar keyBody descending, env, p, f =>
      match evalLF lst env p f with
      | some (.list xs) =>
          match evalOrderByKeys keyBody itemVar env p f xs with
          | none => none   -- non-int key or none = residue
          | some keyed =>
              let sorted := stableSortByKey (!descending) [] keyed
              some (.list (sorted.map (·.2)))
      | _ => none
  -- E1.14 (#1056): ListTake — prefix slice with `Int.toNat` clamping.
  | .listTake lst nE, env, p, f =>
      match evalLF lst env p f, evalLF nE env p f with
      | some (.list xs), some (.int n) => some (.list (xs.take n.toNat))
      | _, _ => none
  -- E1.16 (#1063): Glue — sheaf gluing on records. Eval the sections list;
  -- fold into the consistent union via `evalGlue`. Named-residue surfaces
  -- the first conflicting overlap.
  | .glue sectionsE, env, p, f =>
      match evalLF sectionsE env p f with
      | some (.list secs) => evalGlue secs []
      | _                 => none
  -- E1.17 (#1064): DischargeProp — RDC discharge-propagation. Eval
  -- residues + edges (must both be `.list`); validate shapes and ids;
  -- compute the monotone discharge-closure to fixpoint; return partition
  -- record (all discharged) or named residue (some present).
  | .dischargeProp residuesE edgesE, env, p, f =>
      match evalLF residuesE env p f, evalLF edgesE env p f with
      | some (.list rs), some (.list es) => evalDischargeOuter rs es
      | _, _ => none
  -- E1.18 (#1065): UseCountCheck — tally per-id; partition linear / overused.
  | .useCountCheck usagesE, env, p, f =>
      match evalLF usagesE env p f with
      | some (.list us) => evalUseCountOuter us
      | _ => none
  -- E1.19 (#1070): MatchTag — closed-tag dispatch (control-flow checkability).
  -- `universe` is ADMISSION metadata, NOT consulted at runtime. Runtime is
  -- pure first-match on `arms` + `default` fall-through. Non-int scrutinee
  -- → `none` (type residue). Unmatched in-int tag → evaluate `default`
  -- (the emitter pins it to a `ResidueE` for the never-silent named ρ).
  | .matchTag scrut _universe arms default, env, p, f =>
      match evalLF scrut env p f with
      | some (.int tag) => matchArms default env p f tag arms
      | _               => none   -- non-int / residue scrut ⇒ type residue
  -- E1.str (#1653 carve 1): string fragment. CODE-POINT semantics (wasm parity).
  | .strLit s, _, _, _ => some (.str s)
  | .strLen a, env, p, f =>
      match evalLF a env p f with
      | some (.str s) => some (.int (Int.ofNat s.length))
      | _             => none
  | .strCharAt a iE, env, p, f =>
      match evalLF a env p f, evalLF iE env p f with
      | some (.str s), some (.int i) =>
          if 0 ≤ i ∧ i.toNat < s.length then
            match s.data.get? i.toNat with
            | some c => some (.str (String.mk [c]))
            | none   => none
          else none   -- negative or ≥ length ⇒ typed residue
      | _, _ => none
  | .strCodeAt a iE, env, p, f =>
      match evalLF a env p f, evalLF iE env p f with
      | some (.str s), some (.int i) =>
          if 0 ≤ i ∧ i.toNat < s.length then
            match s.data.get? i.toNat with
            | some c => some (.int (Int.ofNat (Char.toNat c)))
            | none   => none
          else none
      | _, _ => none
  | .strSubstring a iE jE, env, p, f =>
      match evalLF a env p f, evalLF iE env p f, evalLF jE env p f with
      | some (.str s), some (.int i), some (.int j) =>
          let n : Int := Int.ofNat s.length
          let start := if i < 0 then 0 else if i > n then n else i
          let stop  := if j < 0 then 0 else if j > n then n else j
          let take  := if stop ≤ start then 0 else stop - start
          some (.str (String.mk (s.data.drop start.toNat |>.take take.toNat)))
      | _, _, _ => none
  | .intToStr a, env, p, f =>
      match evalLF a env p f with
      | some (.int n) => some (.str (toString n))
      | _             => none
  | .contentHash a, env, p, f =>
      match evalLF a env p f with
      | some v => some (.str (Residua.SHA256.sha256Hex (reifyVal v)))
      | none   => none

termination_by e _ _ f => (f, sizeOf e, 0)
decreasing_by
  all_goals (
    first
    | decreasing_tactic
    | (try (have h_lst_pos : 1 ≤ sizeOf lst := by cases lst <;> simp_arith)
       try (have h_s0_pos : 1 ≤ sizeOf state0 := by cases state0 <;> simp_arith)
       decreasing_tactic))

/-- The inner list-fold helper for `BoundedFold`. Structurally recursive on
    `xs`; `body` is fixed across iterations. Threads the typed residue —
    any per-step `evalL body` returning `none` aborts the fold with `none`.

    Env-update order mirrors the host `{**env, accVar: acc, itemVar: item}`
    (last write wins on key collision): we prepend `(itemVar, item)` IN FRONT
    of `(accVar, acc)` so `lookup` returns `itemVar`'s binding first if the
    two names collide — matching Python's overwrite semantics. -/
def evalFold (body : Expr) (accVar itemVar : String) (env : Env) (acc : Val)
    (programs : Programs) (fuel : Nat) : List Val → Option Val
  | []           => some acc
  | item :: rest =>
      match evalLF body ((itemVar, item) :: (accVar, acc) :: env) programs fuel with
      | some acc' => evalFold body accVar itemVar env acc' programs fuel rest
      | none      => none
termination_by xs => (fuel, sizeOf body, xs.length + 1)

/-- E1.12 (#1054): the inner item-walk helper for `GroupBy`. Iterate over the
    list-of-items, evaluating `keyBody` per item in `env ++ [(itemVar, item)]`;
    on residue (`none`) abort with `none`; on success append to the matching
    bucket via `addToGroupKey` (preserves first-seen key order). -/
def evalGroupBy (keyBody : Expr) (itemVar : String) (env : Env)
    (programs : Programs) (fuel : Nat) :
    List Val → List (Val × List Val) → Option (List (Val × List Val))
  | [],          acc => some acc
  | item :: rest, acc =>
      match evalLF keyBody ((itemVar, item) :: env) programs fuel with
      | none   => none
      | some k => evalGroupBy keyBody itemVar env programs fuel rest
                    (addToGroupKey k item acc)
termination_by xs _ => (fuel, sizeOf keyBody, xs.length + 1)

/-- E1.13 (#1055): pre-evaluate `(keyBody, item)` pairs for `OrderBy`. For each
    item: bind `itemVar`, evaluate `keyBody`; require `Val.int` (residue
    otherwise); accumulate `(key, item)` pairs preserving input order. -/
def evalOrderByKeys (keyBody : Expr) (itemVar : String) (env : Env)
    (programs : Programs) (fuel : Nat) :
    List Val → Option (List (Int × Val))
  | []           => some []
  | item :: rest =>
      match evalLF keyBody ((itemVar, item) :: env) programs fuel with
      | some (.int k) =>
          match evalOrderByKeys keyBody itemVar env programs fuel rest with
          | none       => none
          | some keyed => some ((k, item) :: keyed)
      | _ => none   -- non-int key or none ⇒ residue
termination_by xs => (fuel, sizeOf keyBody, xs.length + 1)

/-- E1.19 (#1070): first-match arm dispatch for `MatchTag`. Structural
    recursion on `arms`. On match, evaluate the chosen `body`; on arm-list
    exhaustion, evaluate `default`. -/
def matchArms (default : Expr) (env : Env) (programs : Programs) (fuel : Nat) :
    Int → List (Int × Expr) → Option Val
  | _,   []                    => evalLF default env programs fuel
  | tag, (code, body) :: rest =>
      if tag = code then evalLF body env programs fuel
      else matchArms default env programs fuel tag rest
termination_by _ xs => (fuel, sizeOf default + sizeOf xs, xs.length + 1)

/-- E1.16 (#1063): lookup a key in a record-shaped kv list (first occurrence). -/
def recordLookupVal (key : String) :
    List (String × Val) → Option Val
  | []            => none
  | (k, v) :: kvs => if key = k then some v else recordLookupVal key kvs

/-- E1.16 (#1063): walk one section's `(k, v)` pairs into `acc`. For each
    new key, append. For each key already in `acc`, require `beqVal` agreement;
    on disagreement, return `.conflict k va vb` carrying the first witness.
    Structural recursion on the section list. -/
def mergeSectionInto :
    List (String × Val) → List (String × Val) → GlueStep
  | [],            acc => .ok acc
  | (k, v) :: rest, acc =>
      match recordLookupVal k acc with
      | none      => mergeSectionInto rest (acc ++ [(k, v)])
      | some va   =>
          if beqVal va v
          then mergeSectionInto rest acc
          else .conflict k va v
termination_by xs _ => xs.length

/-- E1.16 (#1063): the outer sections fold for Glue. Structural recursion
    on the section list. `.record kvs :: rest` → merge kvs into acc via
    `mergeSectionInto`; on `.conflict` surface the named residue; on `.ok`
    continue with the updated acc. Empty → `Val.record acc`. Non-record
    section ⇒ `none` (type residue, mirrors host SlotError). -/
def evalGlue :
    List Val → List (String × Val) → Option Val
  | [],                    acc => some (.record acc)
  | (.record kvs) :: rest, acc =>
      match mergeSectionInto kvs acc with
      | .ok acc'           => evalGlue rest acc'
      | .conflict k va vb  =>
          some (.residue (.record [(k, .record [("a", va), ("b", vb)])]))
  | _ :: _,                _   => none
termination_by xs _ => xs.length

-- §3a — E1.17 (#1064) helpers for dischargeProp.
-- Parse residue/edge records into typed `(Int × Bool)` / `(Int × Int)`
-- pairs. Membership / validation / monotone fixpoint are pure list walks.

/-- Parse one residue Val into `(id, discharged)`. -/
def parseResidueRec : Val → Option (Int × Bool)
  | .record kvs =>
      match recordLookupVal "id" kvs, recordLookupVal "discharged" kvs with
      | some (.int id), some (.bool d) => some (id, d)
      | _, _ => none
  | _ => none

/-- Walk the residue list. Bail on any non-record / missing-field shape.
    Detects duplicate ids and bails (matches host \[E1.17_duplicate_id]). -/
def parseAllResidues :
    List Val → List Int → Option (List (Int × Bool))
  | [],         _seen => some []
  | r :: rest,  seen  =>
      match parseResidueRec r with
      | none        => none
      | some (i, d) =>
          if seen.contains i then none
          else
            match parseAllResidues rest (i :: seen) with
            | some rs => some ((i, d) :: rs)
            | none    => none

/-- Parse one edge Val into `(from, to)`. -/
def parseEdgeRec : Val → Option (Int × Int)
  | .record kvs =>
      match recordLookupVal "from" kvs, recordLookupVal "to" kvs with
      | some (.int f), some (.int t) => some (f, t)
      | _, _ => none
  | _ => none

def parseAllEdges : List Val → Option (List (Int × Int))
  | []         => some []
  | e :: rest  =>
      match parseEdgeRec e with
      | none => none
      | some (f, t) =>
          match parseAllEdges rest with
          | some es => some ((f, t) :: es)
          | none    => none

/-- `i ∈ ids` (linear-search membership). -/
def memInt : Int → List Int → Bool
  | _, []      => false
  | x, y :: ys => if x = y then true else memInt x ys

/-- Validate that all edge endpoints exist in the id set. -/
def validateEdges (ids : List Int) : List (Int × Int) → Bool
  | []            => true
  | (f, t) :: es  =>
      if memInt f ids && memInt t ids then validateEdges ids es else false

/-- One pass of edge relaxation: for each edge `(f, t)`, if `f` is
    discharged and `t` isn't yet, add `t`. Returns `(updatedDischarged, changed)`. -/
def dischargeOnePass :
    List (Int × Int) → List Int → Bool → List Int × Bool
  | [],            d, c => (d, c)
  | (f, t) :: es,  d, c =>
      if memInt f d && ¬ memInt t d
      then dischargeOnePass es (t :: d) true
      else dischargeOnePass es d c

/-- Fueled fixpoint of `dischargeOnePass`. Each productive pass strictly
    adds at least one id to the discharged set; non-productive pass means
    we've reached fixpoint. Fuel = #residues + 1 is enough since the set
    is bounded by the id count. -/
def dischargeFix :
    Nat → List (Int × Int) → List Int → List Int
  | 0,      _,     d => d
  | f + 1,  edges, d =>
      let (d', changed) := dischargeOnePass edges d false
      if changed then dischargeFix f edges d' else d'

/-- Split residue ids into `(discharged_in_seq_order, present_in_seq_order)`
    given a fully-computed `dischargedSet`. Preserves the input sequence
    order (matches host's iteration over rs). -/
def partitionByDischarged :
    List (Int × Bool) → List Int → List Int × List Int
  | [],            _     => ([], [])
  | (i, _) :: rest, dset =>
      let (dRest, pRest) := partitionByDischarged rest dset
      if memInt i dset
      then (i :: dRest, pRest)
      else (dRest, i :: pRest)

/-- The deterministic post-parse step: validate, fixpoint, partition,
    return partition or named residue. Pinned shape. -/
def evalDischargeAfterParse (prs : List (Int × Bool))
    (pedges : List (Int × Int)) : Option Val :=
  if validateEdges (prs.map Prod.fst) pedges then
    match partitionByDischarged prs
        (dischargeFix ((prs.map Prod.fst).length + 1) pedges
          ((prs.filter Prod.snd).map Prod.fst)) with
    | (dlist, []) => some (.record [("discharged", .list (dlist.map Val.int)),
                                     ("present", .list [])])
    | (_,     x :: xs) => some (.residue (.record
                            [("present", .list ((x :: xs).map Val.int))]))
  else none

/-- Top-level entry: parse, then delegate to `evalDischargeAfterParse`. -/
def evalDischargeOuter (rs es : List Val) : Option Val :=
  match parseAllResidues rs [] with
  | none      => none
  | some prs  =>
      match parseAllEdges es with
      | none        => none
      | some pedges => evalDischargeAfterParse prs pedges

-- §3a-ii — E1.18 (#1065) helpers for useCountCheck.
-- The tally is a 2-stage walk: extract all int ids (bail on non-int) into
-- a count assoc-list keyed by id, preserving first-seen order; then
-- partition into linear / overused by the count comparison.

/-- Increment the count for `i` in the insertion-ordered assoc list. -/
def tallyBump : List (Int × Nat) → Int → List (Int × Nat)
  | [],            i => [(i, 1)]
  | (j, n) :: rest, i =>
      if i = j then (j, n + 1) :: rest
      else (j, n) :: tallyBump rest i

/-- Tally a usage trace into an insertion-ordered `(id, count)` list.
    Bails on any non-int element. -/
def tallyUsages : List Val → List (Int × Nat) → Option (List (Int × Nat))
  | [],            acc => some acc
  | .int i :: rest, acc => tallyUsages rest (tallyBump acc i)
  | _ :: _,         _   => none

/-- Split the tally into `(linear, overused)` preserving insertion order.
    Linear = count ≤ 1; overused = count > 1. -/
def partitionUsage : List (Int × Nat) → List Int × List (Int × Nat)
  | []            => ([], [])
  | (i, n) :: rest =>
      let (lRest, oRest) := partitionUsage rest
      if n ≤ 1 then (i :: lRest, oRest)
      else (lRest, (i, n) :: oRest)

/-- Top-level entry: tally + partition + emit. Pinned shape host+evalLF. -/
def evalUseCountOuter (us : List Val) : Option Val :=
  match tallyUsages us [] with
  | none => none
  | some tally =>
      match partitionUsage tally with
      | (linear, []) =>
          some (.record [("linear", .list (linear.map Val.int)),
                          ("overused", .list [])])
      | (_, x :: xs) =>
          some (.residue (.record
            [("overused", .list ((x :: xs).map (fun (i, n) =>
              .record [("resource", .int i), ("count", .int (Int.ofNat n))])))]))

/-- E1.9 (#1045): evalArgs — structural-on-list helper for Call's arg
    evaluation. Each arg evaluated in CALLER's env (matches host
    `ev(a)`). Per-arg residue aborts with `none`. -/
def evalArgs : List Expr → Env → Programs → Nat → Option (List Val)
  | [],          _,   _, _ => some []
  | e :: rest,   env, p, f =>
      match evalLF e env p f with
      | none   => none
      | some v =>
          match evalArgs rest env p f with
          | none    => none
          | some vs => some (v :: vs)
termination_by args _ _ f => (f, sizeOf args, 0)

/-- The inner record-fields helper for `MakeRecord`. Walks the field list
    left-to-right; per-step residue from `evalL` aborts with `none`. Uses
    `insertField` so duplicate keys overwrite (host last-write-wins). -/
def evalFields : List (String × Expr) → Env → List (String × Val) → Programs → Nat → Option Val
  | [],              _,   acc, _, _ => some (.record acc)
  | (k, e) :: rest,  env, acc, p, f =>
      match evalLF e env p f with
      | some v => evalFields rest env (insertField k v acc) p f
      | none   => none
termination_by fields _ _ _ f => (f, sizeOf fields, 0)

/-- E1.8 (#1042): FindFirst inner fold. Walks the list with index `i`,
    binding `itemVar` to a `.record [("slot_idx", .int i), ("slot_item", x)]`
    per iteration (matching host's `slot_indexed` shape). On first
    `pred → .bool true`, eval `mapE` and return `.opt (some mapV)`; on
    fall-through, `.opt none`. Non-bool pred OR per-step residue → typed
    residue `none`. NOTE: `idxVar` is in the AST for fidelity but unbound
    in env — mirrors host (host only binds `item_var`). -/
def evalFindFirst (idxVar itemVar : String) (pred mapE : Expr) (env : Env)
    (programs : Programs) (fuel : Nat) :
    Nat → List Val → Option Val
  | _, []        => some (.opt none)
  | i, x :: rest =>
      let env' := (itemVar,
                   .record [("slot_idx", .int (Int.ofNat i)), ("slot_item", x)])
                  :: env
      match evalLF pred env' programs fuel with
      | some (.bool true)  =>
          match evalLF mapE env' programs fuel with
          | some v => some (.opt (some v))
          | none   => none
      | some (.bool false) =>
          evalFindFirst idxVar itemVar pred mapE env programs fuel (i + 1) rest
      | _ => none
termination_by _ xs => (fuel, sizeOf pred + sizeOf mapE + 1, xs.length + 1)
decreasing_by all_goals decreasing_tactic

/-- E1.8 (#1042): AlwaysUntil inner fold. Bool result: scan items with `t >
    fromT`; if `stop` fires, return true (pred-held-up-to-here); if `pred`
    fails on a gated item, return false; fall-through true. Per-step
    residue → typed `none`. -/
def evalAlwaysUntil (itemVar : String) (pred stopE : Expr) (env : Env) (fromT : Int)
    (programs : Programs) (fuel : Nat) :
    List Val → Option Val
  | []         => some (.bool true)
  | x :: rest  =>
      if itemT x ≤ fromT then
        evalAlwaysUntil itemVar pred stopE env fromT programs fuel rest
      else
        let env' := (itemVar, x) :: env
        match evalLF stopE env' programs fuel with
        | some (.bool true)  => some (.bool true)
        | some (.bool false) =>
            match evalLF pred env' programs fuel with
            | some (.bool true)  =>
                evalAlwaysUntil itemVar pred stopE env fromT programs fuel rest
            | some (.bool false) => some (.bool false)
            | _                  => none
        | _ => none
termination_by xs => (fuel, sizeOf pred + sizeOf stopE + 1, xs.length + 1)

/-- E1.8 (#1042): EventuallyAfter inner fold. Bool result: scan items with
    `t > fromT`; first `pred → true` returns true; fall-through false.
    Per-step residue → typed `none`. -/
def evalEventuallyAfter (itemVar : String) (pred : Expr) (env : Env) (fromT : Int)
    (programs : Programs) (fuel : Nat) :
    List Val → Option Val
  | []         => some (.bool false)
  | x :: rest  =>
      if itemT x ≤ fromT then
        evalEventuallyAfter itemVar pred env fromT programs fuel rest
      else
        let env' := (itemVar, x) :: env
        match evalLF pred env' programs fuel with
        | some (.bool true)  => some (.bool true)
        | some (.bool false) =>
            evalEventuallyAfter itemVar pred env fromT programs fuel rest
        | _                  => none
termination_by xs => (fuel, sizeOf pred, xs.length + 1)

/-- E1.10 (#1047): BoundedFix inner loop. Iterates the state via `stepBody`
    while `stopPred` returns false, up to `fuel` times. Returns a record
    `{converged, state, steps}` (named return shape so fuel exhaustion is a
    surfaced typed residue). Non-bool stopPred OR per-step residue → `none`
    (typed residue propagation). Pure-Nat fuel decreasing ⇒ totality. -/
def evalFix (stepVar : String) (stepBody stopPred : Expr) (env : Env)
    (state : Val) (stepsSoFar : Nat) (programs : Programs) (fuel : Nat) :
    Nat → Option Val
  | 0 =>
      let env' := (stepVar, state) :: env
      match evalLF stopPred env' programs fuel with
      | some (.bool b) =>
          some (.record [("converged", .bool b),
                         ("state",     state),
                         ("steps",     .int (Int.ofNat stepsSoFar))])
      | _ => none
  | n + 1 =>
      let env' := (stepVar, state) :: env
      match evalLF stopPred env' programs fuel with
      | some (.bool true) =>
          some (.record [("converged", .bool true),
                         ("state",     state),
                         ("steps",     .int (Int.ofNat stepsSoFar))])
      | some (.bool false) =>
          match evalLF stepBody env' programs fuel with
          | some state' =>
              evalFix stepVar stepBody stopPred env state' (stepsSoFar + 1) programs fuel n
          | none => none
      | _ => none
termination_by bfFuel => (fuel, sizeOf stepBody + sizeOf stopPred + 1, bfFuel + 1)

end

/-! ## §3b — E1.16 glue seal lemma (residue exhaustion).

`evalGlue_residue_exhaustive` says: for any inputs, the result is in
exactly one of three named shapes — `none` (non-record section), a record
(consistent merge), or a named residue carrying the first conflict witness.
This is the residue-exhaustion side of `[spatial_axis_OPEN]`. -/

theorem evalGlue_nil (acc : List (String × Val)) :
    evalGlue [] acc = some (.record acc) := by
  unfold evalGlue; rfl

theorem evalGlue_residue_exhaustive : ∀ (secs : List Val) (acc : List (String × Val)),
      evalGlue secs acc = none
    ∨ (∃ acc', evalGlue secs acc = some (.record acc'))
    ∨ (∃ k va vb, evalGlue secs acc
            = some (.residue (.record [(k, .record [("a", va), ("b", vb)])])))
  | [], acc => Or.inr (Or.inl ⟨acc, evalGlue_nil acc⟩)
  | .record kvs :: rest, acc => by
      match hm : mergeSectionInto kvs acc with
      | .ok acc' =>
          have hstep : evalGlue (.record kvs :: rest) acc = evalGlue rest acc' := by
            simp [evalGlue, hm]
          rw [hstep]
          exact evalGlue_residue_exhaustive rest acc'
      | .conflict k va vb =>
          have hstep : evalGlue (.record kvs :: rest) acc
                         = some (.residue (.record
                              [(k, .record [("a", va), ("b", vb)])])) := by
            simp [evalGlue, hm]
          exact Or.inr (Or.inr ⟨k, va, vb, hstep⟩)
  | .int _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .bool _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .list _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .opt _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .ok _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .err _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .residue _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  | .str _ :: _, _ => by unfold evalGlue; exact Or.inl rfl
  termination_by secs _ => secs.length

/-! ## §3c — E1.17 dischargeProp seal (residue exhaustion + named witness).

`evalDischargeOuter_residue_exhaustive` says: for any inputs, the result
is in exactly one of three named shapes — `none` (type residue / dangling
id), `.record partition` (consistent fixpoint, present is empty), or
`.residue (.record [("present", non-empty)])` (the named-residue case,
runtime instance of `[rdc_irreducible_residue]`). -/

/-- Inner residue exhaustion (after parsing succeeded). Pure structural
    case-analysis on the partition. -/
theorem evalDischargeAfterParse_residue_exhaustive
    (prs : List (Int × Bool)) (pedges : List (Int × Int)) :
      evalDischargeAfterParse prs pedges = none
    ∨ (∃ dlist, evalDischargeAfterParse prs pedges
          = some (.record [("discharged", .list dlist), ("present", .list [])]))
    ∨ (∃ plist, evalDischargeAfterParse prs pedges
          = some (.residue (.record [("present", .list plist)]))) := by
  unfold evalDischargeAfterParse
  split
  · split
    · rename_i dlist _
      exact Or.inr (Or.inl ⟨dlist.map Val.int, rfl⟩)
    · rename_i _ x xs _
      exact Or.inr (Or.inr ⟨(x :: xs).map Val.int, rfl⟩)
  · exact Or.inl rfl

theorem evalDischargeOuter_residue_exhaustive (rs es : List Val) :
      evalDischargeOuter rs es = none
    ∨ (∃ dlist, evalDischargeOuter rs es
          = some (.record [("discharged", .list dlist), ("present", .list [])]))
    ∨ (∃ plist, evalDischargeOuter rs es
          = some (.residue (.record [("present", .list plist)]))) := by
  unfold evalDischargeOuter
  cases hpr : parseAllResidues rs [] with
  | none => exact Or.inl rfl
  | some prs =>
      cases hpe : parseAllEdges es with
      | none => exact Or.inl rfl
      | some pedges =>
          exact evalDischargeAfterParse_residue_exhaustive prs pedges

/-! ## §3d — E1.18 useCountCheck seal (residue exhaustion + named overuse).

`evalUseCountOuter_residue_exhaustive` says: for any input usage trace,
the result is in exactly one of three named shapes — `none` (non-int
element), `.record [("linear", _), ("overused", .list [])]` (all linear),
or `.residue (.record [("overused", non-empty witness list)])` (the named
`[substructural_overuse]` case). -/

/-- Inner residue exhaustion after the tally succeeded — pure partition split. -/
theorem evalUseCountAfterTally_residue_exhaustive (tally : List (Int × Nat)) :
      (match partitionUsage tally with
        | (linear, []) =>
            some (Val.record [("linear", .list (linear.map Val.int)),
                              ("overused", .list [])])
        | (_, x :: xs) =>
            some (.residue (Val.record
              [("overused", .list ((x :: xs).map (fun (i, n) =>
                Val.record [("resource", .int i),
                            ("count", .int (Int.ofNat n))])))])))
        = none
    ∨ (∃ linear, (match partitionUsage tally with
        | (linear, []) =>
            some (Val.record [("linear", .list (linear.map Val.int)),
                              ("overused", .list [])])
        | (_, x :: xs) =>
            some (.residue (Val.record
              [("overused", .list ((x :: xs).map (fun (i, n) =>
                Val.record [("resource", .int i),
                            ("count", .int (Int.ofNat n))])))])))
          = some (.record [("linear", .list linear), ("overused", .list [])]))
    ∨ (∃ witnesses, (match partitionUsage tally with
        | (linear, []) =>
            some (Val.record [("linear", .list (linear.map Val.int)),
                              ("overused", .list [])])
        | (_, x :: xs) =>
            some (.residue (Val.record
              [("overused", .list ((x :: xs).map (fun (i, n) =>
                Val.record [("resource", .int i),
                            ("count", .int (Int.ofNat n))])))])))
          = some (.residue (.record [("overused", .list witnesses)]))) := by
  split
  · rename_i linear _
    exact Or.inr (Or.inl ⟨linear.map Val.int, rfl⟩)
  · rename_i _ x xs _
    refine Or.inr (Or.inr
      ⟨(x :: xs).map (fun (i, n) =>
          Val.record [("resource", .int i),
                      ("count", .int (Int.ofNat n))]), ?_⟩)
    rfl

theorem evalUseCountOuter_residue_exhaustive (us : List Val) :
      evalUseCountOuter us = none
    ∨ (∃ linear, evalUseCountOuter us
          = some (.record [("linear", .list linear), ("overused", .list [])]))
    ∨ (∃ witnesses, evalUseCountOuter us
          = some (.residue (.record [("overused", .list witnesses)]))) := by
  unfold evalUseCountOuter
  cases htally : tallyUsages us [] with
  | none => exact Or.inl rfl
  | some tally => exact evalUseCountAfterTally_residue_exhaustive tally

/-! ## §3e — E1.19 matchTag seal (residue exhaustion + chosen-or-default).

`evalMatchTag_residue_exhaustive` says: for any inputs, the result is in
exactly one of three named shapes — `none` (non-int / residue scrutinee),
the chosen arm body's `evalLF` (some `(code, body)` arm matched), or
the `default`'s `evalLF` (no arm matched, falls through). The dispatch's
pinned semantics: `universe` is NOT consulted at runtime — runtime
dispatch is pure first-match + default. -/

/-- E1.19 (#1070): the arm-key list (mirrors host's `tag_branch_keys`). -/
def tagBranchKeys : List (Int × Expr) → List Int
  | []                => []
  | (code, _) :: rest => code :: tagBranchKeys rest

/-- E1.19 (#1070): the decidable admission predicate — `univ ⊆ branchKeys`.
    The strict-form disjunction (accept a `ResidueE` default in lieu of a
    full cover) lives in the host emitter; modelled by the boolean OR
    `predicate ∨ default_is_residue` at admission-time, NOT inside this
    Lean-side decidable core. Keeps the runtime seal minimal. -/
def matchExhaustive (univ : List Int) (arms : List (Int × Expr)) : Bool :=
  univ.all (fun u => (tagBranchKeys arms).contains u)

/-- E1.19 (#1070): `matchArms`'s structural reach-result: either the
    `default`'s eval (no arm matched) or some chosen arm's body eval. -/
theorem matchArms_reaches_body_or_default
    (default : Expr) (env : Env) (programs : Programs) (fuel : Nat) (tag : Int) :
    ∀ (arms : List (Int × Expr)),
      matchArms default env programs fuel tag arms = evalLF default env programs fuel
      ∨ (∃ code body, (code, body) ∈ arms
                      ∧ matchArms default env programs fuel tag arms
                        = evalLF body env programs fuel)
  | []                  => Or.inl (by simp [matchArms])
  | (code, body) :: rest => by
      by_cases hc : tag = code
      · refine Or.inr ⟨code, body, List.mem_cons_self _ _, ?_⟩
        simp [matchArms, hc]
      · have hstep : matchArms default env programs fuel tag ((code, body) :: rest)
                   = matchArms default env programs fuel tag rest := by
          simp [matchArms, hc]
        rw [hstep]
        rcases matchArms_reaches_body_or_default default env programs fuel tag rest with
          h | ⟨c, b, hmem, heq⟩
        · exact Or.inl h
        · exact Or.inr ⟨c, b, List.mem_cons_of_mem _ hmem, heq⟩

/- E1.19 (#1070) note: the dispatch-level trichotomy seal for matchTag is
   split:
     * matchArms_reaches_body_or_default (above) — the chosen-arm-body OR
       default half (the dispatch content for arms).
     * The "none on non-int scrut" half is by definition of evalLF's
       matchTag arm. Lean-4-core CAVEAT: evalLF is mutual + well-founded,
       and Lean does NOT auto-generate a usable equational lemma for a
       single arm of a mutual WF def. So an outer theorem mentioning
       evalLF (.matchTag …) directly is parked as [matchTag_outer_seal_OPEN]
       until a Lean-4-core route lands.
     * The existing seals on evalGlue/evalDischargeOuter/evalUseCountOuter
       avoid this by operating on inner non-mutual helpers; the matchTag
       runtime arm has no inner non-mutual analogue because matchArms is
       mutual with evalLF for body-eval calls.
   The runtime "never-silent" content IS captured by
   matchArms_reaches_body_or_default (every reachable result is either a
   chosen-arm-body's eval or the default's eval — never a silent value).
-/

/-- Default fuel for the 2-arg `evalL` wrapper. Generous bound so non-Call
    programs never hit it; Call-bearing programs needing more fuel must use
    `evalLF` directly with an explicit fuel. -/
def defaultEvalFuel : Nat := 1000000

/-- E1.9 (#1045): the 2-arg entry wrapper around `evalLF`. Preserves the
    public surface area used by 60+ existing inline `native_decide`
    examples + the conformance gate's `evalL` references. Defaults
    `programs := []` (no Call resolution available — Call evaluates to
    typed residue) and `fuel := defaultEvalFuel`. Existing non-Call tests
    produce identical results (Call never fires; fuel never inspected). -/
def evalL (e : Expr) (env : Env) : Option Val := evalLF e env [] defaultEvalFuel

/-! ## §4 — Fixture harness for cross-side conformance

A `GenFixture` carries a (name, Expr, Env, pythonVal) tuple — the Python
emitter writes these against the REAL `interp.eval_` verdict, mapping float
`n.is_integer()` to `Int n` (integer-valued only; see [E1_float_OPEN]).
A typed-residue fixture has `pythonVal := none` (the Python side raised /
sentinel'd; `evalL` agrees by returning `none`). -/

structure GenFixture where
  name      : String
  expr      : Expr
  pythonVal : Option Val
  deriving Repr

/-- Bool equality on `Option Val`. We define this explicitly rather than rely
    on a derived `DecidableEq Val` because the recursive `List Val`
    constructor in `Val` blocks the default `deriving DecidableEq` in current
    Lean 4. Composes the mutually-defined `beqVal`. -/
def beqOptVal : Option Val → Option Val → Bool
  | none,   none   => true
  | some x, some y => beqVal x y
  | _, _ => false

/-- Per-fixture cross-check: Lean `evalL` verdict equals the Python verdict
    EXACTLY (`Option Val` equality — `none` = typed residue on both sides).
    Fixtures evaluate in the empty environment; any variable bindings the
    fixture exercises must come via `letE` inside the expression itself
    (closed-form fixtures match the architect's `--lean` emitter shape). -/
def checkFixture (f : GenFixture) : Bool :=
  beqOptVal (evalL f.expr []) f.pythonVal

/-- Aggregate over the fixture list. -/
def allFixturesEval (fs : List GenFixture) : Bool :=
  fs.all checkFixture

/-! ## §5 — Inline `native_decide` sanity (regression catch before gen file lands)

Pin the intended verdicts on a few canonical expressions even before the
emitter's gen file is present. Catches a regression in `evalL` itself
(separate from the cross-side conformance).

We use `beqVal`-via-`Option.beq` for these checks because `Val` does not
derive `DecidableEq` (the recursive `List Val` constructor blocks the
default derive in current Lean 4). The `(_ == _) = true` form makes
`native_decide` work on a Bool comparison rather than a Prop equality. -/

example : beqOptVal (evalL (.add (.num 2) (.num 3)) []) (some (.int 5)) = true := by native_decide
example : beqOptVal (evalL (.mul (.num 4) (.num 5)) []) (some (.int 20)) = true := by native_decide
example : beqOptVal (evalL (.lt (.num 2) (.num 3)) []) (some (.bool true)) = true := by native_decide
example : beqOptVal (evalL (.andE (.boollit true) (.boollit false)) []) (some (.bool false)) = true := by native_decide
-- A nested let + ifE: `if (2<3) then let x = 4 in x*x else 0` = 16
example :
    beqOptVal
      (evalL (.ifE (.lt (.num 2) (.num 3))
                   (.letE "x" (.num 4) (.mul (.var "x") (.var "x")))
                   (.num 0))
             [])
      (some (.int 16)) = true := by native_decide
-- Typed residue: unbound var returns none.
example : beqOptVal (evalL (.var "missing") []) none = true := by native_decide
-- Typed residue: type mismatch (adding a bool) returns none.
example : beqOptVal (evalL (.add (.num 1) (.boollit true)) []) none = true := by native_decide

-- E1.11 (#1053, revised) — floor Mod only (matches Python `%` on negative operands).
-- Div NOT added to evalLF: existing host `Div` is float `/`; evalLF has no Float
-- so Div is outside the conformance domain (Klaus's revision).
example : beqOptVal (evalL (.mod (.num 10) (.num 3)) []) (some (.int 1)) = true := by native_decide
example : beqOptVal (evalL (.mod (.num (-7)) (.num 2)) []) (some (.int 1)) = true := by native_decide
example : beqOptVal (evalL (.mod (.num 7) (.num (-2))) []) (some (.int (-1))) = true := by native_decide
example : beqOptVal (evalL (.mod (.num (-7)) (.num (-2))) []) (some (.int (-1))) = true := by native_decide
-- Mod by zero ⇒ typed residue (none, mirrors host SlotError `[E1.11_mod_by_zero]`).
example : beqOptVal (evalL (.mod (.num 5) (.num 0)) []) none = true := by native_decide
-- Type mismatch ⇒ none.
example : beqOptVal (evalL (.mod (.num 5) (.boollit true)) []) none = true := by native_decide

-- E1.12 (#1054) — GroupBy: the quotient q as a first-class node.
-- Group by parity: [1,2,3] → [{key:1, items:[1,3]}, {key:0, items:[2]}] in first-seen order.
example :
    beqOptVal
      (evalL
        (.groupBy
          (.listAppend (.listAppend (.listSingleton (.num 1)) (.listSingleton (.num 2)))
                       (.listSingleton (.num 3)))
          "x" (.mod (.var "x") (.num 2)))
        [])
      (some (.list [
        .record [("key", .int 1), ("items", .list [.int 1, .int 3])],
        .record [("key", .int 0), ("items", .list [.int 2])]
      ])) = true := by native_decide
-- Empty list ⇒ empty groups.
example :
    beqOptVal
      (evalL (.groupBy .emptyList "x" (.var "x")) [])
      (some (.list [])) = true := by native_decide
-- Non-list input ⇒ none.
example :
    beqOptVal
      (evalL (.groupBy (.num 5) "x" (.var "x")) [])
      none = true := by native_decide
-- Key residue (unbound var in keyBody) ⇒ none.
example :
    beqOptVal
      (evalL (.groupBy (.listSingleton (.num 1)) "x" (.var "missing")) [])
      none = true := by native_decide
-- Bool keys: group [true,false,true,true] → [{key:T,items:[T,T,T]},{key:F,items:[F]}]
example :
    beqOptVal
      (evalL
        (.groupBy
          (.listAppend (.listAppend (.listAppend
            (.listSingleton (.boollit true))
            (.listSingleton (.boollit false)))
            (.listSingleton (.boollit true)))
            (.listSingleton (.boollit true)))
          "b" (.var "b"))
        [])
      (some (.list [
        .record [("key", .bool true), ("items", .list [.bool true, .bool true, .bool true])],
        .record [("key", .bool false), ("items", .list [.bool false])]
      ])) = true := by native_decide

-- E1.13 (#1055) — OrderBy total stable sort by int key.
-- Sort [3,1,2] asc by identity → [1,2,3].
example :
    beqOptVal
      (evalL
        (.orderBy
          (.listAppend (.listAppend (.listSingleton (.num 3)) (.listSingleton (.num 1)))
                       (.listSingleton (.num 2)))
          "x" (.var "x") false)
        [])
      (some (.list [.int 1, .int 2, .int 3])) = true := by native_decide
-- Sort [3,1,2] desc → [3,2,1].
example :
    beqOptVal
      (evalL
        (.orderBy
          (.listAppend (.listAppend (.listSingleton (.num 3)) (.listSingleton (.num 1)))
                       (.listSingleton (.num 2)))
          "x" (.var "x") true)
        [])
      (some (.list [.int 3, .int 2, .int 1])) = true := by native_decide
-- Stable on ties: all keys = 0 → input order preserved (both asc and desc).
example :
    beqOptVal
      (evalL
        (.orderBy
          (.listAppend (.listAppend (.listSingleton (.num 10)) (.listSingleton (.num 20)))
                       (.listSingleton (.num 30)))
          "x" (.num 0) false)
        [])
      (some (.list [.int 10, .int 20, .int 30])) = true := by native_decide
example :
    beqOptVal
      (evalL
        (.orderBy
          (.listAppend (.listAppend (.listSingleton (.num 10)) (.listSingleton (.num 20)))
                       (.listSingleton (.num 30)))
          "x" (.num 0) true)
        [])
      (some (.list [.int 10, .int 20, .int 30])) = true := by native_decide
-- Empty list → empty.
example :
    beqOptVal
      (evalL (.orderBy .emptyList "x" (.var "x") false) [])
      (some (.list [])) = true := by native_decide
-- Non-int key (bool) → residue.
example :
    beqOptVal
      (evalL (.orderBy (.listSingleton (.num 1)) "x" (.boollit true) false) [])
      none = true := by native_decide
-- Non-list input → residue.
example :
    beqOptVal
      (evalL (.orderBy (.num 5) "x" (.var "x") false) [])
      none = true := by native_decide

-- E1.14 (#1056) — ListTake prefix slice with Int.toNat clamping.
-- take 2 of [1,2,3,4] = [1,2].
example :
    beqOptVal
      (evalL
        (.listTake
          (.listAppend (.listAppend (.listAppend
            (.listSingleton (.num 1)) (.listSingleton (.num 2)))
            (.listSingleton (.num 3))) (.listSingleton (.num 4)))
          (.num 2))
        [])
      (some (.list [.int 1, .int 2])) = true := by native_decide
-- take 0 = [].
example :
    beqOptVal
      (evalL (.listTake (.listAppend (.listSingleton (.num 1)) (.listSingleton (.num 2))) (.num 0)) [])
      (some (.list [])) = true := by native_decide
-- take ≥ len = whole list.
example :
    beqOptVal
      (evalL (.listTake (.listAppend (.listSingleton (.num 1)) (.listSingleton (.num 2))) (.num 10)) [])
      (some (.list [.int 1, .int 2])) = true := by native_decide
-- take negative → Int.toNat clamps to 0 → [].
example :
    beqOptVal
      (evalL (.listTake (.listAppend (.listSingleton (.num 1)) (.listSingleton (.num 2))) (.neg (.num 1))) [])
      (some (.list [])) = true := by native_decide
-- take of empty = [].
example :
    beqOptVal
      (evalL (.listTake .emptyList (.num 5)) [])
      (some (.list [])) = true := by native_decide
-- take of non-list = residue.
example :
    beqOptVal
      (evalL (.listTake (.num 5) (.num 1)) [])
      none = true := by native_decide

-- E1.15 (#1057) — first-class Residue ρ as a DSL primitive.
-- Construct .residue (.int 42).
example :
    beqOptVal
      (evalL (.residueE (.num 42)) [])
      (some (.residue (.int 42))) = true := by native_decide
-- isResidueE on a residue → true.
example :
    beqOptVal
      (evalL (.isResidueE (.residueE (.num 1))) [])
      (some (.bool true)) = true := by native_decide
-- isResidueE on a non-residue (Ok) → false.
example :
    beqOptVal
      (evalL (.isResidueE (.okE (.num 1))) [])
      (some (.bool false)) = true := by native_decide
-- isResidueE on a primitive (int) → false.
example :
    beqOptVal
      (evalL (.isResidueE (.num 5)) [])
      (some (.bool false)) = true := by native_decide
-- getResidue on a residue → payload.
example :
    beqOptVal
      (evalL (.getResidue (.residueE (.num 7))) [])
      (some (.int 7)) = true := by native_decide
-- getResidue on a non-residue → typed residue (none).
example :
    beqOptVal
      (evalL (.getResidue (.num 5)) [])
      none = true := by native_decide
-- getResidue on Ok → typed residue.
example :
    beqOptVal
      (evalL (.getResidue (.okE (.num 5))) [])
      none = true := by native_decide
-- beqVal: residue x = residue y when x = y.
example :
    beqOptVal
      (evalL (.eqE (.residueE (.num 1)) (.residueE (.num 1))) [])
      (some (.bool true)) = true := by native_decide
-- beqVal: residue ≠ ok (different ctors).
example :
    beqOptVal
      (evalL (.eqE (.residueE (.num 1)) (.okE (.num 1))) [])
      (some (.bool false)) = true := by native_decide

-- E1.11b (#1059) — Div (exact-int) + AbsE + MinE + MaxE.
-- Div 6/2 = 3 (exact).
example :
    beqOptVal (evalL (.div (.num 6) (.num 2)) []) (some (.int 3)) = true := by native_decide
-- Div 7/2 = none (non-exact).
example :
    beqOptVal (evalL (.div (.num 7) (.num 2)) []) none = true := by native_decide
-- Div 5/0 = none.
example :
    beqOptVal (evalL (.div (.num 5) (.num 0)) []) none = true := by native_decide
-- Div -6/3 = -2.
example :
    beqOptVal (evalL (.div (.num (-6)) (.num 3)) []) (some (.int (-2))) = true := by native_decide
-- AbsE -7 = 7.
example :
    beqOptVal (evalL (.absE (.num (-7))) []) (some (.int 7)) = true := by native_decide
-- AbsE 7 = 7.
example :
    beqOptVal (evalL (.absE (.num 7)) []) (some (.int 7)) = true := by native_decide
-- AbsE 0 = 0.
example :
    beqOptVal (evalL (.absE (.num 0)) []) (some (.int 0)) = true := by native_decide
-- MinE 3 7 = 3, MaxE 3 7 = 7.
example :
    beqOptVal (evalL (.minE (.num 3) (.num 7)) []) (some (.int 3)) = true := by native_decide
example :
    beqOptVal (evalL (.maxE (.num 3) (.num 7)) []) (some (.int 7)) = true := by native_decide
-- MinE -5 -2 = -5, MaxE -5 -2 = -2.
example :
    beqOptVal (evalL (.minE (.num (-5)) (.num (-2))) []) (some (.int (-5))) = true := by native_decide
example :
    beqOptVal (evalL (.maxE (.num (-5)) (.num (-2))) []) (some (.int (-2))) = true := by native_decide
-- Type mismatch ⇒ none.
example :
    beqOptVal (evalL (.absE (.boollit true)) []) none = true := by native_decide
example :
    beqOptVal (evalL (.minE (.num 1) (.boollit true)) []) none = true := by native_decide

-- E1.2 (#1030) inline `native_decide` sanity for the list fragment.

example : beqOptVal (evalL .emptyList []) (some (.list [])) = true := by native_decide
example : beqOptVal (evalL (.listSingleton (.num 42)) []) (some (.list [.int 42])) = true := by native_decide
example :
    beqOptVal
      (evalL (.listAppend
              (.listSingleton (.num 1))
              (.listAppend (.listSingleton (.num 2)) (.listSingleton (.num 3))))
             [])
      (some (.list [.int 1, .int 2, .int 3])) = true := by native_decide
example :
    beqOptVal
      (evalL (.listLen
              (.listAppend (.listSingleton (.num 1))
                           (.listAppend (.listSingleton (.num 2)) (.listSingleton (.num 3)))))
             [])
      (some (.int 3)) = true := by native_decide
-- ListFirst [] mirrors host residue: opt none (NOT a typed-residue / none).
example : beqOptVal (evalL (.listFirst .emptyList) []) (some (.opt none)) = true := by native_decide
-- ListLast on non-empty.
example : beqOptVal (evalL (.listLast (.listSingleton (.num 7))) []) (some (.opt (some (.int 7)))) = true := by native_decide
-- ListLen on a non-list returns the typed residue (none).
example : beqOptVal (evalL (.listLen (.num 5)) []) none = true := by native_decide

-- E1.3 (#1032) inline `native_decide` sanity for the Option fragment.

-- noneLit literal → opt none.
example : beqOptVal (evalL .noneLit []) (some (.opt none)) = true := by native_decide
-- someE: wrap a value.
example : beqOptVal (evalL (.someE (.num 5)) []) (some (.opt (some (.int 5)))) = true := by native_decide
-- isNoneE of a noneLit → bool true.
example : beqOptVal (evalL (.isNoneE .noneLit) []) (some (.bool true)) = true := by native_decide
-- isNoneE of a someE → bool false.
example : beqOptVal (evalL (.isNoneE (.someE (.num 1))) []) (some (.bool false)) = true := by native_decide
-- isSomeE of a someE → bool true.
example : beqOptVal (evalL (.isSomeE (.someE (.num 1))) []) (some (.bool true)) = true := by native_decide
-- isSomeE of a noneLit → bool false.
example : beqOptVal (evalL (.isSomeE .noneLit) []) (some (.bool false)) = true := by native_decide
-- unwrapSome of someE → underlying value.
example : beqOptVal (evalL (.unwrapSome (.someE (.num 7))) []) (some (.int 7)) = true := by native_decide
-- unwrapSome of noneLit → typed residue (host raises).
example : beqOptVal (evalL (.unwrapSome .noneLit) []) none = true := by native_decide
-- Type mismatch: isNoneE of a non-Option → typed residue.
example : beqOptVal (evalL (.isNoneE (.num 0)) []) none = true := by native_decide
-- Nested: someE inside a letE; unwrap and arith.
example :
    beqOptVal
      (evalL (.letE "o" (.someE (.num 10))
                 (.add (.unwrapSome (.var "o")) (.num 5)))
             [])
      (some (.int 15)) = true := by native_decide

-- E1.4 (#1034) inline `native_decide` sanity for BoundedFold.

-- sum [1,2,3] (acc + item from 0) = 6.
example :
    beqOptVal
      (evalL (.boundedFold
                (.listAppend (.listSingleton (.num 1))
                  (.listAppend (.listSingleton (.num 2)) (.listSingleton (.num 3))))
                (.num 0) "acc" "it"
                (.add (.var "acc") (.var "it")))
             [])
      (some (.int 6)) = true := by native_decide
-- product [2,3,4] (acc * item from 1) = 24.
example :
    beqOptVal
      (evalL (.boundedFold
                (.listAppend (.listSingleton (.num 2))
                  (.listAppend (.listSingleton (.num 3)) (.listSingleton (.num 4))))
                (.num 1) "acc" "it"
                (.mul (.var "acc") (.var "it")))
             [])
      (some (.int 24)) = true := by native_decide
-- count-via-fold (always +1) over [10,20,30] = 3 (init 0, body = acc + 1).
example :
    beqOptVal
      (evalL (.boundedFold
                (.listAppend (.listSingleton (.num 10))
                  (.listAppend (.listSingleton (.num 20)) (.listSingleton (.num 30))))
                (.num 0) "acc" "it"
                (.add (.var "acc") (.num 1)))
             [])
      (some (.int 3)) = true := by native_decide
-- Fold over empty list returns init unchanged.
example :
    beqOptVal
      (evalL (.boundedFold .emptyList (.num 42) "acc" "it" (.var "acc")) [])
      (some (.int 42)) = true := by native_decide
-- itemVar shadows accVar when names collide (Python `{...,acc:a,item:i}`
-- has `item` win on collision since written last; we mirror by prepending
-- itemVar binding in front of accVar in env).
example :
    beqOptVal
      (evalL (.boundedFold (.listSingleton (.num 99)) (.num 0)
                "x" "x" (.var "x"))
             [])
      (some (.int 99)) = true := by native_decide
-- Per-step residue propagation: body residues (unwrapSome noneLit) → fold none.
example :
    beqOptVal
      (evalL (.boundedFold (.listSingleton (.num 1)) (.num 0)
                "acc" "it" (.add (.var "acc") (.unwrapSome .noneLit)))
             [])
      none = true := by native_decide
-- Typed residue: non-list `lst` → none.
example :
    beqOptVal
      (evalL (.boundedFold (.num 5) (.num 0) "acc" "it" (.var "acc")) [])
      none = true := by native_decide

-- E1.5 (#1036) inline `native_decide` sanity for ListDrop / ListWindow.

-- listDrop [1,2,3,4] 2 = [3,4].
example :
    beqOptVal
      (evalL (.listDrop
                (.listAppend (.listSingleton (.num 1))
                  (.listAppend (.listSingleton (.num 2))
                    (.listAppend (.listSingleton (.num 3)) (.listSingleton (.num 4)))))
                (.num 2))
             [])
      (some (.list [.int 3, .int 4])) = true := by native_decide
-- listDrop [] 1 = [].
example :
    beqOptVal
      (evalL (.listDrop .emptyList (.num 1)) [])
      (some (.list [])) = true := by native_decide
-- listDrop xs 0 = xs (full list).
example :
    beqOptVal
      (evalL (.listDrop (.listSingleton (.num 9)) (.num 0)) [])
      (some (.list [.int 9])) = true := by native_decide
-- listDrop residue: lst is not a list → none.
example :
    beqOptVal
      (evalL (.listDrop (.num 5) (.num 1)) [])
      none = true := by native_decide
-- listWindow [1,2,3] 2 = [[1,2],[2,3]].
example :
    beqOptVal
      (evalL (.listWindow
                (.listAppend (.listSingleton (.num 1))
                  (.listAppend (.listSingleton (.num 2)) (.listSingleton (.num 3))))
                2)
             [])
      (some (.list [.list [.int 1, .int 2], .list [.int 2, .int 3]])) = true := by native_decide
-- listWindow [1] 3 = [] (k > len).
example :
    beqOptVal
      (evalL (.listWindow (.listSingleton (.num 1)) 3) [])
      (some (.list [])) = true := by native_decide
-- listWindow [1,2] 2 = [[1,2]] (k = len).
example :
    beqOptVal
      (evalL (.listWindow
                (.listAppend (.listSingleton (.num 1)) (.listSingleton (.num 2)))
                2)
             [])
      (some (.list [.list [.int 1, .int 2]])) = true := by native_decide
-- listWindow on non-list → none (typed residue).
example :
    beqOptVal
      (evalL (.listWindow (.num 7) 2) [])
      none = true := by native_decide

-- E1.6 (#1038) inline `native_decide` sanity for record fragment.

-- makeRecord {a:1, b:2} = .record [(a,1),(b,2)]
example :
    beqOptVal
      (evalL (.makeRecord [("a", .num 1), ("b", .num 2)]) [])
      (some (.record [("a", .int 1), ("b", .int 2)])) = true := by native_decide
-- empty record.
example :
    beqOptVal
      (evalL (.makeRecord []) [])
      (some (.record [])) = true := by native_decide
-- fieldAccess returns value.
example :
    beqOptVal
      (evalL (.fieldAccess (.makeRecord [("a", .num 1), ("b", .num 2)]) "a") [])
      (some (.int 1)) = true := by native_decide
-- fieldAccess on second field.
example :
    beqOptVal
      (evalL (.fieldAccess (.makeRecord [("a", .num 1), ("b", .num 2)]) "b") [])
      (some (.int 2)) = true := by native_decide
-- Missing key → typed residue.
example :
    beqOptVal
      (evalL (.fieldAccess (.makeRecord [("a", .num 1)]) "z") [])
      none = true := by native_decide
-- Non-record → typed residue.
example :
    beqOptVal
      (evalL (.fieldAccess (.num 5) "a") [])
      none = true := by native_decide
-- Per-field residue propagation: field with unwrapSome noneLit → none.
example :
    beqOptVal
      (evalL (.makeRecord [("a", .unwrapSome .noneLit)]) [])
      none = true := by native_decide
-- Duplicate keys: last write wins (host dict semantics).
example :
    beqOptVal
      (evalL (.fieldAccess (.makeRecord [("a", .num 1), ("a", .num 3)]) "a") [])
      (some (.int 3)) = true := by native_decide
-- Duplicate key preserves first-insertion position.
example :
    beqOptVal
      (evalL (.makeRecord [("a", .num 1), ("b", .num 2), ("a", .num 3)]) [])
      (some (.record [("a", .int 3), ("b", .int 2)])) = true := by native_decide
-- Nested: record of records.
example :
    beqOptVal
      (evalL (.fieldAccess
                (.fieldAccess
                  (.makeRecord [("outer", .makeRecord [("inner", .num 42)])])
                  "outer")
                "inner")
             [])
      (some (.int 42)) = true := by native_decide

-- E1.7a (#1040) inline `native_decide` sanity for ListIndexed.

-- listIndexed [10,20] = [{slot_idx:0, slot_item:10}, {slot_idx:1, slot_item:20}].
example :
    beqOptVal
      (evalL (.listIndexed
                (.listAppend (.listSingleton (.num 10)) (.listSingleton (.num 20))))
             [])
      (some (.list
        [ .record [("slot_idx", .int 0), ("slot_item", .int 10)]
        , .record [("slot_idx", .int 1), ("slot_item", .int 20)]
        ])) = true := by native_decide
-- listIndexed empty = empty.
example :
    beqOptVal
      (evalL (.listIndexed .emptyList) [])
      (some (.list [])) = true := by native_decide
-- listIndexed on non-list → typed residue.
example :
    beqOptVal
      (evalL (.listIndexed (.num 5)) [])
      none = true := by native_decide

-- E1.7b (#1040) inline `native_decide` sanity for Result fragment.

-- okE 5 = .ok 5.
example :
    beqOptVal
      (evalL (.okE (.num 5)) [])
      (some (.ok (.int 5))) = true := by native_decide
-- errE 7 = .err 7.
example :
    beqOptVal
      (evalL (.errE (.num 7)) [])
      (some (.err (.int 7))) = true := by native_decide
-- isOkE on ok → true.
example :
    beqOptVal
      (evalL (.isOkE (.okE (.num 1))) [])
      (some (.bool true)) = true := by native_decide
-- isOkE on err → false.
example :
    beqOptVal
      (evalL (.isOkE (.errE (.num 1))) [])
      (some (.bool false)) = true := by native_decide
-- getOk on ok → underlying value.
example :
    beqOptVal
      (evalL (.getOk (.okE (.num 42))) [])
      (some (.int 42)) = true := by native_decide
-- getOk on err → typed residue (host raises).
example :
    beqOptVal
      (evalL (.getOk (.errE (.num 1))) [])
      none = true := by native_decide
-- isOkE on non-Result → typed residue.
example :
    beqOptVal
      (evalL (.isOkE (.num 0)) [])
      none = true := by native_decide
-- Nested: getOk inside a let.
example :
    beqOptVal
      (evalL (.letE "r" (.okE (.num 9))
                 (.add (.getOk (.var "r")) (.num 1)))
             [])
      (some (.int 10)) = true := by native_decide

-- E1.8 (#1042) inline `native_decide` sanity for FindFirst / AlwaysUntil / EventuallyAfter.

-- findFirst over [1,2,3]: first item where slot_item > 1 → opt (some {slot_idx:1, slot_item:2}).
example :
    beqOptVal
      (evalL
        (.findFirst
          (.listAppend (.listSingleton (.num 1))
            (.listAppend (.listSingleton (.num 2)) (.listSingleton (.num 3))))
          "ix" "it"
          (.gt (.fieldAccess (.var "it") "slot_item") (.num 1))
          (.var "it"))
        [])
      (some (.opt (some
        (.record [("slot_idx", .int 1), ("slot_item", .int 2)])))) = true := by native_decide
-- findFirst with no match → opt none.
example :
    beqOptVal
      (evalL
        (.findFirst (.listSingleton (.num 1)) "ix" "it"
          (.boollit false) (.var "it"))
        [])
      (some (.opt none)) = true := by native_decide
-- findFirst on empty list → opt none.
example :
    beqOptVal
      (evalL
        (.findFirst .emptyList "ix" "it" (.boollit true) (.var "it"))
        [])
      (some (.opt none)) = true := by native_decide
-- findFirst on non-list lst → typed residue.
example :
    beqOptVal
      (evalL (.findFirst (.num 5) "ix" "it" (.boollit true) (.var "it")) [])
      none = true := by native_decide

-- alwaysUntil: for items with t > 0 in [{t:1}, {t:2}], pred (slot_item.t < 100)
-- holds for both; stop never fires → fall-through true.
example :
    beqOptVal
      (evalL
        (.alwaysUntil
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 2)])))
          (.num 0) "it"
          (.lt (.fieldAccess (.var "it") "t") (.num 100))
          (.boollit false))
        [])
      (some (.bool true)) = true := by native_decide
-- alwaysUntil: pred fails at item t=2 → false.
example :
    beqOptVal
      (evalL
        (.alwaysUntil
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 2)])))
          (.num 0) "it"
          (.lt (.fieldAccess (.var "it") "t") (.num 2))   -- pred: t < 2, fails at t=2
          (.boollit false))
        [])
      (some (.bool false)) = true := by native_decide
-- alwaysUntil: from_t gate skips items with t ≤ from_t. from_t=1 skips t=1.
example :
    beqOptVal
      (evalL
        (.alwaysUntil
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 2)])))
          (.num 1) "it"
          (.lt (.fieldAccess (.var "it") "t") (.num 100))   -- pred true; only t=2 checked
          (.boollit false))
        [])
      (some (.bool true)) = true := by native_decide
-- alwaysUntil: stop fires → true (pred held to here).
example :
    beqOptVal
      (evalL
        (.alwaysUntil
          (.listSingleton (.makeRecord [("t", .num 1)]))
          (.num 0) "it"
          (.boollit false)   -- pred would fail
          (.boollit true))   -- stop fires first → return true
        [])
      (some (.bool true)) = true := by native_decide

-- eventuallyAfter: some item satisfies pred → true.
example :
    beqOptVal
      (evalL
        (.eventuallyAfter
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 5)])))
          (.num 0) "it"
          (.gte (.fieldAccess (.var "it") "t") (.num 5)))
        [])
      (some (.bool true)) = true := by native_decide
-- eventuallyAfter: no item satisfies → false.
example :
    beqOptVal
      (evalL
        (.eventuallyAfter
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 2)])))
          (.num 0) "it"
          (.boollit false))
        [])
      (some (.bool false)) = true := by native_decide
-- eventuallyAfter: from_t skips early items.
example :
    beqOptVal
      (evalL
        (.eventuallyAfter
          (.listAppend (.listSingleton (.makeRecord [("t", .num 1)]))
            (.listSingleton (.makeRecord [("t", .num 5)])))
          (.num 5) "it"
          (.boollit true))   -- from_t=5 skips both t=1 and t=5 → fall-through false
        [])
      (some (.bool false)) = true := by native_decide
-- eventuallyAfter on non-list → typed residue.
example :
    beqOptVal
      (evalL (.eventuallyAfter (.num 5) (.num 0) "it" (.boollit true)) [])
      none = true := by native_decide

-- E1.10 (#1047) inline `native_decide` sanity for BoundedFix.

-- Countdown to 0: state0 = 5; step = state - 1; stopPred = state == 0; fuel = 10.
-- Should converge at steps=5 with state=0.
example :
    beqOptVal
      (evalL (.boundedFix
                (.num 5) "s"
                (.sub (.var "s") (.num 1))
                (.eqE (.var "s") (.num 0))
                10)
             [])
      (some (.record [("converged", .bool true),
                      ("state",     .int 0),
                      ("steps",     .int 5)])) = true := by native_decide
-- Convergence at step 0 (initial state already satisfies stopPred).
example :
    beqOptVal
      (evalL (.boundedFix
                (.num 0) "s"
                (.sub (.var "s") (.num 1))
                (.eqE (.var "s") (.num 0))
                10)
             [])
      (some (.record [("converged", .bool true),
                      ("state",     .int 0),
                      ("steps",     .int 0)])) = true := by native_decide
-- Fuel exhaustion: never converges → converged=false, steps=fuel.
example :
    beqOptVal
      (evalL (.boundedFix
                (.num 100) "s"
                (.sub (.var "s") (.num 1))
                (.eqE (.var "s") (.num 0))
                3)
             [])
      (some (.record [("converged", .bool false),
                      ("state",     .int 97),
                      ("steps",     .int 3)])) = true := by native_decide
-- Sum-until-threshold pattern: accumulate (init 0); step = state + 7;
-- stopPred = state ≥ 20; fuel = 10. Reaches 21 at step 3.
example :
    beqOptVal
      (evalL (.boundedFix
                (.num 0) "s"
                (.add (.var "s") (.num 7))
                (.gte (.var "s") (.num 20))
                10)
             [])
      (some (.record [("converged", .bool true),
                      ("state",     .int 21),
                      ("steps",     .int 3)])) = true := by native_decide
-- Per-step residue propagation: stepBody residues → fix none.
example :
    beqOptVal
      (evalL (.boundedFix
                (.num 5) "s"
                (.add (.var "s") (.unwrapSome .noneLit))   -- residue inside step
                (.eqE (.var "s") (.num 0))
                3)
             [])
      none = true := by native_decide
-- Non-Bool stopPred → typed residue.
example :
    beqOptVal
      (evalL (.boundedFix (.num 5) "s" (.var "s") (.num 1) 3) [])
      none = true := by native_decide
-- Fuel = 0: post-loop check on state0.
example :
    beqOptVal
      (evalL (.boundedFix (.num 7) "s" (.var "s") (.boollit true) 0) [])
      (some (.record [("converged", .bool true),
                      ("state",     .int 7),
                      ("steps",     .int 0)])) = true := by native_decide

-- E1.9 (#1045) inline `native_decide` sanity for Call.
-- These use `evalLF` directly to pass a programs table + fuel.

-- Identity program: id(x) = x. Call id(42) → 42.
example :
    beqOptVal
      (evalLF (.call "id" [.num 42]) [] [("id", ["x"], .var "x")] 10)
      (some (.int 42)) = true := by native_decide
-- Double program: double(x) = x + x. Call double(5) → 10.
example :
    beqOptVal
      (evalLF (.call "double" [.num 5]) [] [("double", ["x"], .add (.var "x") (.var "x"))] 10)
      (some (.int 10)) = true := by native_decide
-- Two-arg program: add(a, b) = a + b. Call add(3, 4) → 7.
example :
    beqOptVal
      (evalLF (.call "add" [.num 3, .num 4]) [] [("add", ["a", "b"], .add (.var "a") (.var "b"))] 10)
      (some (.int 7)) = true := by native_decide
-- Caller env DOES NOT leak into callee body (fresh-scope semantics).
-- Caller binds `x` to 99; callee's `x` param shadows it. Result = 1 (callee's x).
example :
    beqOptVal
      (evalLF (.call "id" [.num 1]) [("x", .int 99)] [("id", ["x"], .var "x")] 10)
      (some (.int 1)) = true := by native_decide
-- Args evaluated in CALLER's env (host fidelity).
-- Caller binds y=8; arg is `y + 2 = 10`; callee returns it doubled.
example :
    beqOptVal
      (evalLF (.call "double" [.add (.var "y") (.num 2)])
              [("y", .int 8)]
              [("double", ["x"], .add (.var "x") (.var "x"))]
              10)
      (some (.int 20)) = true := by native_decide
-- Unknown program name → typed residue.
example :
    beqOptVal
      (evalLF (.call "missing" [.num 1]) [] [("id", ["x"], .var "x")] 10)
      none = true := by native_decide
-- Arity mismatch (1 param, 2 args) → typed residue.
example :
    beqOptVal
      (evalLF (.call "id" [.num 1, .num 2]) [] [("id", ["x"], .var "x")] 10)
      none = true := by native_decide
-- Per-arg residue propagates (arg is `unwrapSome noneLit`).
example :
    beqOptVal
      (evalLF (.call "id" [.unwrapSome .noneLit]) [] [("id", ["x"], .var "x")] 10)
      none = true := by native_decide
-- Recursive Call: countdown(n) = if n ≤ 0 then 0 else countdown(n-1) — terminates.
example :
    beqOptVal
      (evalLF (.call "cd" [.num 5]) []
        [("cd", ["n"],
          .ifE (.lte (.var "n") (.num 0))
               (.num 0)
               (.call "cd" [.sub (.var "n") (.num 1)]))]
        10)
      (some (.int 0)) = true := by native_decide
-- Fuel exhaustion: recursion exceeds fuel → [E1.9_fuel_exhausted] residue.
example :
    beqOptVal
      (evalLF (.call "cd" [.num 100]) []
        [("cd", ["n"],
          .ifE (.lte (.var "n") (.num 0))
               (.num 0)
               (.call "cd" [.sub (.var "n") (.num 1)]))]
        5)
      none = true := by native_decide
-- The 2-arg wrapper `evalL` with default fuel: non-Call programs unchanged.
example : beqOptVal (evalL (.add (.num 2) (.num 3)) []) (some (.int 5)) = true := by native_decide
-- The 2-arg wrapper on a Call WITHOUT programs → typed residue (unknown name).
example : beqOptVal (evalL (.call "any" []) []) none = true := by native_decide

end MSTNFSlotSemanticsCoreMWE

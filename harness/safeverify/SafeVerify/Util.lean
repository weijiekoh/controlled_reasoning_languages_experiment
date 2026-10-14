import SafeVerify.Types
import Lean

open Lean SafeVerify

/-- Port to Lean v4.33.1: auto-generated auxiliary declarations (`noConfusionType`,
`noConfusion`, ...) take a hygienic universe parameter whose name embeds the module
name, e.g. `v._@.Target.<hash>._hygCtx._hyg.5` vs `v._@.Submission.<hash>...`. Two
elaborations of identical source therefore differ only by this alpha-renaming. Rename
every level parameter that carries macro scopes to a positional canonical name before
comparing. User-written level parameters (`u`, `v`) have no macro scopes and are left
untouched, so this does not weaken checks on user-written declarations. -/
def canonHygienicLevelParams (ci : ConstantInfo) : ConstantInfo :=
  let ps := ci.levelParams
  if !ps.any Name.hasMacroScopes then ci else
  let rec rename : List Name → Nat → List Name
    | [], _ => []
    | n :: ns, i => (if n.hasMacroScopes then Name.mkSimple s!"_sv_hyg_{i}" else n) :: rename ns (i + 1)
  let ps' := rename ps 0
  let lvls := ps'.map Level.param
  let inst (e : Expr) : Expr := e.instantiateLevelParams ps lvls
  match ci with
  | .defnInfo d => .defnInfo { d with levelParams := ps', type := inst d.type, value := inst d.value }
  | .thmInfo t => .thmInfo { t with levelParams := ps', type := inst t.type, value := inst t.value }
  | .opaqueInfo o => .opaqueInfo { o with levelParams := ps', type := inst o.type, value := inst o.value }
  | .ctorInfo c => .ctorInfo { c with levelParams := ps', type := inst c.type }
  | .inductInfo i => .inductInfo { i with levelParams := ps', type := inst i.type }
  | ci => ci

/-
From Lean.Environment
Check if two theorems have the same type and name
-/
def equivThm (cinfo₁ cinfo₂ : ConstantInfo) : Bool := Id.run do
  -- Port to Lean v4.33.1: compare modulo hygienic level-parameter names.
  let .thmInfo tval₁ := canonHygienicLevelParams cinfo₁ | false
  let .thmInfo tval₂ := canonHygienicLevelParams cinfo₂ | false
  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all

/-
Check if two definitions have the same type and name.
If checkVal is true, then also check their values are the same
-/
def equivDefn (ctarget cnew : ConstantInfo) (checkVal : Bool := false) : Bool := Id.run do
  -- Port to Lean v4.33.1: compare modulo hygienic level-parameter names.
  let .defnInfo tval₁ := canonHygienicLevelParams ctarget | false
  let .defnInfo tval₂ := canonHygienicLevelParams cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.safety == tval₂.safety
    && (if checkVal then tval₁.value == tval₂.value else true)

/-
Check if two opaque constants are the same
-/
def equivOpaq (ctarget cnew : ConstantInfo) : Bool := Id.run do
  -- Port to Lean v4.33.1: compare modulo hygienic level-parameter names.
  let .opaqueInfo tval₁ := canonHygienicLevelParams ctarget | false
  let .opaqueInfo tval₂ := canonHygienicLevelParams cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.all == tval₂.all
    && tval₁.isUnsafe == tval₂.isUnsafe
    && tval₁.value == tval₂.value

/-
Check if two constructors are the same
-/
def equivCtor (ctarget cnew : ConstantInfo) : Bool := Id.run do
  -- Port to Lean v4.33.1: compare modulo hygienic level-parameter names.
  let .ctorInfo tval₁ := canonHygienicLevelParams ctarget | false
  let .ctorInfo tval₂ := canonHygienicLevelParams cnew | false

  return tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.induct == tval₂.induct
    && tval₁.cidx == tval₂.cidx
    && tval₁.numParams == tval₂.numParams
    && tval₁.numFields == tval₂.numFields
    && tval₁.isUnsafe == tval₂.isUnsafe

/-
Check if two inductive types are the same.
Takes a lookup function to retrieve constructor ConstantInfo by name.
-/
def equivInduct (ctarget cnew : ConstantInfo)
    (lookupTarget lookupNew : Name → Option ConstantInfo) : Bool := Id.run do
  -- Port to Lean v4.33.1: compare modulo hygienic level-parameter names.
  let .inductInfo tval₁ := canonHygienicLevelParams ctarget | false
  let .inductInfo tval₂ := canonHygienicLevelParams cnew | false

  -- Check basic fields
  unless tval₁.name == tval₂.name
    && tval₁.type == tval₂.type
    && tval₁.levelParams == tval₂.levelParams
    && tval₁.numParams == tval₂.numParams
    && tval₁.numIndices == tval₂.numIndices
    && tval₁.all == tval₂.all
    && tval₁.ctors == tval₂.ctors
    && tval₁.isRec == tval₂.isRec
    && tval₁.isReflexive == tval₂.isReflexive
    && tval₁.isUnsafe == tval₂.isUnsafe
  do return false

  -- Check each constructor using equivCtor
  for ctorName in tval₁.ctors do
    let some ctor₁ := lookupTarget ctorName | return false
    let some ctor₂ := lookupNew ctorName | return false
    unless equivCtor ctor₁ ctor₂ do return false

  return true

open Elab Meta Term Tactic

structure NegateConfig where
  distrib : Bool := false
deriving Inhabited

/-- Takes an expression `e` and outputs the negation of `e`, pushing `not` accross
`e`. For example, occurences of `¬ ∀ a, p a` are replaced by `∃ a, ¬ p a`. -/
private def negateExpr (cfg : NegateConfig) (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).cleanupAnnotations
  handler e
where handler (e : Expr) : MetaM Expr := do
  match e with
  | .app (.app (.const ``And _) p) q =>
    if cfg.distrib then
      return (mkOr (← handler p) (← handler q))
    else
      return (.forallE `_  p (← handler  q) .default)
  | .forallE name ty body binfo =>
    let body' : Expr := .lam name ty (← handler body) binfo
    return (← mkAppM ``Exists #[body'])
  | .app (.app (.const ``Or _) p) q =>
    return (mkAnd (← handler p) (← handler q))
  | .app (.app (.const ``Exists _) _) (.lam name btype body binfo) =>
    return .forallE name btype (← handler body) binfo
  | .lam name btype body binfo =>
    return .lam name btype (← handler body) binfo
  -- handle `≠` separately
  | .app (.app (.app (.const ``Ne lvls) α) p) q =>
    return .app (.app (.app (.const ``Eq lvls) α) p) q
  | .app (.const ``Not _) p =>
    return p
  | _ =>
    return mkNot e

def checkNegatedTheorem {m} [Monad m] [MonadLiftT CoreM m]
    (ctarget cnew : ConstantInfo) : m Bool :=
  -- We run in MetaM but don't really need any context
  Lean.Meta.MetaM.run' do
  unless ctarget.levelParams == cnew.levelParams do return false
  let targetType := ctarget.type
  let negatedType ← negateExpr default targetType
  match Lean.Kernel.isDefEq (← getEnv) (← getLCtx) negatedType cnew.type with
  | .error _ =>  return false
  | .ok bool => return bool

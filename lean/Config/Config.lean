module

public import Lean

public section

namespace EnvConfig

inductive Validated (α : Type) where
  | ok (value : α)
  | errors (messages : Array String)

instance : Inhabited (Validated α) := ⟨.errors #[]⟩

namespace Validated

instance : Applicative Validated where
  pure := .ok
  map f v := match v with
    | .ok a => .ok (f a)
    | .errors es => .errors es
  seq f x := match f, x () with
    | .ok g, .ok a => .ok (g a)
    | .ok _, .errors es => .errors es
    | .errors es, .ok _ => .errors es
    | .errors e₁, .errors e₂ => .errors (e₁ ++ e₂)

def toIO : Validated α → IO α
  | .ok a => pure a
  | .errors es =>
    throw <| IO.userError <|
      "configuration error:\n" ++ String.intercalate "\n" (es.toList.map ("  • " ++ ·))

end Validated

def trimWS (s : String) : String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  (cs.reverse.dropWhile Char.isWhitespace).reverse.foldl (·.push ·) ""

class EnvValue (α : Type) where
  parse : String → Except String α

instance : EnvValue String where
  parse s := .ok s

instance : EnvValue Nat where
  parse s := match (trimWS s).toNat? with
    | some n => .ok n
    | none => .error s!"expected a natural number, got {repr s}"

instance : EnvValue Int where
  parse s := match (trimWS s).toInt? with
    | some n => .ok n
    | none => .error s!"expected an integer, got {repr s}"

instance : EnvValue Bool where
  parse s := match (trimWS s).map Char.toLower with
    | "true" | "1" | "yes" | "on" => .ok true
    | "false" | "0" | "no" | "off" => .ok false
    | _ => .error s!"expected a boolean, got {repr s}"

instance : EnvValue System.FilePath where
  parse s := .ok ⟨s⟩

/-- Comma-separated list; blank entries are dropped, so `""` gives `#[]`. -/
instance [EnvValue α] : EnvValue (Array α) where
  parse s := ((s.splitOn ",").map trimWS |>.filter (· ≠ "")).toArray.mapM EnvValue.parse

instance [EnvValue α] : EnvValue (List α) where
  parse s := return (← EnvValue.parse (α := Array α) s).toList

def readValue [EnvValue α] (key : String) : IO (Option (Validated α)) := do
  match ← IO.getEnv key with
  | none => return none
  | some raw =>
    match EnvValue.parse (α := α) raw with
    | .ok a => return some (.ok a)
    | .error msg => return some (.errors #[s!"{key}: {msg}"])

class FromEnv (α : Type) where
  ofEnv : (pfx : String) → IO (Validated α)

class EnvPrefix (α : Type) where
  envPrefix : String

class EnvField (α : Type) where
  read : (key : String) → IO (Validated α)
  readWithDefault : (key : String) → (dflt : α) → IO (Validated α)

instance (priority := 1000) [EnvValue α] : EnvField α where
  read key := do
    match ← readValue (α := α) key with
    | some v => return v
    | none => return .errors #[s!"{key}: required variable is not set"]
  readWithDefault key dflt := do
    match ← readValue (α := α) key with
    | some v => return v
    | none => return .ok dflt

instance (priority := 1100) [EnvValue α] : EnvField (Option α) where
  read key := do
    match ← readValue (α := α) key with
    | some (.ok a) => return .ok (some a)
    | some (.errors es) => return .errors es
    | none => return .ok none
  readWithDefault key dflt := do
    match ← readValue (α := α) key with
    | some (.ok a) => return .ok (some a)
    | some (.errors es) => return .errors es
    | none => return .ok dflt

instance (priority := 900) [FromEnv α] : EnvField α where
  read key := FromEnv.ofEnv (key ++ "_")
  readWithDefault key dflt := do
    match ← FromEnv.ofEnv (α := α) (key ++ "_") with
    | .ok a => return .ok a
    | .errors _ => return .ok dflt

def loadConfig (α : Type) [FromEnv α] [EnvPrefix α] : IO α := do
  (← FromEnv.ofEnv (α := α) (EnvPrefix.envPrefix (α := α))).toIO

def loadConfigWith (α : Type) [FromEnv α] (pfx : String) : IO α := do
  (← FromEnv.ofEnv (α := α) pfx).toIO

def tryLoadConfig (α : Type) [FromEnv α] [EnvPrefix α] :
    IO (Except (Array String) α) := do
  match ← FromEnv.ofEnv (α := α) (EnvPrefix.envPrefix (α := α)) with
  | .ok a => return .ok a
  | .errors es => return .error es

section Deriving
open Lean Elab Command Term Meta PrettyPrinter

def screamingSnake (s : String) : String := Id.run do
  let mut out := ""
  let mut prevLower := false
  for c in s.toList do
    if c.isUpper && prevLower then
      out := out.push '_'
    out := out.push c.toUpper
    prevLower := c.isLower || c.isDigit
  return out

private def mkFromEnvInstance (declName : Name) : CommandElabM Bool := do
  let env ← getEnv
  unless isStructure env declName do
    throwError "`FromEnv` can only be derived for structures; {declName} is not one"
  let some (.inductInfo info) := env.find? declName
    | throwError "{declName} is not an inductive declaration"
  unless info.numParams == 0 && info.levelParams.isEmpty do
    throwError
      "`FromEnv` does not support parameterised or universe-polymorphic structures"
  let fields := getStructureFields env declName
  for f in fields do
    if (isSubobjectField? env declName f).isSome then
      throwError
        "`FromEnv` does not support `extends`; give the parent structure its own field"
  let ctorName := (getStructureCtor env declName).name
  let ty := mkCIdent declName
  let ctor := mkCIdent ctorName
  -- Structure defaults live in `T.field._default`, which is elaboration-time
  -- only and has no compiled code, so it cannot be *referenced* by the instance
  -- we are about to emit. Recover the underlying term instead and splice that.
  let defaults : Array (Option Term) ← liftTermElabM do
    forallTelescopeReducing (← getConstInfo ctorName).type fun args _ => do
      let mut out := #[]
      for i in [0 : fields.size] do
        let f := fields[i]!
        match getDefaultFnForField? env declName f with
        | none => out := out.push none
        | some d =>
          let info ← getConstInfo d
          unless ← isDefEq info.type (← inferType args[i]!) do
            throwError
              "`FromEnv`: the default for field `{f}` refers to another field, \
               which cannot be resolved before that field is read"
          let some val := info.value?
            | throwError "`FromEnv`: cannot read the default value for field `{f}`"
          out := out.push (some (← withOptions (·.setBool `pp.fullNames true) <| delab val))
      return out
  let mut stmts : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
  let mut vals : Array Ident := #[]
  for i in [0 : fields.size] do
    let f := fields[i]!
    let v := mkIdent (Name.mkSimple s!"__field_{f.getString!}")
    let key := Syntax.mkStrLit (screamingSnake f.getString!)
    stmts := stmts.push <| ←
      match defaults[i]! with
      | some dflt =>
        `(Lean.Parser.Term.doSeqItem|
            let $v ← EnvConfig.EnvField.readWithDefault (pfx ++ $key) $dflt)
      | none =>
        `(Lean.Parser.Term.doSeqItem|
            let $v ← EnvConfig.EnvField.read (pfx ++ $key))
    vals := vals.push v
  -- `Ctor <$> v₁ <*> v₂ <*> …`, which accumulates errors across all fields.
  let app ←
    match vals.toList with
    | [] => `(pure $ctor)
    | v :: vs => do
      let mut a ← `($ctor <$> $v)
      for w in vs do
        a ← `($a <*> $w)
      pure a
  stmts := stmts.push (← `(Lean.Parser.Term.doSeqItem| return $app))
  elabCommand <| ← `(command|
    instance : EnvConfig.FromEnv $ty where
      ofEnv pfx := do $[$stmts]*)
  return true

initialize
  Lean.Elab.registerDerivingHandler ``FromEnv fun declNames =>
    declNames.allM mkFromEnvInstance

end Deriving

end EnvConfig

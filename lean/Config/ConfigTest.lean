import Config.Config

open EnvConfig

def expectEq [BEq α] [Repr α] (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

/-! The introductory case: one required value and two structure defaults. -/
structure FoobarConfig where
  baz : Nat := 8
  qux : String
  maxRetries : Nat := 3
  deriving FromEnv

instance : EnvPrefix FoobarConfig := ⟨"FOOBAR_"⟩

def testDefaultsAndPrefix : IO Unit := do
  let cfg ← loadConfig FoobarConfig
  expectEq cfg.qux "from-environment" "required string"
  expectEq cfg.baz 8 "first default"
  expectEq cfg.maxRetries 3 "camel-case default"

def testOverridesAndCustomPrefix : IO Unit := do
  let cfg ← loadConfigWith FoobarConfig "OVERRIDE_"
  expectEq cfg.qux "overridden" "custom prefix"
  expectEq cfg.baz 21 "trimmed natural-number override"
  expectEq cfg.maxRetries 0 "maxRetries maps to MAX_RETRIES"

/-! Built-in scalar, collection, optional, and path decoders. -/
structure RichConfig where
  enabled : Bool
  offset : Int
  ports : Array Nat
  flags : List Bool
  note : Option String
  missing : Option Nat
  stateDir : System.FilePath
  empty : Array Nat
  deriving FromEnv

instance : EnvPrefix RichConfig := ⟨"RICH_"⟩

def testBuiltInValues : IO Unit := do
  let cfg ← loadConfig RichConfig
  expectEq cfg.enabled true "case-insensitive boolean"
  expectEq cfg.offset (-42) "signed integer"
  expectEq cfg.ports #[80, 443, 8080] "trimmed array with blank entry"
  expectEq cfg.flags [true, false, true, false] "boolean list aliases"
  expectEq cfg.note (some "  preserve whitespace  ") "present optional string"
  expectEq cfg.missing none "missing optional value"
  expectEq cfg.stateDir.toString "/var/lib/acme widgets" "file path"
  expectEq cfg.empty #[] "empty comma-separated array"

/-! Nested structures recursively extend the field name with an underscore. -/
structure DatabaseConfig where
  host : String
  port : Nat := 5432
  deriving FromEnv

structure ServiceConfig where
  database : DatabaseConfig
  workers : Nat
  deriving FromEnv

instance : EnvPrefix ServiceConfig := ⟨"NESTED_"⟩

def testNestedConfig : IO Unit := do
  let cfg ← loadConfig ServiceConfig
  expectEq cfg.database.host "db.internal" "nested required field"
  expectEq cfg.database.port 5432 "nested default"
  expectEq cfg.workers 6 "sibling field"

/-! Applications can extend EnvValue for domain-specific field types. -/
inductive LogLevel where
  | debug
  | info
  | warn
  deriving BEq, Repr

instance : EnvValue LogLevel where
  parse
    | "debug" => .ok .debug
    | "info" => .ok .info
    | "warn" => .ok .warn
    | value => .error s!"expected debug, info, or warn, got {repr value}"

structure CustomConfig where
  logLevel : LogLevel
  labels : Array String
  deriving FromEnv

instance : EnvPrefix CustomConfig := ⟨"CUSTOM_"⟩

def testCustomValue : IO Unit := do
  let cfg ← loadConfig CustomConfig
  expectEq cfg.logLevel .warn "custom EnvValue"
  expectEq cfg.labels #["api", "worker", "scheduler"] "custom config collection"

/-! Independent field failures accumulate in declaration order. -/
structure BrokenConfig where
  count : Nat := 10
  enabled : Bool
  name : String
  backupPort : Nat := 9000
  deriving FromEnv

instance : EnvPrefix BrokenConfig := ⟨"BROKEN_"⟩

def testAccumulatedErrors : IO Unit := do
  match ← tryLoadConfig BrokenConfig with
  | .ok _ => throw (IO.userError "broken config unexpectedly loaded")
  | .error errors =>
    expectEq errors.toList [
      "BROKEN_COUNT: expected a natural number, got \"many\"",
      "BROKEN_ENABLED: expected a boolean, got \"perhaps\"",
      "BROKEN_NAME: required variable is not set",
      "BROKEN_BACKUP_PORT: expected a natural number, got \"-1\"",
    ] "accumulated errors"

structure RequiredConfig where
  value : String
  count : Nat
  deriving FromEnv

def testThrowingLoader : IO Unit := do
  let caught ← try
    let _ ← loadConfigWith RequiredConfig "CONFIG_TEST_ABSENT_"
    pure (none : Option String)
  catch error =>
    pure (some (toString error))
  expectEq caught (some <|
    "configuration error:\n" ++
    "  • CONFIG_TEST_ABSENT_VALUE: required variable is not set\n" ++
    "  • CONFIG_TEST_ABSENT_COUNT: required variable is not set")
    "loadConfigWith exception"

def main : IO Unit := do
  testDefaultsAndPrefix
  testOverridesAndCustomPrefix
  testBuiltInValues
  testNestedConfig
  testCustomValue
  testAccumulatedErrors
  testThrowingLoader
  IO.println "config loading: all cases passed"

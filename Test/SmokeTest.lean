import Acme

/-!
Workspace smoke test: the ecosystem libraries resolve, link, and run in one
binary — the gRPC runtime, the PostgreSQL client, and the protovalidate
runtime, each touched through a representative symbol.
-/

def expect (cond : Bool) (msg : String) : IO Unit := do
  unless cond do throw (IO.userError msg)

def main : IO Unit := do
  expect (Acme.name == "acme-widgets") "acme root module"
  -- pg-lean: encode a startup message through the wire layer
  let startup := Pg.Protocol.encodeStartup #[("user", "acme")]
  expect (Pg.Protocol.getUInt32? startup 4 == some Pg.Protocol.protocolVersion)
    "pg-lean wire layer"
  -- grpc-lean: gRPC message framing roundtrip
  match Grpc.Message.encode { data := String.toUTF8 "widget" } with
  | .ok framed => expect (framed.size == 5 + 6) "grpc-lean framing"
  | .error status => throw (IO.userError s!"grpc-lean framing: {status.messageD}")
  -- protovalidate: a CEL runtime predicate
  expect (Cel.regexMatch "w-1" "^w-[0-9]+$") "protovalidate CEL runtime"
  IO.println "acme-widgets smoke: all ecosystem libraries linked"

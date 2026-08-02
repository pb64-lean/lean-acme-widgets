module

public import Grpc
public import Pg
public import Protovalidate.Cel
public import Protovalidate.Runtime

public section

namespace Acme

/-!
Root module of the Acme Widgets service. Inert for now: it exists to anchor
the `lean/` source root and to prove that the whole sibling ecosystem —
gRPC runtime, PostgreSQL client, and protovalidate runtime — resolves and
links in one workspace. Service logic arrives on top of this.
-/

def name : String := "acme-widgets"

def version : String := "0.0.1"

end Acme

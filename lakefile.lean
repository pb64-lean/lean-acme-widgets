import Lake
open Lake DSL

/-!
# lakefile.lean — IDE project model only.

Bazel owns the real build and tests in this repository; Lake exists so that
`lake serve` / editors resolve the hand-authored ecosystem imports (`Grpc`,
`Pg`, `Protovalidate.*`) from the sibling checkouts. The generated
`AcmeDb` modules and sources that import them remain Bazel-only.

Use Bazel for validation:

  bazel test //...
-/

package «lean-acme-widgets» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «pg-lean» from "../pg-lean"
require «rules-lean-grpc» from "../grpc-lean"
require «protovalidate-lean» from "../protovalidate-lean"

lean_lib «Acme» where
  srcDir := "lean"
  roots := #[`Acme]

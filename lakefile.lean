import Lake
open Lake DSL

/-!
# lakefile.lean — IDE project model only.

Bazel owns the real build and tests in this repository; Lake exists so that
`lake serve` / editors resolve the ecosystem imports (`Grpc`, `Pg`,
`Protovalidate.*`) from the sibling checkouts.

Use Bazel for validation:

  bazel test //...
-/

package «lean-acme-widgets» where
  leanOptions := #[⟨`experimental.module, true⟩]

require «pg-lean» from "../pg-lean"
require «rules-lean-grpc» from "../grpc-lean"

lean_lib «Acme» where
  srcDir := "lean"
  roots := #[`Acme]

import Lake
open Lake DSL

package «hax-lib-additions» where
  license := "MIT"
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Hax prelude library (Rust primitives, core models, tactics)
@[default_target]
lean_lib «Hax» where
  srcDir := "."

require Qq from git
  "https://github.com/leanprover-community/quote4" @ "dce0ad79c486cb1fb504af04f953c3466b0c6db8"

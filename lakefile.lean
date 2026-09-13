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
  "https://github.com/leanprover-community/quote4" @ "92c15be17b7caf78c2ad767ec40f89052d908d81"

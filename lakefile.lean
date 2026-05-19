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
  "https://github.com/leanprover-community/quote4" @ "707efb56d0696634e9e965523a1bbe9ac6ce141d"

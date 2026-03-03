import Lake
open Lake DSL

package «hax-lib-additions» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Hax prelude library (Rust primitives, core models, tactics)
@[default_target]
lean_lib «Hax» where
  srcDir := "."

require Qq from git
  "https://github.com/leanprover-community/quote4" @ "b8f98e9087e02c8553945a2c5abf07cec8e798c3"

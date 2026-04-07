/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/

namespace Rust_primitives.Hax

  abbrev Never : Type := Empty
  abbrev never_to_any.{u} {α : Sort u} : Never → α := Empty.elim

end Rust_primitives.Hax

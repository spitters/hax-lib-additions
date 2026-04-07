/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Hax.Rust_primitives

/-! Core-model for `Clone`, represented as a no-op (pure identity). -/

namespace Core.Clone

class Clone (Self : Type) where

def Clone.clone {Self: Type} : Self -> RustM Self :=
  fun x => pure x

end Core.Clone

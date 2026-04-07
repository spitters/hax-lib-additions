/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Hax.Core_models.Extracted

def Core_models.Ops.Deref.Deref.deref {α Allocator} (_ : Type) (v: Alloc.Vec.Vec α Allocator)
  : RustM (Array α)
  := pure v

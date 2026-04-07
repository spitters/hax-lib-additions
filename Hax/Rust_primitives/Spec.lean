/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Std.Do
import Hax.Rust_primitives.RustM

open Std.Do

/-! Hax specification contracts bundling requires/ensures with Hoare triples. -/

structure Spec {α}
    (requires : RustM Prop)
    (ensures : α → RustM Prop)
    (f : RustM α) where
  pureRequires : {p : Prop // ⦃ ⌜ True ⌝ ⦄ requires ⦃ ⇓r => ⌜ r = p ⌝ ⦄}
  pureEnsures : {p : α → Prop // pureRequires.val → ∀ a, ⦃ ⌜ True ⌝ ⦄ ensures a ⦃ ⇓r => ⌜ r = p a ⌝ ⦄}
  contract : ⦃ ⌜ pureRequires.val ⌝ ⦄ f ⦃ ⇓r => ⌜ pureEnsures.val r ⌝ ⦄

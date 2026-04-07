/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Std.Do.PostCond

namespace Std.Do
universe u
variable {ps : PostShape.{u}} {α σ ε : Type u}

theorem PostCond.entails.of_left_entails
    {p q : α → Assertion ps} {x : ExceptConds ps}  (h : ∀ a, p a ⊢ₛ q a) :
    (p, x) ⊢ₚ (q, x) := by simp [h]

end Std.Do

/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Std.Tactic.BVDecide

macro "hax_bv_decide" c:Lean.Parser.Tactic.optConfig : tactic => `(tactic| (
  simp only [hax_bv_decide] at *; bv_decide $c
))

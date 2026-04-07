/-
Copyright (c) 2025 Cryspen, 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Hax.MissingCore.Clone

class Core.Marker.Copy.AssociatedTypes (Self : Type) where

class Core.Marker.Copy
  (Self : Type)
  [associatedTypes : outParam (Core.Marker.Copy.AssociatedTypes (Self :
      Type))]
  where
  [trait_constr : Core.Clone.Clone Self]

attribute [instance] Core.Marker.Copy.trait_constr

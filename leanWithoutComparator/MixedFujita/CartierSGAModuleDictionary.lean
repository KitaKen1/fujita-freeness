/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleFramesSGAModuleIso
public import MixedFujita.CartierSGALineBundle

/-!
The SGA presentation constructed from an actual Cartier divisor recovers its entire original
module sheaf. In particular, representing that SGA line bundle by a Cartier divisor again gives
a sheaf isomorphic to the original Cartier sheaf. The comparison is over every open and commutes
with restrictions; this extends the earlier global-section-set dictionary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)

/-- The actual Cartier sheaf is the SGA module sheaf of its constructed line-bundle presentation. -/
noncomputable def cartierSGAModuleIso : D.sheaf ≅ (cartierSGALineBundle D).toModules 1 :=
  moduleFramesSGAModuleIso D.sheaf (cartierEquationOpenCover D).U
    (cartierEquationOpenCover_frame (cartierEquationOpenCover D))
    (cartierEquationOpenCover_iSup_eq_top (cartierEquationOpenCover D))

/-- Returning from the SGA line bundle to an actual Cartier divisor recovers the same module
sheaf, without a supplied representation or sheaf comparison. -/
noncomputable def cartierSGARoundTripSheafIso :
    D.sheaf ≅ (sgaLineBundleCartierDivisor (cartierSGALineBundle D)).sheaf :=
  cartierSGAModuleIso D ≪≫ sgaLineBundleCartierIso (cartierSGALineBundle D)

theorem cartierSGAModuleIso_app_bijective (W : X.Opens) :
    Function.Bijective (Scheme.Modules.Hom.app (cartierSGAModuleIso D).hom W) :=
  ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app (cartierSGAModuleIso D).hom W)

theorem cartierSGARoundTripSheafIso_app_bijective (W : X.Opens) :
    Function.Bijective (Scheme.Modules.Hom.app (cartierSGARoundTripSheafIso D).hom W) :=
  ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app (cartierSGARoundTripSheafIso D).hom W)

end MixedFujita

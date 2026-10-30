/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleOpenFrameCoefficients

/-!
Identify the components of an actual frame on an open subscheme with
the coefficients of its actual ambient over-site frame. This evaluates
the fully faithful inverse on actual opens, rather than assuming that
the two presentations have the same component maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}}

theorem moduleRestrictFrameOverIso_component (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (V : (U : Scheme).Opens) (s : Γ(M, U.ι ''ᵁ V)) :
    moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e)
      (U.ι ''ᵁ V) (U.ι_image_le V) s =
      Scheme.Modules.Hom.app e.hom V s := by
  have h := (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_preimage
    (((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm).hom)
  exact ConcreteCategory.congr_hom
    (congrArg (fun b => Scheme.Modules.Hom.app b V) h) s

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleLocalPullbackCoefficients
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism

/-!
Actual scheme-module isomorphisms can be detected on an actual open cover,
and on its actual inverse-image cover under any scheme morphism. The proof
passes through the existing slice-site/open-subscheme equivalence and the
proved local-isomorphism criterion, without supplying global inverses.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {X Y : Scheme.{u}}

theorem moduleHom_isIso_of_openCover {I : Type v} (U : I → X.Opens)
    (hU : IsOpenCover U) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f)) : IsIso f := by
  apply SheafOfModules.isIso_of_coversTop ((Opens.coversTop_iff (X : Type u) U).mpr hU) f
  intro i
  have hi := h i
  let E := Scheme.Modules.overEquiv (U i)
  have hn := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality f
  have hc : IsIso (E.functor.map (f.over (U i)) ≫
      (Scheme.Modules.overFunctorEquiv (U i)).hom.app N) := by
    change IsIso ((SheafOfModules.overFunctor X.ringCatSheaf (U i) ⋙ E.functor).map f ≫
      (Scheme.Modules.overFunctorEquiv (U i)).hom.app N)
    rw [hn]
    infer_instance
  have : IsIso (E.functor.map (f.over (U i))) :=
    IsIso.of_isIso_comp_right (E.functor.map (f.over (U i)))
      ((Scheme.Modules.overFunctorEquiv (U i)).hom.app N)
  exact isIso_of_reflects_iso (f.over (U i)) E.functor

theorem moduleHom_isIso_iff_openCover {I : Type v} (U : I → X.Opens)
    (hU : IsOpenCover U) {M N : X.Modules} (f : M ⟶ N) :
    IsIso f ↔ ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map f) := by
  constructor
  · intro hf i
    exact Functor.map_isIso _ f
  · exact moduleHom_isIso_of_openCover U hU f

theorem moduleHom_isIso_of_preimage_openCover {I : Type v} (φ : Y ⟶ X) (U : I → X.Opens)
    (hU : IsOpenCover U) {M N : Y.Modules} (f : M ⟶ N)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U i).ι).map f)) : IsIso f := by
  apply moduleHom_isIso_of_openCover (fun i ↦ φ ⁻¹ᵁ U i) _ f h
  rw [IsOpenCover, ← Scheme.Hom.preimage_iSup, hU.iSup_eq_top, Scheme.Hom.preimage_top]

end MixedFujita

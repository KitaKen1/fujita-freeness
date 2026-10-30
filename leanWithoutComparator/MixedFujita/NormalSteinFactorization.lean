/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalSectionsAndStein
public import SGA.Foundations.Cohomology.SteinFactorization

/-!
The actual canonical Stein construction for an arbitrary proper morphism from a normal integral
scheme to a locally noetherian scheme. This allows the existing polynomial-Proj Cartier section
morphism, with its explicit hyperplane divisor equations, to use the proved Stein machinery.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Z : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian Z]

theorem properMap_exists_normal_stein_factorization (f : X ⟶ Z) [IsProper f]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (g : X ⟶ Y) (_ : IsDominant g) (h : Y ⟶ Z),
      IsProper g ∧ IsFinite h ∧ g ≫ h = f ∧
      (∀ V : Y.Opens, Function.Bijective (g.app V).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧
      ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := by
  have hfin : IsFinite f.fromNormalization := CohomologyAux.isFinite_fromNormalization f
  have : IsProper f.toNormalization := by
    have : IsProper (f.toNormalization ≫ f.fromNormalization) := by
      rw [f.toNormalization_fromNormalization]
      infer_instance
    exact IsProper.of_comp _ f.fromNormalization
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  have hiso (V : f.normalization.Opens) : IsIso (f.toNormalization.app V) :=
    CohomologyAux.isIso_toNormalization_app f V
  have happ (V : f.normalization.Opens) : Function.Bijective (f.toNormalization.app V).hom :=
    ConcreteCategory.bijective_of_isIso (f.toNormalization.app V)
  exact ⟨f.normalization, inferInstance, inferInstance, f.toNormalization, inferInstance,
    f.fromNormalization, inferInstance, hfin, f.toNormalization_fromNormalization, happ,
    zariskiConnectednessStatement X f.normalization f.toNormalization hiso,
    normal_stalks_of_all_open_app_bijective f.toNormalization hnorm happ⟩

end MixedFujita

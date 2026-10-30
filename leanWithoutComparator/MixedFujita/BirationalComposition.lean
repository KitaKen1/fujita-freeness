/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantBoundaryPerturbation

/-!
Actual function-field maps, Cartier pullbacks and chart Jacobians compose.
These identities supply the geometric comparison of discrepancies along a
tower of birational models. They do not assert existence of a common resolution.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T U : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral U]
  (ρ : T ⟶ X) (σ : U ⟶ T) [IsDominant ρ] [IsDominant σ]

/-- Function-field maps of actual dominant scheme morphisms compose. -/
theorem dominantFunctionFieldMap_comp :
    dominantFunctionFieldMap (σ ≫ ρ) = dominantFunctionFieldMap ρ ≫ dominantFunctionFieldMap σ := by
  ext a
  change (dominantFunctionFieldMap (σ ≫ ρ)).hom a =
    (dominantFunctionFieldMap σ).hom ((dominantFunctionFieldMap ρ).hom a)
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  have : Nonempty (ρ ⁻¹ᵁ V) := dominant_preimage_nonempty ρ V
  have : Nonempty (σ ⁻¹ᵁ (ρ ⁻¹ᵁ V)) := dominant_preimage_nonempty σ (ρ ⁻¹ᵁ V)
  change (dominantFunctionFieldMap (σ ≫ ρ)).hom (X.germToFunctionField V s) =
    (dominantFunctionFieldMap σ).hom
      ((dominantFunctionFieldMap ρ).hom (X.germToFunctionField V s))
  rw [dominantFunctionFieldMap_germ (σ ≫ ρ) V (σ ⁻¹ᵁ (ρ ⁻¹ᵁ V)) le_rfl,
    dominantFunctionFieldMap_germ ρ V (ρ ⁻¹ᵁ V) le_rfl,
    dominantFunctionFieldMap_germ σ (ρ ⁻¹ᵁ V) (σ ⁻¹ᵁ (ρ ⁻¹ᵁ V)) le_rfl]
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply,
    Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]

/-- Units of the actual function fields compose under pullback. -/
theorem dominantFunctionFieldUnits_comp (f : X.functionFieldˣ) :
    Units.map (dominantFunctionFieldMap (σ ≫ ρ)).hom.toMonoidHom f =
      Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom
        (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f) := by
  apply Units.ext
  simp only [Units.coe_map, dominantFunctionFieldMap_comp,
    CommRingCat.hom_comp]
  rfl

/-- The actual Cartier pullback is functorial. -/
theorem cartierPullback_comp (D : CartierDivisor X) :
    cartierPullback (σ ≫ ρ) D = cartierPullback σ (cartierPullback ρ D) := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ (σ t))
  refine ⟨Units.map (dominantFunctionFieldMap (σ ≫ ρ)).hom.toMonoidHom f, ?_, ?_⟩
  · exact cartierPullback_isLocalEquationAt (σ ≫ ρ) D t (by simpa using hf)
  · rw [dominantFunctionFieldUnits_comp]
    exact cartierPullback_isLocalEquationAt σ (cartierPullback ρ D) t
      (cartierPullback_isLocalEquationAt ρ D (σ t) hf)

variable {K : Type u} [Field K]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [U.Over (Spec (CommRingCat.of K))]
  [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Actual function-field K-algebra maps compose. -/
theorem dominantFunctionFieldAlgHom_comp :
    dominantFunctionFieldAlgHom (K := K) (σ ≫ ρ) =
      (dominantFunctionFieldAlgHom σ).comp (dominantFunctionFieldAlgHom ρ) := by
  apply AlgHom.toRingHom_injective
  exact congrArg CommRingCat.Hom.hom (dominantFunctionFieldMap_comp ρ σ)

/-- Bijectivity on actual function fields is stable under composition. -/
theorem dominantFunctionFieldAlgHom_comp_bijective
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) :
    Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ ≫ ρ)) := by
  rw [dominantFunctionFieldAlgHom_comp]
  exact hσ.comp hρ

/-- The Jacobian of an actual composite is the pulled first Jacobian times the second. -/
theorem chartRelativeJacobianDet_comp {n : ℕ} (c : EtaleChart K X n)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) :
    chartRelativeJacobianDet (σ ≫ ρ) c c'' =
      dominantFunctionFieldAlgHom (K := K) σ (chartRelativeJacobianDet ρ c c') *
        chartRelativeJacobianDet σ c' c'' := by
  unfold chartRelativeJacobianDet
  rw [dominantFunctionFieldAlgHom_comp]
  exact etaleRelativeJacobian_det_comp _ _ _ _
    (etaleChartFunctionFieldCoords_formallyEtale c') _
    (etaleChartFunctionFieldCoords_formallyEtale c'')

end MixedFujita

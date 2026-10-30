/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Projective.Chow
public import MixedFujita.QuasiProjectiveCartierAmpleness
public import MixedFujita.HironakaBlowUpModels

/-! 実Chowモデルの元ampleと非空開上同型から実関数体同型。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Chow's actual projective model carries an ORIGINAL ample Cartier
divisor internally, preserving the actual isomorphism over a nonempty open. -/
theorem proper_integral_exists_chow_model_with_ample_cartier
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))] :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : Y.Over (Spec (CommRingCat.of K)))
      (p : Y ⟶ X) (_ : p.IsOver (Spec (CommRingCat.of K)))
      (_ : IsHProjective p) (_ : Surjective p) (U : X.Opens),
      (U : Set X).Nonempty ∧ IsIso (p ∣_ U) ∧
        ∃ A : CartierDivisor Y, CartierIsAmpleProj K A := by
  obtain ⟨Y, p, U, hp, hsurj, hproj, hU, hiso, hY⟩ :=
    exists_isHProjective_of_isProper (X ↘ Spec (CommRingCat.of K))
  let := hp
  let := hsurj
  let := hY
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsHProjective (Y ↘ Spec (CommRingCat.of K)) := hproj
  exact ⟨Y, inferInstance, inferInstance, p, inferInstance, hp, hsurj, U, hU, hiso,
    proper_isQuasiProjective_exists_ample_cartier K⟩


/-- An actual isomorphism over any nonempty target open proves bijectivity
of the actual function-field map, without a birationality witness input. -/
theorem dominantFunctionFieldMap_bijective_of_isIso_nonempty_restrict
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsDominant p] (U : X.Opens) (hU : (U : Set X).Nonempty)
    [IsIso (p ∣_ U)] : Function.Bijective (dominantFunctionFieldMap p).hom := by
  let : Nonempty U := Set.nonempty_coe_sort.mpr hU
  have hpU : p (genericPoint Y) ∈ U := by
    rw [dominant_map_genericPoint p]
    exact Scheme.genericPoint_mem U
  let y : (p ⁻¹ᵁ U).toScheme := ⟨genericPoint Y, hpU⟩
  have h : IsIso (((p ∣_ U) ≫ U.ι).stalkMap y) := by infer_instance
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at h
  let : IsIso (p.stalkMap (genericPoint Y) ≫ (p ⁻¹ᵁ U).ι.stalkMap y) := h
  have hs : IsIso (p.stalkMap (genericPoint Y)) :=
    IsIso.of_isIso_comp_right _ ((p ⁻¹ᵁ U).ι.stalkMap y)
  exact dominantFunctionFieldMap_bijective_of_isIso_stalkMap p hs

end MixedFujita

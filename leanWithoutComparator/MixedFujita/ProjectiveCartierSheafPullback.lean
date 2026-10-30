/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierEquationFrameGenerator
public import MixedFujita.ModuleNonemptyCoverInjection
public import MixedFujita.ProjectivePullbackCartier
public import MixedFujita.CartierNegativeGradedPullback

/-!
The actual sheaf of a homogeneous Cartier divisor commutes with pullback
between integral sources when the equation avoids both generic images.
No dominance or flatness of the map is required. The pulled negative
inclusion is proved monic and has exactly the target equation ideal.
Canonical ideal presentations give the negative sheaf isomorphism;
Cartier tensor cancellation gives the positive one.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {n : ℕ} {R : Type u} [CommRing R] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (e : X ⟶ polynomialProjectiveScheme n R) (φ : Y ⟶ X)
  (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
  (hX : f ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (hY : f ∉ ((φ ≫ e) (genericPoint Y)).asHomogeneousIdeal)

noncomputable def projectivePullbackSourceCoordinateIndex
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (φ ≫ e) k)}) :
    {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
  ⟨j.val, ⟨⟨φ (Classical.choice j.property).val, (Classical.choice j.property).property⟩⟩⟩

omit [IsIntegral X] [IsIntegral Y] in
theorem projectivePullbackHomogeneousEquation_comp (k : Fin n) :
    φ.app (projectivePullbackCoordinateOpen e k)
        (projectivePullbackHomogeneousEquation e k d f hf) =
      projectivePullbackHomogeneousEquation (φ ≫ e) k d f hf := rfl

local notation "Ds" => projectivePullbackHomogeneousCartier e d f hf hd hX
local notation "Dt" => projectivePullbackHomogeneousCartier (φ ≫ e) d f hf hd hY

noncomputable def projectiveCartierNegativePullbackMap :
    (Scheme.Modules.pullback φ).obj (-Ds).sheaf ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  modulePullbackCoefficientHom φ
    (negativeCartierToUnit X Ds (projectivePullbackHomogeneousCartier_isEffective e d f hf hd hX))

noncomputable def projectiveCartierSourceEquationFrame
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (φ ≫ e) k)}) :
    (-Ds).sheaf.restrict (projectivePullbackCoordinateOpen e j.val).ι ≅
      SheafOfModules.unit (projectivePullbackCoordinateOpen e j.val : Scheme).ringCatSheaf := by
  let : Nonempty (projectivePullbackCoordinateOpen e j.val) :=
    (projectivePullbackSourceCoordinateIndex e φ j).property
  exact negativeCartierRegularEquationFrame Ds _
    (projectivePullbackHomogeneousEquation e j.val d f hf)
    (projectivePullbackHomogeneousEquation_ne_zero e j.val d f hf hd hX)
    (projectivePullbackHomogeneousCartier_restrict e d f hf hd hX
      (projectivePullbackSourceCoordinateIndex e φ j)).symm

omit [IsIntegral Y] in
theorem projectiveCartierSourceEquationFrameGenerator_image
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (φ ≫ e) k)}) :
    Scheme.Modules.Hom.app
        (negativeCartierToUnit X Ds (projectivePullbackHomogeneousCartier_isEffective e d f hf hd hX))
        (projectivePullbackCoordinateOpen e j.val)
        (moduleOpenFrameGenerator (-Ds).sheaf _
          (projectiveCartierSourceEquationFrame e φ d f hf hd hX j)) =
      projectivePullbackHomogeneousEquation e j.val d f hf := by
  let : Nonempty (projectivePullbackCoordinateOpen e j.val) :=
    (projectivePullbackSourceCoordinateIndex e φ j).property
  exact negativeCartierRegularEquationFrameGenerator_image Ds
    (projectivePullbackHomogeneousCartier_isEffective e d f hf hd hX)
    (projectivePullbackCoordinateOpen e j.val)
    (projectivePullbackHomogeneousEquation e j.val d f hf)
    (projectivePullbackHomogeneousEquation_ne_zero e j.val d f hf hd hX)
    (projectivePullbackHomogeneousCartier_restrict e d f hf hd hX
      (projectivePullbackSourceCoordinateIndex e φ j)).symm

omit [IsIntegral Y] in
theorem projectiveCartierNegativePullbackMap_local_formula
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen (φ ≫ e) k)})
    (W : Y.Opens) (hW : W ≤ projectivePullbackCoordinateOpen (φ ≫ e) j.val)
    (s : Γ((Scheme.Modules.pullback φ).obj (-Ds).sheaf, W)) :
    Scheme.Modules.Hom.app (projectiveCartierNegativePullbackMap e φ d f hf hd hX) W s =
      moduleOverFrameCoefficient ((Scheme.Modules.pullback φ).obj (-Ds).sheaf)
        (φ ⁻¹ᵁ projectivePullbackCoordinateOpen e j.val)
        (modulePulledOpenFrame φ (-Ds).sheaf _
          (projectiveCartierSourceEquationFrame e φ d f hf hd hX j)) W hW s *
        Y.presheaf.map (homOfLE hW).op
          (projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf) := by
  have h := modulePullbackStructureHom_local_formula φ (-Ds).sheaf
    (negativeCartierToUnit X Ds (projectivePullbackHomogeneousCartier_isEffective e d f hf hd hX))
    _ (projectiveCartierSourceEquationFrame e φ d f hf hd hX j) W hW s
  rw [projectiveCartierSourceEquationFrameGenerator_image,
    projectivePullbackHomogeneousEquation_comp] at h
  exact h

include hY in
theorem projectiveCartierNegativePullbackMap_mono :
    Mono (projectiveCartierNegativePullbackMap e φ d f hf hd hX) := by
  apply moduleHom_mono_of_nonempty_cover (projectivePullbackNonemptyCoordinateOpen (φ ≫ e))
    (projectivePullbackNonemptyCoordinateOpen_cover (φ ≫ e))
  intro j W _ hW s t hst
  have ha := projectivePullbackHomogeneousEquation_ne_zero (φ ≫ e) j.val d f hf hd hY
  have hr : Y.presheaf.map (homOfLE hW).op
      (projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf) ≠ 0 := by
    intro hz
    exact ha (map_injective_of_isIntegral Y (homOfLE hW) (hz.trans (map_zero _).symm))
  rw [projectiveCartierNegativePullbackMap_local_formula e φ d f hf hd hX j W hW s,
    projectiveCartierNegativePullbackMap_local_formula e φ d f hf hd hX j W hW t] at hst
  exact (moduleOverFrameCoefficient _ _ _ W hW).injective (mul_right_cancel₀ hr hst)

noncomputable def projectiveCartierNegativePullbackImageIdeal : Y.IdealSheafData :=
  invertibleModuleImageIdealSheaf ((Scheme.Modules.pullback φ).obj (-Ds).sheaf)
    (cartierPullbackSheaf_isInvertible (-Ds) φ)
    (projectiveCartierNegativePullbackMap e φ d f hf hd hX)

variable [IsAffineHom e] [IsAffineHom φ]

theorem projectiveCartierNegativePullbackImageIdeal_eq :
    projectiveCartierNegativePullbackImageIdeal e φ d f hf hd hX =
      projectivePullbackCartierIdealSheaf (φ ≫ e) d f hf hd hY := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (projectivePullbackNonemptyCoordinateAffineOpen (φ ≫ e))
    (projectivePullbackNonemptyCoordinateOpen_cover (φ ≫ e))
  intro j
  rw [projectivePullbackCartierIdealSheaf_coordinate_ideal]
  change moduleStructureImageIdeal (projectiveCartierNegativePullbackMap e φ d f hf hd hX)
    (projectivePullbackCoordinateOpen (φ ≫ e) j.val) = _
  have h := modulePullbackStructureHom_local_image φ (-Ds).sheaf
    (negativeCartierToUnit X Ds (projectivePullbackHomogeneousCartier_isEffective e d f hf hd hX))
    _ (projectiveCartierSourceEquationFrame e φ d f hf hd hX j)
    (projectivePullbackCoordinateOpen (φ ≫ e) j.val) le_rfl
  rw [projectiveCartierSourceEquationFrameGenerator_image,
    projectivePullbackHomogeneousEquation_comp] at h
  change moduleStructureImageIdeal (projectiveCartierNegativePullbackMap e φ d f hf hd hX)
      (projectivePullbackCoordinateOpen (φ ≫ e) j.val) =
    Ideal.span ({(Y.presheaf.map (𝟙 (op (projectivePullbackCoordinateOpen (φ ≫ e) j.val)))
      (projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf))} :
        Set Γ(Y, projectivePullbackCoordinateOpen (φ ≫ e) j.val)) at h
  have hi := ConcreteCategory.congr_hom
    (Y.presheaf.map_id (op (projectivePullbackCoordinateOpen (φ ≫ e) j.val)))
    (projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf)
  change Y.presheaf.map (𝟙 (op (projectivePullbackCoordinateOpen (φ ≫ e) j.val)))
    (projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf) =
      projectivePullbackHomogeneousEquation (φ ≫ e) j.val d f hf at hi
  rw [hi] at h
  exact h

noncomputable def projectiveCartierNegativePullbackIdealPresentation :
    InvertibleIdealPresentation (projectivePullbackCartierIdealSheaf (φ ≫ e) d f hf hd hY) where
  moduleSheaf := (Scheme.Modules.pullback φ).obj (-Ds).sheaf
  invertible := cartierPullbackSheaf_isInvertible (-Ds) φ
  inclusion := projectiveCartierNegativePullbackMap e φ d f hf hd hX
  injective U := by
    change Function.Injective ((moduleOpenEvaluation Y U).map
      (projectiveCartierNegativePullbackMap e φ d f hf hd hX))
    have := projectiveCartierNegativePullbackMap_mono e φ d f hf hd hX hY
    exact (ModuleCat.mono_iff_injective _).mp ((moduleOpenEvaluation Y U).map_mono
      (projectiveCartierNegativePullbackMap e φ d f hf hd hX))
  image_eq U := by
    rw [← projectiveCartierNegativePullbackImageIdeal_eq e φ d f hf hd hX hY]
    rfl

noncomputable def projectiveHomogeneousCartierNegativePullbackIso :
    (Scheme.Modules.pullback φ).obj (-Ds).sheaf ≅ (-Dt).sheaf :=
  invertibleIdealPresentationCanonicalIso
    (projectiveCartierNegativePullbackIdealPresentation e φ d f hf hd hX hY) ≪≫
      (effectiveCartierIdealModuleIso Dt
        (projectivePullbackHomogeneousCartier_isEffective (φ ≫ e) d f hf hd hY)).symm

noncomputable def projectiveHomogeneousCartierPullbackIso :
    (Scheme.Modules.pullback φ).obj (Ds).sheaf ≅ (Dt).sheaf := by
  simpa only [neg_neg] using cartierPullbackNegativeIso (-Ds) φ (-Dt)
    (projectiveHomogeneousCartierNegativePullbackIso e φ d f hf hd hX hY)

end MixedFujita

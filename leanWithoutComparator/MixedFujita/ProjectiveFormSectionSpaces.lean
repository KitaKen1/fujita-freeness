/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneSections
public import MixedFujita.ProjectiveBaseConstants
public import MixedFujita.CartierGradedSections
public import MixedFujita.GradedLinearSystem

/-!
The image of forms in the actual section spaces of D·J. For a morphism over the base
field, the actual section of a degree-D form is linear in the form, it vanishes exactly
for the forms vanishing at the generic point, and sections of forms multiply as the
forms do. Hence the image of the degree-D forms is a finite-dimensional subspace of
dimension dim S_D - dim (P ∩ S_D), with P the homogeneous ideal of the generic point,
and these subspaces form a graded family closed under the actual products.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K)

omit [IsIntegral Y] in
theorem projectivePullbackHomogeneousEquation_eq_affine (k : Fin n) (D : ℕ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) :
    projectivePullbackHomogeneousEquation e k D F hF =
      projectivePullbackAffinePolynomialMap e k (projectiveDehomogenize K k F) :=
  (projectivePullbackAffinePolynomialMap_dehomogenize e k D F hF).symm

omit [IsIntegral Y] in
theorem projectivePullbackHomogeneousEquation_X_mul (k : Fin n) (D : ℕ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) :
    projectivePullbackHomogeneousEquation e k (D + 1) (MvPolynomial.X k * F)
        (by simpa [add_comm] using (MvPolynomial.isHomogeneous_X K k).mul hF) =
      projectivePullbackHomogeneousEquation e k D F hF := by
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectivePullbackHomogeneousEquation_eq_affine,
    map_mul, projectiveDehomogenize_X_self, one_mul]

/-- A pulled-back chart equation vanishes exactly when the form vanishes at the generic point. -/
theorem projectivePullbackHomogeneousEquation_eq_zero_iff (k : Fin n)
    [Nonempty (projectivePullbackCoordinateOpen e k)] (D : ℕ)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) :
    projectivePullbackHomogeneousEquation e k D F hF = 0 ↔
      F ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
  have hXF : (MvPolynomial.X k * F).IsHomogeneous (D + 1) := by
    simpa [add_comm] using (MvPolynomial.isHomogeneous_X K k).mul hF
  have hξ : genericPoint Y ∈ projectivePullbackCoordinateOpen e k :=
    integral_genericPoint_mem_nonempty_open _
  have hXk : MvPolynomial.X k ∉ (e (genericPoint Y)).asHomogeneousIdeal := hξ
  have hmem : F ∈ (e (genericPoint Y)).asHomogeneousIdeal ↔
      MvPolynomial.X k * F ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
    constructor
    · intro h
      exact Ideal.mul_mem_left _ _ h
    · intro h
      exact ((e (genericPoint Y)).isPrime.mem_or_mem h).resolve_left hXk
  rw [← projectivePullbackHomogeneousEquation_X_mul e k D F hF, hmem]
  constructor
  · intro h0
    by_contra hn
    exact projectivePullbackHomogeneousEquation_ne_zero e k (D + 1) _ hXF (Nat.succ_pos D) hn h0
  · intro h
    have hb := projectivePullbackHomogeneousEquation_basicOpen e k (D + 1) _ hXF (Nat.succ_pos D)
    have hnot : genericPoint Y ∉ Y.basicOpen
        (projectivePullbackHomogeneousEquation e k (D + 1) _ hXF) := by
      rw [hb]
      exact fun h' => h'.2 h
    have hgerm : Y.presheaf.germ _ (genericPoint Y) hξ
        (projectivePullbackHomogeneousEquation e k (D + 1) _ hXF) = 0 := by
      by_contra hne
      exact hnot ((Y.mem_basicOpen _ (genericPoint Y) hξ).mpr
        ((isUnit_iff_ne_zero (G₀ := Y.functionField)).mpr hne))
    exact germ_injective_of_isIntegral Y (genericPoint Y) hξ (by simpa using hgerm)

variable (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
  (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})

theorem projectiveFormRatio_add (D : ℕ) (F G : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D)
    (hG : G.IsHomogeneous D) :
    projectiveFormRatio e g hg hggen j D (F + G) (hF.add hG) =
      projectiveFormRatio e g hg hggen j D F hF + projectiveFormRatio e g hg hggen j D G hG := by
  unfold projectiveFormRatio
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectivePullbackHomogeneousEquation_eq_affine,
    projectivePullbackHomogeneousEquation_eq_affine, map_add, map_add, map_add, add_mul]

theorem projectiveFormRatio_mul (D D' : ℕ) (F G : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D)
    (hG : G.IsHomogeneous D') :
    projectiveFormRatio e g hg hggen j (D + D') (F * G) (hF.mul hG) =
      projectiveFormRatio e g hg hggen j D F hF * projectiveFormRatio e g hg hggen j D' G hG := by
  unfold projectiveFormRatio
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectivePullbackHomogeneousEquation_eq_affine,
    projectivePullbackHomogeneousEquation_eq_affine, map_mul, map_mul, map_mul, pow_add,
    Units.val_mul]
  ring

theorem projectiveFormRatio_eq_zero_iff (D : ℕ) (F : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous D) :
    projectiveFormRatio e g hg hggen j D F hF = 0 ↔ F ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
  unfold projectiveFormRatio
  rw [mul_eq_zero, or_iff_left (Units.ne_zero _), map_eq_zero_iff _
    (Y.germToFunctionField_injective _), projectivePullbackHomogeneousEquation_eq_zero_iff]

section Base

variable [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

theorem projectiveFormRatio_smul
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ) (c : K)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D) :
    projectiveFormRatio e g hg hggen j D (c • F)
        (Submodule.smul_mem (MvPolynomial.homogeneousSubmodule (Fin n) K D) c hF) =
      (algebraMap K Γ(Y, ⊤) c) • projectiveFormRatio e g hg hggen j D F hF := by
  unfold projectiveFormRatio
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectivePullbackHomogeneousEquation_eq_affine,
    MvPolynomial.smul_eq_C_mul, map_mul, projectiveDehomogenize_C, map_mul,
    projectivePullbackAffinePolynomialMap_C e he, map_mul, germToFunctionField_restrict, Algebra.smul_def,
    mul_assoc]
  rfl

/-- The actual sections of degree-D forms, as a base-field linear map. -/
noncomputable def projectiveFormSectionLinear
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin n) K D →ₗ[K]
      Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) where
  toFun F := projectiveFormSection e g hg hggen j D F.1 F.2
  map_add' F G := by
    apply cartierSectionRational_injective
    rw [map_add]
    simp only [Submodule.coe_add, projectiveFormSection_rational]
    exact projectiveFormRatio_add e g hg hggen j D F.1 G.1 F.2 G.2
  map_smul' c F := by
    apply cartierSectionRational_injective
    change cartierSectionRational _ (projectiveFormSection e g hg hggen j D (c • F.1) _) =
      cartierSectionRational _ ((algebraMap K Γ(Y, ⊤) c) • projectiveFormSection e g hg hggen j D F.1 F.2)
    rw [map_smul, projectiveFormSection_rational, projectiveFormSection_rational]
    exact projectiveFormRatio_smul e g hg hggen j he D c F.1 F.2

theorem projectiveFormSectionLinear_apply
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ)
    (F : MvPolynomial.homogeneousSubmodule (Fin n) K D) :
    projectiveFormSectionLinear e g hg hggen j he D F =
      projectiveFormSection e g hg hggen j D F.1 F.2 := rfl

theorem projectiveFormSectionLinear_eq_zero_iff
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ)
    (F : MvPolynomial.homogeneousSubmodule (Fin n) K D) :
    projectiveFormSectionLinear e g hg hggen j he D F = 0 ↔
      (F : MvPolynomial (Fin n) K) ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
  rw [projectiveFormSectionLinear_apply, ← projectiveFormRatio_eq_zero_iff e g hg hggen j D F.1 F.2,
    ← projectiveFormSection_rational]
  exact (map_eq_zero_iff _ (cartierSectionRational_injective _)).symm

/-- The image of the degree-D forms in the actual sections of D·J. -/
noncomputable def projectiveFormSectionSpace
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ) :
    Submodule K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
  LinearMap.range (projectiveFormSectionLinear e g hg hggen j he D)

instance projectiveFormSectionSpace_finiteDimensional
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ) :
    FiniteDimensional K (projectiveFormSectionSpace e g hg hggen j he D) :=
  LinearMap.finiteDimensional_range _

/-- dim of the image = dim S_D - dim (P ∩ S_D). -/
theorem projectiveFormSectionSpace_finrank
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D : ℕ) :
    Module.finrank K (projectiveFormSectionSpace e g hg hggen j he D) =
      Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin n) K D) -
        Module.finrank K ↥((e (genericPoint Y)).asHomogeneousIdeal.toIdeal.restrictScalars K ⊓
          MvPolynomial.homogeneousSubmodule (Fin n) K D) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (projectiveFormSectionLinear e g hg hggen j he D)
  have hker : LinearMap.ker (projectiveFormSectionLinear e g hg hggen j he D) =
      ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal.restrictScalars K ⊓
        MvPolynomial.homogeneousSubmodule (Fin n) K D).comap
          (MvPolynomial.homogeneousSubmodule (Fin n) K D).subtype := by
    ext F
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf, Submodule.coe_subtype,
      Submodule.restrictScalars_mem, SetLike.coe_mem, and_true]
    exact projectiveFormSectionLinear_eq_zero_iff e g hg hggen j he D F
  have hkerrank : Module.finrank K (LinearMap.ker (projectiveFormSectionLinear e g hg hggen j he D)) =
      Module.finrank K ↥((e (genericPoint Y)).asHomogeneousIdeal.toIdeal.restrictScalars K ⊓
        MvPolynomial.homogeneousSubmodule (Fin n) K D) := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_right)
  unfold projectiveFormSectionSpace
  omega

omit [Y.Over (Spec (CommRingCat.of K))] in
theorem projectiveFormSection_mul (D D' : ℕ) (F G : MvPolynomial (Fin n) K)
    (hF : F.IsHomogeneous D) (hG : G.IsHomogeneous D') :
    cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) D D'
        (projectiveFormSection e g hg hggen j D F hF) (projectiveFormSection e g hg hggen j D' G hG) =
      projectiveFormSection e g hg hggen j (D + D') (F * G) (hF.mul hG) := by
  apply cartierSectionRational_injective
  rw [cartierNsmulProduct_rational, projectiveFormSection_rational, projectiveFormSection_rational,
    projectiveFormSection_rational]
  exact (projectiveFormRatio_mul e g hg hggen j D D' F G hF hG).symm

theorem projectiveFormSectionSpace_mul_mem
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (D D' : ℕ)
    {s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)}
    {t : Γ((D' • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)}
    (hs : s ∈ projectiveFormSectionSpace e g hg hggen j he D)
    (ht : t ∈ projectiveFormSectionSpace e g hg hggen j he D') :
    cartierNsmulProduct (projectiveHyperplaneCartier e g hg hggen) D D' s t ∈
      projectiveFormSectionSpace e g hg hggen j he (D + D') := by
  obtain ⟨F, rfl⟩ := hs
  obtain ⟨G, rfl⟩ := ht
  refine ⟨⟨F.1 * G.1, F.2.mul G.2⟩, ?_⟩
  rw [projectiveFormSectionLinear_apply, projectiveFormSectionLinear_apply,
    projectiveFormSectionLinear_apply]
  exact (projectiveFormSection_mul e g hg hggen j D D' F.1 G.1 F.2 G.2).symm

end Base

end MixedFujita

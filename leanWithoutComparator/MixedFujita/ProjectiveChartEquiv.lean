/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartAlgebra

/-!
The inverse to chart dehomogenization sends an affine coordinate to X_i/X_k.
The two compositions are proved using the homogeneous-localization spanning
family, with no assumption of a domain or of a chosen homogeneous basis.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} (R : Type*) [CommRing R] (k : Fin n)

noncomputable def projectiveChartCoefficient :
    R →+* HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    (polynomialDegreeZeroEquiv n R).symm.toRingHom

noncomputable def projectiveChartCoordinate (i : Fin n) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) :=
  HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) 1
    (MvPolynomial.X i) (by simpa using MvPolynomial.isHomogeneous_X R i)

noncomputable def projectiveChartAffineToLocalization :
    MvPolynomial {j : Fin n // j ≠ k} R →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
        (MvPolynomial.X k) :=
  MvPolynomial.eval₂Hom (projectiveChartCoefficient R k)
    (fun i => projectiveChartCoordinate R k i.val)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveChartCoefficient_mk (r : R) :
    projectiveChartCoefficient R k r =
      HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) 0
        (MvPolynomial.C r) (by simp) := by
  apply HomogeneousLocalization.val_injective
  simp [projectiveChartCoefficient, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk,
    polynomialDegreeZeroEquiv_symm_coe]

theorem projectiveChartCoordinate_self : projectiveChartCoordinate R k k = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [projectiveChartCoordinate, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one]

set_option backward.isDefEq.respectTransparency false in
theorem projectiveChartLocalizationToAffine_coefficient (r : R) :
    projectiveChartLocalizationToAffine R k (projectiveChartCoefficient R k r) =
      MvPolynomial.C r := by
  rw [projectiveChartCoefficient_mk,
    projectiveChartLocalizationToAffine_mk R k 0 _ (MvPolynomial.isHomogeneous_C (Fin n) r),
    projectiveDehomogenize_C]

theorem projectiveChartLocalizationToAffine_coordinate (i : Fin n) :
    projectiveChartLocalizationToAffine R k (projectiveChartCoordinate R k i) =
      projectiveChartVariable R k i := by
  rw [projectiveChartCoordinate,
    projectiveChartLocalizationToAffine_mk R k 1 _ (MvPolynomial.isHomogeneous_X R i)]
  simp [projectiveDehomogenize]

theorem projectiveChartAffineToLocalization_variable (i : Fin n) :
    projectiveChartAffineToLocalization R k (projectiveChartVariable R k i) =
      projectiveChartCoordinate R k i := by
  by_cases h : i = k
  · subst i
    simp [projectiveChartVariable, projectiveChartCoordinate_self]
  · simp [projectiveChartVariable, h, projectiveChartAffineToLocalization]

theorem projectiveChartAffine_roundtrip
    (f : MvPolynomial {j : Fin n // j ≠ k} R) :
    projectiveChartLocalizationToAffine R k (projectiveChartAffineToLocalization R k f) = f := by
  have h : (projectiveChartLocalizationToAffine R k).comp
      (projectiveChartAffineToLocalization R k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [projectiveChartAffineToLocalization, projectiveChartLocalizationToAffine_coefficient]
    · intro i
      simp [projectiveChartAffineToLocalization, projectiveChartLocalizationToAffine_coordinate,
        projectiveChartVariable, i.property]
  exact RingHom.congr_fun h f

theorem projectiveCoordinateProduct_isHomogeneous (a : Fin n → ℕ) :
    (∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ a i).IsHomogeneous (∑ i, a i) := by
  apply MvPolynomial.IsHomogeneous.prod
  intro i hi
  simpa using (MvPolynomial.isHomogeneous_X R i).pow (a i)

theorem projectiveChartCoordinate_prod (a : Fin n → ℕ) :
    (∏ i, projectiveChartCoordinate R k i ^ a i) =
      HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) (∑ i, a i)
        (∏ i, (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ a i)
        (by simpa using projectiveCoordinateProduct_isHomogeneous R a) := by
  apply (show Function.Injective (algebraMap _ (Localization.Away
    (MvPolynomial.X k : MvPolynomial (Fin n) R))) from HomogeneousLocalization.val_injective _)
  simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply,
    projectiveChartCoordinate, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_prod]
  congr 1
  apply Subtype.ext
  simp [Finset.prod_pow_eq_pow_sum]

theorem projectiveChartLocalization_roundtrip
    (x : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) :
    projectiveChartAffineToLocalization R k (projectiveChartLocalizationToAffine R k x) = x := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) R
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top (𝒜 := 𝒜)
    (MvPolynomial.isHomogeneous_X R k) (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)
    (polynomial_adjoin_variables_degreeZero n R) (fun _ => 1)
    (fun i => MvPolynomial.isHomogeneous_X R i)
  have hx : x ∈ (⊤ : Submodule (𝒜 0) (HomogeneousLocalization.Away 𝒜
      (MvPolynomial.X k))) := trivial
  rw [← hspan] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, a, ha, rfl⟩ := hz
    have had : ∑ i, a i = d := by simpa using ha
    rw [projectiveChartLocalizationToAffine_mk R k d _
      (by simpa [← had] using projectiveCoordinateProduct_isHomogeneous R a)]
    simp only [map_prod, map_pow]
    have hvar : ∀ i : Fin n,
        projectiveChartAffineToLocalization R k
          (projectiveDehomogenize R k (MvPolynomial.X i)) = projectiveChartCoordinate R k i := by
      intro i
      simpa [projectiveDehomogenize] using projectiveChartAffineToLocalization_variable R k i
    simp only [hvar]
    rw [projectiveChartCoordinate_prod]
    subst d
    rfl
  | zero => simp
  | add x y hx hy hx' hy' => simp [map_add, hx', hy']
  | smul r x hx hx' =>
    rw [Algebra.smul_def, map_mul, map_mul, hx']
    congr 1
    have hr : algebraMap (𝒜 0) (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X k)) r =
        projectiveChartCoefficient R k (polynomialDegreeZeroEquiv n R r) := by
      change (HomogeneousLocalization.fromZeroRingHom _ _) r =
        (HomogeneousLocalization.fromZeroRingHom _ _) _
      exact congrArg _ ((polynomialDegreeZeroEquiv n R).symm_apply_apply r).symm
    rw [hr, projectiveChartLocalizationToAffine_coefficient]
    simp [projectiveChartAffineToLocalization]

noncomputable def projectiveChartRingEquiv :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) ≃+* MvPolynomial {j : Fin n // j ≠ k} R :=
  { projectiveChartLocalizationToAffine R k with
    invFun := projectiveChartAffineToLocalization R k
    left_inv := projectiveChartLocalization_roundtrip R k
    right_inv := projectiveChartAffine_roundtrip R k }

end MixedFujita

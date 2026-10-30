/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSubschemeFibers

/-!
Invertible diagonal coordinate transformations preserve each standard chart.
Their actual global Proj maps pull back the generated ideal sheaves with
all multiplicities preserved. This supplies the nonzero parameter fibers;
it does not assert flatness or log canonical threshold semicontinuity.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {K : Type u} [Field K]

theorem polynomialDiagonal_coordinate_cancel (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) :
    (MvPolynomial.X k : MvPolynomial (Fin n) K) =
      polynomialDiagonalGradedHom w t (MvPolynomial.X k) * MvPolynomial.C ((t⁻¹) ^ w k) := by
  change MvPolynomial.X k =
    polynomialDiagonalHom w t (MvPolynomial.X k) * MvPolynomial.C ((t⁻¹) ^ w k)
  simp only [polynomialDiagonalHom, MvPolynomial.eval₂Hom_X']
  rw [mul_right_comm, ← MvPolynomial.C_mul, ← mul_pow]
  simp [ht]

noncomputable def projectiveChartDiagonalMap (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (MvPolynomial.X k) →+*
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (MvPolynomial.X k) :=
  (HomogeneousLocalization.awayMap (e := (0 : ℕ)) _
    (by simp)
    (polynomialDiagonal_coordinate_cancel w ht k)).comp
      (HomogeneousLocalization.Away.map (polynomialDiagonalGradedHom w t) (MvPolynomial.X k))

theorem projectiveChartDiagonalMap_mk (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    projectiveChartDiagonalMap w ht k
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K k) d f
        (by simpa using hf)) =
      projectiveChartCoefficient K k (((t⁻¹) ^ w k) ^ d) *
        HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K k) d
          (polynomialDiagonalHom w t f)
          (by simpa using polynomialDiagonalHom_isHomogeneous w t hf) := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveChartDiagonalMap, RingHom.comp_apply,
    HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk, projectiveChartCoefficient_mk,
    HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_zero, ← map_pow]
  change MvPolynomial.X k ^ d *
    (polynomialDiagonalHom w t f * MvPolynomial.C (((t⁻¹) ^ w k) ^ d)) =
      MvPolynomial.X k ^ d *
        (MvPolynomial.C (((t⁻¹) ^ w k) ^ d) * polynomialDiagonalHom w t f)
  ring

noncomputable def projectiveChartDiagonalSchemeMap (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) :
    polynomialProjectiveCoordinateChart n K k ⟶ polynomialProjectiveCoordinateChart n K k :=
  (polynomialProjectiveCoordinateChartIso n K k).hom ≫
    Spec.map (CommRingCat.ofHom (projectiveChartDiagonalMap w ht k)) ≫
      (polynomialProjectiveCoordinateChartIso n K k).inv

theorem projectiveChartDiagonalSchemeMap_global_commutes (w : Fin n → ℕ) {t : K}
    (ht : t ≠ 0) (k : Fin n) :
    projectiveChartDiagonalSchemeMap w ht k ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)).ι =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)).ι ≫
        polynomialDiagonalProjectiveMap w ht := by
  apply (cancel_epi (polynomialProjectiveCoordinateChartIso n K k).inv).mp
  simp only [projectiveChartDiagonalSchemeMap, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]
  change Spec.map (CommRingCat.ofHom (projectiveChartDiagonalMap w ht k)) ≫
      Proj.awayι _ _ (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one =
    Proj.awayι _ _ (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one ≫
      polynomialDiagonalProjectiveMap w ht
  let m := HomogeneousLocalization.awayMap (e := (0 : ℕ))
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (by simp)
    (polynomialDiagonal_coordinate_cancel w ht k)
  change Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (polynomialDiagonalGradedHom w t) (MvPolynomial.X k)) ≫
        CommRingCat.ofHom m) ≫
      Proj.awayι _ _ (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one =
    Proj.awayι _ _ (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one ≫
      Proj.map (polynomialDiagonalGradedHom w t)
        (graded_irrelevant_le_map_of_surjective _ (polynomialDiagonalGradedHom_surjective w ht))
  rw [Spec.map_comp, Category.assoc,
    ← Proj.awayι_comp_map (polynomialDiagonalGradedHom w t)
      (graded_irrelevant_le_map_of_surjective _ (polynomialDiagonalGradedHom_surjective w ht))
      Nat.zero_lt_one (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)]
  rw [← Category.assoc]
  exact congrArg (fun a => a ≫ polynomialDiagonalProjectiveMap w ht)
    (Proj.SpecMap_awayMap_awayι _
      ((polynomialDiagonalGradedHom w t).map_mem (MvPolynomial.isHomogeneous_X K k))
      Nat.zero_lt_one (by simp : MvPolynomial.C ((t⁻¹) ^ w k) ∈
        MvPolynomial.homogeneousSubmodule (Fin n) K 0)
      (polynomialDiagonal_coordinate_cancel w ht k))

theorem homogeneousProjectiveIdealSheaf_eq_of_span_eq {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (f : ι → MvPolynomial (Fin n) K)
    (g : κ → MvPolynomial (Fin n) K) (d e : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (hg : ∀ l ∈ J, (g l).IsHomogeneous e)
    (h : Ideal.span (Set.range (fun l : I => f l)) =
      Ideal.span (Set.range (fun l : J => g l))) :
    homogeneousProjectiveIdealSheaf I f d hf = homogeneousProjectiveIdealSheaf J g e hg := by
  apply homogeneousProjectiveIdealSheaf_unique
  intro k
  rw [homogeneousProjectiveIdealSheaf_restrict]
  congr 1
  apply projectiveChartIdealMap_injective K k
  rw [homogeneousChartLocalizationIdeal_affine, homogeneousChartLocalizationIdeal_affine, h]

theorem homogeneousChartLocalizationIdeal_diagonal {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (w : Fin n → ℕ) {t : K}
    (ht : t ≠ 0) (k : Fin n) :
    Ideal.map (projectiveChartDiagonalMap w ht k)
        (homogeneousChartLocalizationIdeal I f d hf k) =
      homogeneousChartLocalizationIdeal I (fun l => polynomialDiagonalHom w t (f l)) d
        (fun l hl => polynomialDiagonalHom_isHomogeneous w t (hf l hl)) k := by
  rw [homogeneousChartLocalizationIdeal, homogeneousChartLocalizationIdeal,
    Ideal.map_span, ← Set.range_comp']
  have heq : (fun l : I => projectiveChartDiagonalMap w ht k
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K k) d (f l)
        (by simpa using hf l l.property))) =
      (fun l : I => projectiveChartCoefficient K k (((t⁻¹) ^ w k) ^ d) *
        HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X K k) d
          (polynomialDiagonalHom w t (f l))
          (by simpa using polynomialDiagonalHom_isHomogeneous w t (hf l l.property))) := by
    funext l
    exact projectiveChartDiagonalMap_mk w ht k d (f l) (hf l l.property)
  rw [heq]
  apply ideal_span_range_unit_mul
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero ht)))).map
    (projectiveChartCoefficient K k)

theorem projectiveChartIdealSheaf_diagonal (w : Fin n → ℕ) {t : K}
    (ht : t ≠ 0) (k : Fin n)
    (J : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))) :
    (projectiveChartIdealSheaf K k J).comap (projectiveChartDiagonalSchemeMap w ht k) =
      projectiveChartIdealSheaf K k (J.map (projectiveChartDiagonalMap w ht k)) := by
  rw [projectiveChartIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  simp only [projectiveChartDiagonalSchemeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.IdealSheafData.comap_comp, specIdealSheaf_comap]
  rfl

theorem homogeneousProjectiveIdealSheaf_diagonal {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    (homogeneousProjectiveIdealSheaf I f d hf).comap (polynomialDiagonalProjectiveMap w ht) =
      homogeneousProjectiveIdealSheaf I (fun l => polynomialDiagonalHom w t (f l)) d
        (fun l hl => polynomialDiagonalHom_isHomogeneous w t (hf l hl)) := by
  apply homogeneousProjectiveIdealSheaf_unique
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartDiagonalSchemeMap_global_commutes w ht k,
    Scheme.IdealSheafData.comap_comp, homogeneousProjectiveIdealSheaf_restrict,
    projectiveChartIdealSheaf_diagonal, homogeneousChartLocalizationIdeal_diagonal]

theorem homogeneousParameterProjectiveIdealSheaf_nonzero {ι : Type u}
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    (homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
        (polynomialParameterProjectiveEval t) =
      (homogeneousProjectiveIdealSheaf I f d hf).comap
        (polynomialDiagonalProjectiveMap w ht) := by
  rw [homogeneousProjectiveIdealSheaf_diagonal]
  change (homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
    (polynomialScalarProjectiveMap (Polynomial.evalRingHom t)
      (fun c => ⟨Polynomial.C c, by simp⟩)) = _
  rw [homogeneousParameterProjectiveIdealSheaf, homogeneousProjectiveIdealSheaf_scalar]
  apply homogeneousProjectiveIdealSheaf_eq_of_span_eq
  rw [Set.range_comp', ← Ideal.map_span]
  change Ideal.map (MvPolynomial.map (Polynomial.evalRingHom t))
    (homogeneousParameterIdeal I w p f) = _
  rw [homogeneousParameterIdeal_nonzero_fiber I w p f ht hw, Ideal.map_span,
    ← Set.range_comp']

theorem projectiveChartDiagonalMap_coefficient (w : Fin n → ℕ) {t : K}
    (ht : t ≠ 0) (k : Fin n) :
    (projectiveChartDiagonalMap w ht k).comp (projectiveChartCoefficient K k) =
      projectiveChartCoefficient K k := by
  apply RingHom.ext
  intro r
  change projectiveChartDiagonalMap w ht k (projectiveChartCoefficient K k r) = _
  rw [projectiveChartCoefficient_mk,
    projectiveChartDiagonalMap_mk w ht k 0 _ (MvPolynomial.isHomogeneous_C (Fin n) r)]
  simp [polynomialDiagonalHom]

theorem polynomialDiagonalProjectiveMap_toBase (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    polynomialDiagonalProjectiveMap w ht ≫ polynomialProjectiveToBase n K =
      polynomialProjectiveToBase n K := by
  apply Scheme.Cover.hom_ext (polynomialProjectiveCoordinateOpenCover K)
  intro k
  change (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)).ι ≫
    (polynomialDiagonalProjectiveMap w ht ≫ polynomialProjectiveToBase n K) =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveToBase n K
  rw [← Category.assoc, ← projectiveChartDiagonalSchemeMap_global_commutes w ht k,
    Category.assoc, polynomialProjectiveCoordinateChart_toBase]
  simp only [projectiveChartDiagonalSchemeMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  congr 1
  exact congrArg Spec.map (congrArg CommRingCat.ofHom (projectiveChartDiagonalMap_coefficient w ht k))

theorem idealSheaf_comap_iso_subscheme {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ≅ Y) :
    ∃ e : (I.comap f.hom).subscheme ≅ I.subscheme,
      e.hom ≫ I.subschemeι = (I.comap f.hom).subschemeι ≫ f.hom := by
  let e := I.comapIso f.hom ≪≫ asIso (pullback.snd f.hom I.subschemeι)
  refine ⟨e, ?_⟩
  simp only [e, Iso.trans_hom, asIso_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_snd_assoc,
    Scheme.IdealSheafData.subschemeMap_subschemeι]

end MixedFujita

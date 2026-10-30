/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialPointBlowupTransform
public import MixedFujita.ProjectiveJetChartComparison
public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Exceptional

/-!
Connect polynomial strict transforms to the actual standard affine point-blow-up charts.
The exceptional ideal on each chart is (X_k), its actual coordinate quotient is the polynomial
ring in the other variables, and the strict transform in this quotient is the dehomogenized
leading form. Translation at every exceptional-chart point is a finite polynomial evaluation.
Transport from this standard model to an arbitrary smooth point is a separate comparison.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {n : ℕ} {K : Type u} [Field K]

theorem polynomialPointBlowupMap_eq_chartSubst (k : Fin n) :
    polynomialPointBlowupMap (K := K) k =
      affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n n) k := by
  unfold polynomialPointBlowupMap
  congr 1
  ext i
  simp [CoordinateSubspace.center]

theorem standardPointBlowup_chart_projection (k : Fin n) :
    CoordinateSubspace.modelChart K n n k k.isLt ≫
      affineBlowUp.π (CoordinateSubspace.centerIdeal K n n) =
      Spec.map (CommRingCat.ofHom (polynomialPointBlowupMap (K := K) k).toRingHom) := by
  rw [CoordinateSubspace.modelChart_π, polynomialPointBlowupMap_eq_chartSubst]

theorem standardPointBlowup_exceptional_ideal_chart (k : Fin n) :
    (affineBlowUp.exceptionalIdeal (CoordinateSubspace.centerIdeal K n n)).comap
      (CoordinateSubspace.modelChart K n n k k.isLt) =
      Scheme.IdealSheafData.ofIdealTop
        ((Ideal.span {(MvPolynomial.X k : MvPolynomial (Fin n) K)}).map
          (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) K))).inv.hom) :=
  CoordinateSubspace.comap_exceptionalIdeal_modelChart K n n k k.isLt

theorem pointBlowupExceptionalRestriction_coe (k : Fin n) (f : MvPolynomial (Fin n) K) :
    pointBlowupExceptionalRestriction k (f : MvPowerSeries (Fin n) K) =
      (CoordinateSubspace.killX K k f : MvPowerSeries {i : Fin n // i ≠ k} K) := by
  have hX (i : Fin n) : pointBlowupExceptionalRestriction (K := K) k (MvPowerSeries.X i) =
      (CoordinateSubspace.killX K k (MvPolynomial.X i) :
        MvPowerSeries {i : Fin n // i ≠ k} K) := by
    by_cases hi : i = k
    · subst i
      rw [CoordinateSubspace.killX_X_self, MvPolynomial.coe_zero]
      apply MvPowerSeries.killCompl_X_eq_zero
      rintro ⟨j, hj⟩
      exact j.property hj
    · rw [CoordinateSubspace.killX_X_of_ne K k hi, MvPolynomial.coe_X]
      exact MvPowerSeries.killCompl_X (e := ⟨Subtype.val, Subtype.val_injective⟩) ⟨i, hi⟩
  induction f using MvPolynomial.induction_on with
  | C c => simp [pointBlowupExceptionalRestriction, CoordinateSubspace.killX,
      CoordinateSubspace.killPred]
  | add f g hf hg => simp only [MvPolynomial.coe_add, map_add, hf, hg]
  | mul_X f i hf => simp only [MvPolynomial.coe_mul, map_mul, MvPolynomial.coe_X, hf, hX]

theorem polynomialPointBlowupStrictTransform_exceptional (k : Fin n) (m : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : (m : ℕ∞) ≤ (f : MvPowerSeries (Fin n) K).order) :
    CoordinateSubspace.killX K k (polynomialPointBlowupStrictTransform k m f) =
      projectiveDehomogenize K k (homogeneousTaylorForm m (f : MvPowerSeries (Fin n) K)) := by
  apply MvPolynomial.coe_injective {i : Fin n // i ≠ k} K
  rw [← pointBlowupExceptionalRestriction_coe, polynomialPointBlowupStrictTransform_coe k m f hf,
    pointBlowupExceptionalRestriction_strictTransform]

theorem standardPointBlowup_exceptional_quotient_mk (k : Fin n)
    (f : MvPolynomial (Fin n) K) :
    CoordinateSubspace.quotientSpanXAlgEquiv K k (Ideal.Quotient.mk _ f) =
      CoordinateSubspace.killX K k f := by
  change Ideal.quotientKerAlgEquivOfSurjective (CoordinateSubspace.killX_surjective K k)
    (Ideal.quotientEquivAlgOfEq K (CoordinateSubspace.ker_killX K k).symm
      (Ideal.Quotient.mk _ f)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (CoordinateSubspace.killX_surjective K k) f

theorem standardPointBlowup_strictTransform_exceptional_quotient (k : Fin n) (m : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : (m : ℕ∞) ≤ (f : MvPowerSeries (Fin n) K).order) :
    CoordinateSubspace.quotientSpanXAlgEquiv K k
      (Ideal.Quotient.mk _ (polynomialPointBlowupStrictTransform k m f)) =
      projectiveDehomogenize K k (homogeneousTaylorForm m (f : MvPowerSeries (Fin n) K)) := by
  rw [standardPointBlowup_exceptional_quotient_mk,
    polynomialPointBlowupStrictTransform_exceptional k m f hf]

theorem standardPointBlowup_strictTransform_exceptional_shift (k : Fin n) (m : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : (m : ℕ∞) ≤ (f : MvPowerSeries (Fin n) K).order)
    (p : {i : Fin n // i ≠ k} → K) :
    affinePolynomialTaylor p (CoordinateSubspace.killX K k
      (polynomialPointBlowupStrictTransform k m f)) =
      chartShiftedForm k p (homogeneousTaylorForm m (f : MvPowerSeries (Fin n) K)) := by
  rw [polynomialPointBlowupStrictTransform_exceptional k m f hf,
    affinePolynomialTaylor_projectiveDehomogenize]

end MixedFujita

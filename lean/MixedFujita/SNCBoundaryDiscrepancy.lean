/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryLocalProduct
public import MixedFujita.ProperBirationalSections

/-!
Constructed local boundary products give actual pullback coefficients on every dominant
model. For a smooth birational model, the actual discrepancy coefficient is d*ord(J)
minus the signed coordinate-value sum. This is an exact evaluation on genuine models,
not an identification assumed for a formal test valuation. The remaining geometric
Jacobian lower bound is explicitly distinguished from the integer arithmetic proved here.
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

section Pullback

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  (ρ : T ⟶ X) [IsDominant ρ]

/-- A regular actual stalk element has nonnegative prime order. -/
theorem scheme_ord_nonneg_of_mem_stalk (t : T) (f : T.functionField)
    (hf : f ∈ (algebraMap (T.presheaf.stalk t) T.functionField).range) :
    0 ≤ T.ord f t := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨U, hU, s, rfl⟩ := T.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨t, hU⟩⟩
  rw [← ha, Scheme.algebraMap_germ_eq_germToFunctionField]
  exact TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg s hU

/-- Every selected coordinate remains regular on a dominant model at a point over its chart. -/
theorem sncChartComponentEquation_pullback_ord_nonneg
    {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))] {n r : ℕ}
    (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (t : T)
    (hc : ρ t ∈ c.U) (i : Fin r) :
    0 ≤ T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) t := by
  cases hσ : σ i with
  | none =>
    simp only [sncChartComponentEquation, hσ, Option.elim_none, Units.val_one,
      map_one, TauCeti.AlgebraicGeometry.Scheme.ord_one, le_refl]
  | some a =>
    simp only [sncChartComponentEquation, hσ, Option.elim_some,
      etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
    rw [← X.algebraMap_germ_eq_germToFunctionField hc,
      dominantFunctionFieldMap_algebraMap]
    exact scheme_ord_nonneg_of_mem_stalk t _ ⟨_, rfl⟩

/-- A constructed local product computes the actual pulled-back Cartier coefficient. -/
theorem cartierPullback_coefficient_of_local_product {ι : Type*} [Fintype ι]
    (B : CartierDivisor X) (t : CodimensionOnePoint T) (f : X.functionFieldˣ)
    (hf : B.IsLocalEquationAt (ρ (t : T)) f) (u : (X.presheaf.stalk (ρ (t : T)))ˣ)
    (g : ι → X.functionFieldˣ) (b : ι → ℤ)
    (hprod : (f : X.functionField) =
      algebraMap (X.presheaf.stalk (ρ (t : T))) X.functionField u *
        (∏ i, g i ^ b i : X.functionFieldˣ)) :
    cartierCoefficient (cartierPullback ρ B) (t : T) =
      ∑ i, b i * T.ord ((dominantFunctionFieldMap ρ).hom (g i : X.functionField)) (t : T) := by
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ B (t : T) hf)]
  change T.ord ((dominantFunctionFieldMap ρ).hom (f : X.functionField)) (t : T) = _
  let v := Units.map (ρ.stalkMap (t : T)).hom.toMonoidHom u
  have hunit : T.ord ((dominantFunctionFieldMap ρ).hom
      (algebraMap (X.presheaf.stalk (ρ (t : T))) X.functionField u)) (t : T) = 0 := by
    rw [dominantFunctionFieldMap_algebraMap]
    exact scheme_ord_stalk_unit (t : T) v
  have hu0 : (dominantFunctionFieldMap ρ).hom
      (algebraMap (X.presheaf.stalk (ρ (t : T))) X.functionField u) ≠ 0 :=
    ((u.isUnit.map _).map _).ne_zero
  have hg0 : (dominantFunctionFieldMap ρ).hom
      ((∏ i, g i ^ b i : X.functionFieldˣ) : X.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  rw [hprod, map_mul, Scheme.ord_mul hu0 hg0, hunit, zero_add]
  have heq : (dominantFunctionFieldMap ρ).hom
      ((∏ i, g i ^ b i : X.functionFieldˣ) : X.functionField) =
        ((∏ i, (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (g i)) ^ b i :
          T.functionFieldˣ) : T.functionField) := by
    simp [map_prod]
  rw [heq, scheme_ord_prod_zpow]
  rfl

end Pullback

section SmoothModels

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Adding an actual Cartier boundary subtracts its pullback from the relative discrepancy. -/
theorem logDiscrepancyDivisor_boundary_add (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X) (c'₀ : EtaleChart K T n) :
    logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      c'₀ etaleCharts_cover =
        d • birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover c'₀
          etaleCharts_cover - cartierPullback ρ B := by
  have h := logDiscrepancyDivisor_boundary_zero ρ hρ c₀ f₀ d c'₀
  unfold logDiscrepancyDivisor at h ⊢
  rw [cartierPullback_add, sub_add_eq_sub_sub, h]

/-- For every smooth birational model and every prime divisor, ordinary SNC geometry
constructs charts giving the actual discrepancy formula, without a supplied local product. -/
theorem normal_isSNCFamily_actual_discrepancy_formula
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (_ : ρ (t : T) ∈ c.U),
      IsSNCChart c ξ σ ∧ ∀ (c' : EtaleChart K T n), (t : T) ∈ c'.U →
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T) =
            (d : ℤ) * T.ord (chartRelativeJacobianDet ρ c c') (t : T) -
              ∑ i, cartierCoefficient B (ξ i) *
                T.ord ((dominantFunctionFieldMap ρ).hom
                  (sncChartComponentEquation c σ i : X.functionField)) (t : T) := by
  obtain ⟨c, σ, hc, hsnc', f, hf, u, hu⟩ :=
    letI : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    normal_isSNCFamily_boundary_local_product hnorm B ξ hinj hξ hsnc hsupport (ρ (t : T))
  refine ⟨c, σ, hc, hsnc', fun c' hc' => ?_⟩
  rw [logDiscrepancyDivisor_boundary_add, cartierCoefficient_sub, cartierCoefficient_nsmul,
    cartierPullback_coefficient_of_local_product ρ B t f hf u _ _ hu]
  have hloc := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ etaleCharts_cover c'₀
    etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀)
    (t : T) c hc c' hc'
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord hloc, IsUnit.unit_spec]

end SmoothModels

/-- Integer coefficients below d yield a strict klt bound once the geometric SNC sum bound
is supplied. This arithmetic allows negative boundary coefficients. -/
theorem snc_integer_discrepancy_bound {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 1 ≤ d) (J : ℤ) (hJ : 0 ≤ J) (v b : ι → ℤ)
    (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i ≤ 1 + J) (hb : ∀ i, b i < (d : ℤ)) :
    1 + J ≤ (d : ℤ) * (1 + J) - ∑ i, b i * v i ∧
      -(d : ℤ) < (d : ℤ) * J - ∑ i, b i * v i := by
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hcoeff : ∑ i, b i * v i ≤ ((d : ℤ) - 1) * ∑ i, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by have := hb i; omega) (hv i)
  have hsum' := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (d : ℤ) - 1 by omega)
  constructor <;> nlinarith

section ConditionalBound

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- On an arbitrary actual smooth birational model, a geometric SNC sum bound gives the
strict discrepancy bound. Coordinate and Jacobian nonnegativity are derived from actual
regular germs. The geometric sum inequality remains an explicit, unproved prerequisite. -/
theorem normal_isSNCFamily_discrepancy_bound_of_jacobian_sum
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ))
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hsum : ∀ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)),
      ρ (t : T) ∈ c.U → IsSNCChart c ξ σ → ∀ (c' : EtaleChart K T n),
        (t : T) ∈ c'.U →
          ∑ i, T.ord ((dominantFunctionFieldMap ρ).hom
            (sncChartComponentEquation c σ i : X.functionField)) (t : T) ≤
              1 + T.ord (chartRelativeJacobianDet ρ c c') (t : T)) :
    -(d : ℤ) < cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      c'₀ etaleCharts_cover) (t : T) := by
  obtain ⟨c, σ, hc, hcsnc, hformula⟩ :=
    normal_isSNCFamily_actual_discrepancy_formula ρ hρ hnorm c₀ f₀ d B ξ hinj hξ hsnc
      hsupport c'₀ t
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (t : T))
  rw [hformula c' hc']
  have hJ : 0 ≤ T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
    rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
    exact scheme_ord_nonneg_of_mem_stalk (t : T) _ ⟨_, rfl⟩
  exact (snc_integer_discrepancy_bound d hd _ hJ _ _
    (fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c σ (t : T) hc i)
    (hsum c σ hc hcsnc c' hc') hb).2

end ConditionalBound

end MixedFujita

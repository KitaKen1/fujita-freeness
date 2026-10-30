/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogDifferentialForms
public import MixedFujita.LogEtaleCartier
public import MixedFujita.ExteriorDeRhamGradedLeibniz
public import MixedFujita.RelativeCanonicalDivisor

/-!
The twisted logarithmic coordinate model of an étale chart in the rational forms (step 10, R2).

On an étale chart `c` with coordinates `y_j` and logarithmic directions `A`, the logarithmic
generators are `θ_j = dy_j / y_j` (`j ∈ A`) and `θ_j = dy_j` (`j ∉ A`) (`logGenerator`). They are
closed (`rationalDeRhamDiff_ι_logGenerator`), so `e_j ↦ θ_j` is a `K`-algebra map from the
coordinate exterior algebra into the rational forms with closed values (`logExteriorMap`,
`rationalDeRhamDiff_logExteriorMap`). For a rational function `w`, the model map
`a ⊗ e ↦ (a w) θ_e` (`logChartModelMap`) sends the coordinate model `Γ(X, U) ⊗ ⋀Kⁿ` to the rational
forms.

If `∂_j w = −r_j w / y_j` for `j ∈ A` and `∂_j w = 0` otherwise (`w = g^{-p} y^{-r}` in
characteristic `p`, `etaleCoordPartial_logTwistWeight`), the model map intertwines the de Rham
differential of the rational forms with the differential of the twisted logarithmic model of
check 478, with operators `y_j ∂_j − r_j` (`j ∈ A`) and `∂_j` (`j ∉ A`)
(`rationalDeRhamDiff_logChartModelMap`): `dF = Σ_j ∂_j F · μ_j θ_j` with `μ_j = y_j` for `j ∈ A`
and `1` otherwise (`kaehlerD_eq_sum_logGenerator`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Model

variable (c : EtaleChart K X n) (A : Finset (Fin n))

/-- `d(f ω) = df ∧ ω + f dω` for the de Rham differential of the rational forms. -/
theorem rationalDeRhamDiff_smul (f : X.functionField)
    (ω : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :
    rationalDeRhamDiff c (f • ω) =
      ExteriorAlgebra.ι X.functionField (KaehlerDifferential.D K X.functionField f) * ω +
        f • rationalDeRhamDiff c ω :=
  kaehlerDeRhamDiff_smul _ _ f ω

theorem rationalDeRhamDiff_one :
    rationalDeRhamDiff c (1 : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) = 0 :=
  kaehlerDeRhamDiff_one _ _

theorem rationalDeRhamDiff_mul (x z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :
    rationalDeRhamDiff c (x * z) =
      rationalDeRhamDiff c x * z + exteriorInvolute K X.functionField x * rationalDeRhamDiff c z :=
  kaehlerDeRhamDiff_mul _ _ x z

/-- Exact `1`-forms are closed. -/
theorem rationalDeRhamDiff_ι_kaehlerD (g : X.functionField) :
    rationalDeRhamDiff c
      (ExteriorAlgebra.ι X.functionField (KaehlerDifferential.D K X.functionField g)) = 0 := by
  have h := kaehlerDeRhamDiff_exact_mul (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords_formallyEtale c) g 1
  rw [mul_one, kaehlerDeRhamDiff_one, mul_zero, neg_zero] at h
  exact h

/-- **The logarithmic generators of a chart**: `dy_j / y_j` for `j ∈ A`, `dy_j` otherwise. -/
noncomputable def logGenerator (j : Fin n) : Ω[X.functionField⁄K] :=
  if j ∈ A then rationalDlog K (etaleChartCoordinateRationalUnit c j)
  else KaehlerDifferential.D K X.functionField (etaleChartCoordinateRationalUnit c j : X.functionField)

/-- `dy_j = μ_j θ_j` with `μ_j = y_j` for `j ∈ A` and `μ_j = 1` otherwise. -/
theorem kaehlerD_coordinate_eq_smul_logGenerator (j : Fin n) :
    KaehlerDifferential.D K X.functionField (etaleChartCoordinateRationalUnit c j : X.functionField) =
      (if j ∈ A then (etaleChartCoordinateRationalUnit c j : X.functionField) else 1) •
        logGenerator c A j := by
  unfold logGenerator
  split_ifs with hj
  · rw [rationalDlog, smul_smul, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  · rw [one_smul]

/-- The logarithmic generators are closed. -/
theorem rationalDeRhamDiff_ι_logGenerator (j : Fin n) :
    rationalDeRhamDiff c (ExteriorAlgebra.ι X.functionField (logGenerator c A j)) = 0 := by
  unfold logGenerator
  split_ifs with hj
  · rw [rationalDlog, map_smul, rationalDeRhamDiff_smul, rationalDeRhamDiff_ι_kaehlerD, smul_zero,
      add_zero, Units.val_inv_eq_inv_val, Derivation.leibniz_inv, map_smul, smul_mul_assoc,
      ExteriorAlgebra.ι_sq_zero, smul_zero]
  · exact rationalDeRhamDiff_ι_kaehlerD c _

/-- **`e_j ↦ θ_j`**, a `K`-algebra map into the rational forms. -/
noncomputable def logExteriorMap :
    CoordExterior K n →ₐ[K] ExteriorAlgebra X.functionField Ω[X.functionField⁄K] :=
  ExteriorAlgebra.lift K ⟨((ExteriorAlgebra.ι X.functionField).restrictScalars K) ∘ₗ
      Fintype.linearCombination K (logGenerator c A), fun m => by
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    exact ExteriorAlgebra.ι_sq_zero _⟩

theorem logExteriorMap_coordVector (j : Fin n) :
    logExteriorMap c A (coordVector K j) =
      ExteriorAlgebra.ι X.functionField (logGenerator c A j) := by
  rw [logExteriorMap, coordVector, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Fintype.linearCombination_apply_single, one_smul]

/-- The values of `e ↦ θ_e` are closed. -/
theorem rationalDeRhamDiff_logExteriorMap (e : CoordExterior K n) :
    rationalDeRhamDiff c (logExteriorMap c A e) = 0 := by
  induction e using ExteriorAlgebra.induction with
  | algebraMap k =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.map_smul_of_tower,
      rationalDeRhamDiff_one, smul_zero]
  | ι v =>
    rw [logExteriorMap, ExteriorAlgebra.lift_ι_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Fintype.linearCombination_apply, map_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, rationalDeRhamDiff_ι_logGenerator,
      smul_zero]
  | mul x z hx hz =>
    rw [map_mul, rationalDeRhamDiff_mul, hx, hz, zero_mul, mul_zero, add_zero]
  | add x z hx hz =>
    rw [map_add, map_add, hx, hz, add_zero]

/-- **The twisted logarithmic model map** `a ⊗ e ↦ (a w) θ_e`. -/
noncomputable def logChartModelMap (w : X.functionField) :
    Γ(X, c.U) ⊗[K] CoordExterior K n →ₗ[K] ExteriorAlgebra X.functionField Ω[X.functionField⁄K] :=
  TensorProduct.lift (LinearMap.mk₂ K
    (fun (a : Γ(X, c.U)) (e : CoordExterior K n) =>
      (sectionGermAlgHom (K := K) c.U a * w) • logExteriorMap c A e)
    (fun a a' e => by rw [map_add, add_mul, add_smul])
    (fun k a e => by rw [map_smul, smul_mul_assoc, smul_assoc])
    (fun a e e' => by rw [map_add, smul_add])
    (fun (k : K) (a : Γ(X, c.U)) (e : CoordExterior K n) => by
      rw [(logExteriorMap c A).map_smul_of_tower]
      exact smul_comm _ _ _))

theorem logChartModelMap_tmul (w : X.functionField) (a : Γ(X, c.U)) (e : CoordExterior K n) :
    logChartModelMap c A w (a ⊗ₜ e) = (sectionGermAlgHom (K := K) c.U a * w) • logExteriorMap c A e := by
  rw [logChartModelMap, TensorProduct.lift.tmul]
  rfl

/-- **The differential of a rational function in the logarithmic generators**:
`dF = Σ_j ∂_j F · μ_j θ_j`. -/
theorem kaehlerD_eq_sum_logGenerator (F : X.functionField) :
    KaehlerDifferential.D K X.functionField F =
      ∑ j, (etaleCoordPartial (etaleChartFunctionFieldCoords c)
          (etaleChartFunctionFieldCoords_formallyEtale c) j F *
        (if j ∈ A then (etaleChartCoordinateRationalUnit c j : X.functionField) else 1)) •
          logGenerator c A j := by
  conv_lhs => rw [← (etaleChartBasis c).sum_repr (KaehlerDifferential.D K X.functionField F)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [etaleChartBasis_apply_eq, kaehlerD_coordinate_eq_smul_logGenerator c A j, smul_smul]
  rfl

/-- The coordinate derivations of `K(X)` restrict to those of the chart. -/
theorem etaleCoordPartial_functionField_germ (j : Fin n) (a : Γ(X, c.U)) :
    etaleCoordPartial (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
        j (sectionGermAlgHom (K := K) c.U a) =
      sectionGermAlgHom (K := K) c.U (etaleCoordPartial c.coords c.formallyEtale j a) :=
  etaleCoordinateDerivation_comp (sectionGermAlgHom c.U) c.coords c.formallyEtale
    (etaleChartFunctionFieldCoords_formallyEtale c) j a

theorem sectionGermAlgHom_etaleCoordFun (j : Fin n) :
    sectionGermAlgHom (K := K) c.U (etaleCoordFun c.coords j) =
      (etaleChartCoordinateRationalUnit c j : X.functionField) := rfl

/-- **The model map intertwines the differentials.** -/
theorem rationalDeRhamDiff_logChartModelMap (r : Fin n → ℕ) (w : X.functionField)
    (hw : ∀ j, etaleCoordPartial (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) j w =
      (if j ∈ A then -((r j : ℕ) : X.functionField) *
        ((etaleChartCoordinateRationalUnit c j : X.functionField))⁻¹ else 0) * w)
    (ω : Γ(X, c.U) ⊗[K] CoordExterior K n) :
    rationalDeRhamDiff c (logChartModelMap c A w ω) =
      logChartModelMap c A w (koszulDeRhamDiff (logTwistedPartial c.coords c.formallyEtale A r) ω) := by
  induction ω using TensorProduct.inductionOn with
  | tmul a e =>
    rw [logChartModelMap_tmul, rationalDeRhamDiff_smul, rationalDeRhamDiff_logExteriorMap, smul_zero,
      add_zero, koszulDeRhamDiff_tmul, map_sum, kaehlerD_eq_sum_logGenerator c A, map_sum,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [logChartModelMap_tmul, map_mul (logExteriorMap c A), logExteriorMap_coordVector,
      LinearMap.map_smul_of_tower, smul_mul_assoc]
    congr 1
    have hY := (etaleChartCoordinateRationalUnit c j).ne_zero
    rw [etaleCoordPartial_leibniz, etaleCoordPartial_functionField_germ, hw j]
    by_cases hj : j ∈ A
    · rw [logTwistedPartial_of_mem c.coords c.formallyEtale A r hj]
      simp only [hj, ite_true, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        eulerOperator_apply, map_sub, map_mul, map_smul, sectionGermAlgHom_etaleCoordFun]
      rw [Algebra.smul_def, map_natCast]
      field_simp
      ring
    · rw [logTwistedPartial_of_not_mem c.coords c.formallyEtale A r hj]
      simp only [hj, ite_false, zero_mul, mul_zero, add_zero, mul_one]
  | add ω ω' h h' => rw [map_add, map_add, h, h', map_add, map_add]

/-- The monomial `y^r = Π_{j ∈ A} y_j^{r_j}` of a chart. -/
noncomputable def logTwistMonomial (r : Fin n → ℕ) : X.functionFieldˣ :=
  ∏ j ∈ A, etaleChartCoordinateRationalUnit c j ^ r j

theorem etaleCoordPartial_functionField_coordinate (i j : Fin n) :
    etaleCoordPartial (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
        j (etaleChartCoordinateRationalUnit c i : X.functionField) = if i = j then 1 else 0 :=
  etaleCoordinateDerivation_coordinate _ _ i j

/-- **The logarithmic derivative of `y^r`**: `∂_j y^r = (r_j / y_j) y^r` for `j ∈ A`, `0` otherwise. -/
theorem etaleCoordPartial_logTwistMonomial (r : Fin n → ℕ) (j : Fin n) :
    etaleCoordPartial (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
        j (logTwistMonomial c A r : X.functionField) =
      (if j ∈ A then ((r j : ℕ) : X.functionField) *
        ((etaleChartCoordinateRationalUnit c j : X.functionField))⁻¹ else 0) *
        (logTwistMonomial c A r : X.functionField) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    simp only [logTwistMonomial, Finset.prod_empty, Units.val_one, Finset.notMem_empty, ite_false,
      zero_mul]
    exact Derivation.map_one_eq_zero _
  | insert a A' ha ih =>
    have hYa := (etaleChartCoordinateRationalUnit c a).ne_zero
    simp only [logTwistMonomial, Finset.prod_insert ha, Units.val_mul, Units.val_pow_eq_pow_val] at ih ⊢
    rw [etaleCoordPartial_leibniz, ih]
    change (etaleCoordinateDerivation _ _ j) _ * _ + _ = _
    rw [Derivation.leibniz_pow]
    change _ • _ • etaleCoordPartial (etaleChartFunctionFieldCoords c)
      (etaleChartFunctionFieldCoords_formallyEtale c) j _ * _ + _ = _
    rw [etaleCoordPartial_functionField_coordinate]
    by_cases hja : j = a
    · subst hja
      simp only [ite_true, Finset.mem_insert, true_or, ha, ite_false, zero_mul, mul_zero, add_zero,
        smul_eq_mul, nsmul_eq_mul, mul_one]
      rcases Nat.eq_zero_or_pos (r j) with h0 | hpos
      · rw [h0]
        simp
      · obtain ⟨q, hq⟩ : ∃ q, r j = q + 1 := ⟨r j - 1, by omega⟩
        rw [hq, Nat.add_sub_cancel, pow_succ]
        field_simp
    · have hmem : (j ∈ insert a A') ↔ j ∈ A' := by
        rw [Finset.mem_insert]
        exact ⟨fun h => h.resolve_left hja, Or.inr⟩
      simp only [Ne.symm hja, ite_false, smul_zero, zero_mul, zero_add, hmem]
      split_ifs <;> ring

/-- **The twist `w = (g^p y^r)⁻¹` has the logarithmic derivatives of the twisted logarithmic
model** in characteristic `p`. -/
theorem etaleCoordPartial_logTwistWeight (r : Fin n → ℕ) (g : X.functionFieldˣ) (p : ℕ)
    [CharP K p] (j : Fin n) :
    etaleCoordPartial (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)
        j (((g ^ p * logTwistMonomial c A r)⁻¹ : X.functionFieldˣ) : X.functionField) =
      (if j ∈ A then -((r j : ℕ) : X.functionField) *
        ((etaleChartCoordinateRationalUnit c j : X.functionField))⁻¹ else 0) *
        (((g ^ p * logTwistMonomial c A r)⁻¹ : X.functionFieldˣ) : X.functionField) := by
  have hpX : (p : X.functionField) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  have hgp : etaleCoordPartial (etaleChartFunctionFieldCoords c)
      (etaleChartFunctionFieldCoords_formallyEtale c) j ((g : X.functionField) ^ p) = 0 := by
    change etaleCoordinateDerivation _ _ j _ = 0
    rw [Derivation.leibniz_pow, nsmul_eq_mul, hpX, zero_mul]
  have hu := (g ^ p * logTwistMonomial c A r).ne_zero
  rw [Units.val_inv_eq_inv_val]
  change etaleCoordinateDerivation _ _ j _ = _
  rw [Derivation.leibniz_inv]
  change -(_ ^ 2) • etaleCoordPartial (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords_formallyEtale c) j _ = _
  rw [Units.val_mul, Units.val_pow_eq_pow_val, etaleCoordPartial_leibniz, hgp, zero_mul, zero_add,
    etaleCoordPartial_logTwistMonomial, smul_eq_mul]
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at hu
  field_simp
  split_ifs <;> ring

end Model

end MixedFujita

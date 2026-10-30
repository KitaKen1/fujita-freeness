/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ThresholdArcSpecialization
public import MixedFujita.FormalTestSNCBadComponent
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
Chart tests of the threshold condition (34) on the affine cone. A form f of degree D is a
function on the affine space over projective space; near the point P̃ = (1 at k, p elsewhere)
of the cone, the coordinates x_i = (y_i + p_i)(1 + s), x_k = 1 + s identify the cone with the
chart x_k = 1 times a line, and f becomes (1 + s)^D times the form in the chart. So a formal test
ψ in the chart at p, extended by the identity in s, is a formal test of affine space at P̃: its
Jacobian determinant is (1 + x_k)^(n-1) times the one of ψ (expand along the row of x_k), the
weights extended by zero at k give the same weighted orders, and the threshold inequality is the
same (`coneTest_bad_of_chart_bad`). No chart change and no renaming of the chart variables to
Fin (n - 1) is needed. The diagonal transforms f(μ x) of forms at rescaled points are handled on
the cone by composing a test with a rescaling of the variables
(`shiftedFormalTestMap_rescale_diagonal`); with μ = 1 this moves the cone point P̃ to c P̃. So a
failure of (34) at the point of projective space with homogeneous coordinates P is a failing
formal test of affine space at P itself, and by the comparison of formal tests with actual
divisors a failure of the threshold at P in the model form
(`affineSpace_modelThresholdBadAt_of_projectiveThresholdBadAt`).
-/

@[expose] public section

open MvPowerSeries

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type*} [Field K]

section Homogeneous

/-- A homogeneous polynomial of degree D scales by c^D when all arguments are multiplied by c. -/
theorem aeval_mul_of_isHomogeneous {σ A : Type*} [CommRing A] [Algebra K A]
    {f : MvPolynomial σ K} {D : ℕ} (hf : f.IsHomogeneous D) (c : A) (u : σ → A) :
    MvPolynomial.aeval (fun j => c * u j) f = c ^ D * MvPolynomial.aeval u f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have hdeg : ∑ i ∈ d.support, d i = D := by
    have h := hf (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply] at h
    simpa [Finsupp.sum] using h
  unfold Finsupp.prod
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end Homogeneous

section ChartRename

variable {n : ℕ} (k : Fin n)

/-- The inclusion of the chart variables x_i, i ≠ k, into the variables of affine space. -/
@[reducible]
def chartVariableEmbedding : {i : Fin n // i ≠ k} ↪ Fin n :=
  Function.Embedding.subtype _

theorem chartVariable_mem_range_embDomain_iff (x : Fin n →₀ ℕ) :
    x ∈ Set.range (Finsupp.embDomain (chartVariableEmbedding k)) ↔ x k = 0 := by
  rw [Finsupp.mem_range_embDomain_iff]
  constructor
  · intro h
    by_contra hk
    obtain ⟨i, hi⟩ := h (Finsupp.mem_support_iff.mpr hk)
    exact i.2 hi
  · intro h i hi
    refine ⟨⟨i, fun hik => ?_⟩, rfl⟩
    rw [hik] at hi
    exact (Finsupp.mem_support_iff.mp hi) h

theorem chartVariable_mem_range_mapDomain_iff (x : Fin n →₀ ℕ) :
    x ∈ Set.range (Finsupp.mapDomain (chartVariableEmbedding k)) ↔ x k = 0 := by
  rw [← chartVariable_mem_range_embDomain_iff k x]
  have : Finsupp.embDomain (chartVariableEmbedding k) =
      Finsupp.mapDomain (M := ℕ) (chartVariableEmbedding k) := by
    funext v
    exact Finsupp.embDomain_eq_mapDomain _ v
  rw [this]

/-- The derivative of a power series in the chart variables, viewed on affine space. -/
theorem pderiv_rename_chartVariable (G : MvPowerSeries {i : Fin n // i ≠ k} K) (j : Fin n) :
    pderiv j (rename (chartVariableEmbedding k) G) =
      if h : j = k then 0 else rename (chartVariableEmbedding k) (pderiv ⟨j, h⟩ G) := by
  classical
  ext d
  rw [coeff_pderiv]
  by_cases hd : d k = 0
  · obtain ⟨d', rfl⟩ := (chartVariable_mem_range_embDomain_iff k d).mpr hd
    by_cases hj : j = k
    · rw [dite_eq_left hj, map_zero]
      subst hj
      rw [coeff_rename_eq_zero, zero_mul]
      rw [chartVariable_mem_range_mapDomain_iff]
      rw [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · rw [dite_eq_right hj]
      have hsum : Finsupp.embDomain (chartVariableEmbedding k) d' + Finsupp.single j 1 =
          Finsupp.embDomain (chartVariableEmbedding k) (d' + Finsupp.single ⟨j, hj⟩ 1) := by
        rw [Finsupp.embDomain_add, Finsupp.embDomain_single]
        rfl
      have happ : (Finsupp.embDomain (chartVariableEmbedding k) d') j = d' ⟨j, hj⟩ :=
        Finsupp.embDomain_apply_self (chartVariableEmbedding k) d' ⟨j, hj⟩
      rw [hsum, coeff_embDomain_rename, coeff_embDomain_rename, coeff_pderiv, happ]
  · have h1 : d + Finsupp.single j 1 ∉ Set.range (Finsupp.mapDomain (chartVariableEmbedding k)) := by
      rw [chartVariable_mem_range_mapDomain_iff, Finsupp.add_apply]
      omega
    rw [coeff_rename_eq_zero _ _ h1, zero_mul]
    split_ifs with hj
    · rw [map_zero]
    · rw [coeff_rename_eq_zero]
      rwa [chartVariable_mem_range_mapDomain_iff]

/-- The weights of affine space extending the chart weights by zero at k. -/
def chartExtendedWeight (w : {i : Fin n // i ≠ k} → ℕ) : Fin n → ℕ :=
  fun j => if h : j = k then 0 else w ⟨j, h⟩

theorem weight_embDomain_chartVariable (w : {i : Fin n // i ≠ k} → ℕ)
    (d' : {i : Fin n // i ≠ k} →₀ ℕ) :
    Finsupp.weight (chartExtendedWeight k w) (Finsupp.embDomain (chartVariableEmbedding k) d') =
      Finsupp.weight w d' := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_embDomain]
  refine Finsupp.sum_congr fun i _ => ?_
  simp only [chartExtendedWeight, Function.Embedding.coe_subtype, i.2, dite_false]

/-- Renaming the chart variables keeps the weighted order for the extended weights. -/
theorem weightedOrder_rename_chartVariable (w : {i : Fin n // i ≠ k} → ℕ)
    (G : MvPowerSeries {i : Fin n // i ≠ k} K) :
    (rename (chartVariableEmbedding k) G).weightedOrder (chartExtendedWeight k w) =
      G.weightedOrder w := by
  classical
  apply le_antisymm
  · by_cases hG : G = 0
    · simp [hG]
    · obtain ⟨d', hd', hw⟩ := exists_coeff_ne_zero_and_weightedOrder w
        ((ne_zero_iff_weightedOrder_finite w).mp hG)
      calc (rename (chartVariableEmbedding k) G).weightedOrder (chartExtendedWeight k w)
          ≤ (Finsupp.weight (chartExtendedWeight k w)
              (Finsupp.embDomain (chartVariableEmbedding k) d') : ℕ∞) :=
            weightedOrder_le _ (by rwa [coeff_embDomain_rename])
        _ = G.weightedOrder w := by rw [weight_embDomain_chartVariable, hw]
  · apply le_weightedOrder
    intro d hd
    by_cases hdk : d k = 0
    · obtain ⟨d', rfl⟩ := (chartVariable_mem_range_embDomain_iff k d).mpr hdk
      rw [coeff_embDomain_rename]
      apply coeff_eq_zero_of_lt_weightedOrder w
      rwa [weight_embDomain_chartVariable] at hd
    · exact coeff_rename_eq_zero _ _ (by rwa [chartVariable_mem_range_mapDomain_iff])

theorem sum_chartExtendedWeight {m : ℕ} (k : Fin (m + 1)) (w : {i : Fin (m + 1) // i ≠ k} → ℕ) :
    ∑ j, chartExtendedWeight k w j = ∑ i, w i := by
  rw [Fin.sum_univ_succAbove _ k]
  simp only [chartExtendedWeight, dite_true, zero_add]
  rw [← Equiv.sum_comp (finSuccAboveEquiv k)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_right (Fin.succAbove_ne k a)]
  rfl

theorem chartExtendedWeight_ne_zero (w : {i : Fin n // i ≠ k} → ℕ) (hw : w ≠ 0) :
    chartExtendedWeight k w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  intro h0
  apply hi
  have := congrFun h0 (i : Fin n)
  simp only [chartExtendedWeight, i.2, dite_false, Pi.zero_apply] at this
  exact this

end ChartRename

section Cone

variable {m : ℕ} (k : Fin (m + 1))

/-- The point of the affine cone over the chart point p: x_k = 1 and x_i = p_i. -/
def conePoint (p : {i : Fin (m + 1) // i ≠ k} → K) : Fin (m + 1) → K :=
  fun i => if h : i = k then 1 else p ⟨i, h⟩

/-- The coordinate images of the cone test: x_k ↦ x_k and x_i ↦ ψ(y_i)(1 + x_k) + p_i x_k. -/
noncomputable def coneTestVars
    (ψ : MvPowerSeries {i : Fin (m + 1) // i ≠ k} K →ₐ[K]
      MvPowerSeries {i : Fin (m + 1) // i ≠ k} K)
    (p : {i : Fin (m + 1) // i ≠ k} → K) : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) K :=
  fun j => if h : j = k then X k else
    rename (chartVariableEmbedding k) (ψ (X ⟨j, h⟩)) * (1 + X k) + C (p ⟨j, h⟩) * X k

variable (ψ : MvPowerSeries {i : Fin (m + 1) // i ≠ k} K →ₐ[K]
    MvPowerSeries {i : Fin (m + 1) // i ≠ k} K) (p : {i : Fin (m + 1) // i ≠ k} → K)

theorem coneTestVars_constantCoeff (j : Fin (m + 1)) : constantCoeff (coneTestVars k ψ p j) = 0 := by
  unfold coneTestVars
  split_ifs with h
  · exact constantCoeff_X k
  · rw [map_add, map_mul, map_mul, constantCoeff_rename, constantCoeff_algHom_X, zero_mul,
      constantCoeff_X, mul_zero, add_zero]

/-- The cone test: the chart test ψ extended by the identity in x_k, in cone coordinates. -/
noncomputable def coneTest : MvPowerSeries (Fin (m + 1)) K →ₐ[K] MvPowerSeries (Fin (m + 1)) K :=
  substAlgHom (hasSubst_of_constantCoeff_zero (coneTestVars_constantCoeff k ψ p))

theorem coneTest_X (j : Fin (m + 1)) : coneTest k ψ p (X j) = coneTestVars k ψ p j :=
  substAlgHom_X _ j

/-- The shifted cone test of a form is (1 + x_k)^D times the chart test of the form. -/
theorem shiftedFormalTestMap_coneTest {f : MvPolynomial (Fin (m + 1)) K} {D : ℕ}
    (hf : f.IsHomogeneous D) :
    shiftedFormalTestMap (coneTest k ψ p) (conePoint k p) f =
      (1 + X k) ^ D * rename (chartVariableEmbedding k) (ψ (chartShiftedForm k p f)) := by
  have hvals : (fun j => algebraMap K (MvPowerSeries (Fin (m + 1)) K) (conePoint k p j) +
      coneTest k ψ p (X j)) = fun j => (1 + X k) *
        (if h : j = k then (1 : MvPowerSeries (Fin (m + 1)) K) else
          C (p ⟨j, h⟩) + rename (chartVariableEmbedding k) (ψ (X ⟨j, h⟩))) := by
    funext j
    rw [coneTest_X]
    by_cases h : j = k
    · subst h
      simp only [conePoint, coneTestVars, dite_true, map_one, mul_one]
    · simp only [conePoint, coneTestVars, h, dite_false, MvPowerSeries.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      ring
  unfold shiftedFormalTestMap
  rw [hvals, aeval_mul_of_isHomogeneous hf]
  congr 1
  unfold chartShiftedForm
  rw [MvPolynomial.comp_aeval_apply, MvPolynomial.comp_aeval_apply]
  congr 2
  funext j
  by_cases h : j = k
  · rw [dite_eq_left h, dite_eq_left h, map_one, map_one]
  · rw [dite_eq_right h, dite_eq_right h, map_add, map_add, algHom_C, rename_C]

/-- The Jacobian determinant of the cone test. -/
theorem coneTest_jacobian_det :
    (powerSeriesJacobian (coneTest k ψ p)).det =
      (1 + X k : MvPowerSeries (Fin (m + 1)) K) ^ m *
        rename (chartVariableEmbedding k) (powerSeriesJacobian ψ).det := by
  classical
  rw [Matrix.det_succ_row _ k, Finset.sum_eq_single k]
  · have hkk : powerSeriesJacobian (coneTest k ψ p) k k = 1 := by
      simp only [powerSeriesJacobian, Matrix.of_apply, coneTest_X, coneTestVars, dite_true,
        pderiv_X_self]
    have hminor : (powerSeriesJacobian (coneTest k ψ p)).submatrix k.succAbove k.succAbove =
        (1 + X k : MvPowerSeries (Fin (m + 1)) K) • ((rename (chartVariableEmbedding k)).toRingHom.mapMatrix
          ((powerSeriesJacobian ψ).submatrix (finSuccAboveEquiv k) (finSuccAboveEquiv k))) := by
      ext a b
      have ha : k.succAbove a ≠ k := Fin.succAbove_ne k a
      have hb : k.succAbove b ≠ k := Fin.succAbove_ne k b
      simp only [Matrix.submatrix_apply, powerSeriesJacobian, Matrix.of_apply, coneTest_X,
        coneTestVars, ha, hb, ↓reduceDIte, Matrix.smul_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, finSuccAboveEquiv_apply, map_add, Derivation.leibniz,
        pderiv_X_of_ne hb.symm, pderiv_rename_chartVariable, pderiv_C, Derivation.map_one_eq_zero,
        mul_zero, zero_add, add_zero]
    rw [hkk, hminor, Matrix.det_smul, Fintype.card_fin, ← RingHom.map_det,
      Matrix.det_submatrix_equiv_self, Even.neg_one_pow ⟨(k : ℕ), rfl⟩, one_mul, one_mul]
    rfl
  · intro j _ hj
    have : powerSeriesJacobian (coneTest k ψ p) k j = 0 := by
      simp only [powerSeriesJacobian, Matrix.of_apply, coneTest_X, coneTestVars, dite_true]
      exact pderiv_X_of_ne hj.symm
    rw [this, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem isUnit_one_add_X (k : Fin (m + 1)) : IsUnit (1 + X k : MvPowerSeries (Fin (m + 1)) K) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, map_one, constantCoeff_X, add_zero]
  exact isUnit_one

/-- A failing chart test of (34) gives a failing formal test of affine space at the cone point,
in the form of the comparison of formal tests with model divisors. -/
theorem coneTest_bad_of_chart_bad {ι : Type*} (f : ι → MvPolynomial (Fin (m + 1)) K)
    (D : ι → ℕ) (hf : ∀ ℓ, (f ℓ).IsHomogeneous (D ℓ)) (h : ℕ)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (w : {i : Fin (m + 1) // i ≠ k} → ℕ) (hw : w ≠ 0)
    (hbad : ∀ ℓ, (h : ℕ∞) * (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) ≤
      (ψ (chartShiftedForm k p (f ℓ))).weightedOrder w) :
    (powerSeriesJacobian (coneTest k ψ p)).det ≠ 0 ∧ chartExtendedWeight k w ≠ 0 ∧
      ∀ ℓ, (h : ℕ∞) * (((∑ i, chartExtendedWeight k w i : ℕ) : ℕ∞) +
        (powerSeriesJacobian (coneTest k ψ p)).det.weightedOrder (chartExtendedWeight k w)) ≤
        (shiftedFormalTestMap (coneTest k ψ p) (conePoint k p) (f ℓ)).weightedOrder
          (chartExtendedWeight k w) := by
  have hunit := isUnit_one_add_X (K := K) k
  have hord_unit : ∀ e : ℕ, ((1 + X k : MvPowerSeries (Fin (m + 1)) K) ^ e).weightedOrder
      (chartExtendedWeight k w) = 0 := fun e => weightedOrder_eq_zero_of_isUnit _ (hunit.pow e)
  refine ⟨?_, chartExtendedWeight_ne_zero k w hw, fun ℓ => ?_⟩
  · rw [coneTest_jacobian_det]
    exact mul_ne_zero (hunit.pow m).ne_zero
      (fun h0 => hJ (rename_injective _ (h0.trans (map_zero _).symm)))
  · rw [coneTest_jacobian_det, shiftedFormalTestMap_coneTest k ψ p (hf ℓ), weightedOrder_mul,
      weightedOrder_mul, hord_unit, hord_unit, zero_add, zero_add,
      weightedOrder_rename_chartVariable, weightedOrder_rename_chartVariable,
      sum_chartExtendedWeight]
    exact hbad ℓ

end Cone

section Diagonal

variable {N : ℕ}

/-- A shifted test of a diagonal transform f(μ x) at the rescaled point a P, for the test composed
with the rescaling by a with μ_j a_j = s, is s^D times the shifted test of f at P. -/
theorem shiftedFormalTestMap_rescale_diagonal {F : MvPolynomial (Fin N) K} {D : ℕ}
    (hF : F.IsHomogeneous D) (Ψ : MvPowerSeries (Fin N) K →ₐ[K] MvPowerSeries (Fin N) K)
    (P μ a : Fin N → K) (s : K) (ha : ∀ j, μ j * a j = s) :
    shiftedFormalTestMap (Ψ.comp (rescaleAlgHom a)) (fun j => a j * P j)
        (MvPolynomial.aeval (fun j => MvPolynomial.C (μ j) * MvPolynomial.X j) F) =
      C (s ^ D) * shiftedFormalTestMap Ψ P F := by
  unfold shiftedFormalTestMap
  rw [MvPolynomial.comp_aeval_apply]
  have hvals : (fun j => (MvPolynomial.aeval fun j => algebraMap K (MvPowerSeries (Fin N) K)
      (a j * P j) + (Ψ.comp (rescaleAlgHom a)) (X j))
        (MvPolynomial.C (μ j) * MvPolynomial.X j)) =
      fun j => C s * (algebraMap K (MvPowerSeries (Fin N) K) (P j) + Ψ (X j)) := by
    funext j
    rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.comp_apply,
      rescaleAlgHom_X_eq, map_mul Ψ, algHom_C]
    simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha j,
      map_mul]
    ring
  rw [hvals, aeval_mul_of_isHomogeneous hF, map_pow]

end Diagonal

section ModelCone

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

universe u

variable {K : Type u} [Field K] [CharZero K] [DecidableEq K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

attribute [local instance] specAlgebraOver affineSpace_smoothOfRelativeDimension

/-- A failure of (34) at the point of projective space with homogeneous coordinates P is a
failure of the threshold in the model form at the point P of the affine cone. -/
theorem affineSpace_modelThresholdBadAt_of_projectiveThresholdBadAt {n : ℕ} {ι : Type}
    [Finite ι] (g : ι → MvPolynomial (Fin n) K) (D : ι → ℕ) (hD : ∀ ℓ, (g ℓ).IsHomogeneous (D ℓ))
    (hg : ∃ ℓ, g ℓ ≠ 0) (h : ℕ) (hh : 1 ≤ h) (P : Fin n → K)
    (hP : ProjectiveThresholdBadAt g h P) :
    ModelThresholdBadAt (affineSpaceEtaleChart K n) 1 1
      (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K n) +
        principalCartierDivisor (affineSpace K n) 1))
      (affineSpacePoint K n P)
      (fun ℓ => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K n) (g ℓ)) h := by
  obtain ⟨k, hk, hbad⟩ := hP
  cases n with
  | zero => exact k.elim0
  | succ m =>
    unfold ProjectiveThresholdAt at hbad
    push Not at hbad
    obtain ⟨ψ, -, hdet, w, hw, hfail⟩ := hbad
    obtain ⟨hJ, hW, hcone⟩ :=
      coneTest_bad_of_chart_bad k ψ (fun i => P i / P k) g D hD h hdet w hw hfail
    have hunit : ∀ c : K, c ≠ 0 → ∀ v : Fin (m + 1) → ℕ,
        (C c : MvPowerSeries (Fin (m + 1)) K).weightedOrder v = 0 := fun c hc v =>
      weightedOrder_eq_zero_of_isUnit v ((isUnit_iff_ne_zero.mpr hc).map _)
    have hpt : (fun j => P k * conePoint k (fun i => P i / P k) j) = P := by
      funext j
      unfold conePoint
      by_cases hj : j = k
      · rw [dite_eq_left hj, mul_one, hj]
      · rw [dite_eq_right hj]
        field_simp
    set Ψ := (coneTest k ψ (fun i => P i / P k)).comp
      (rescaleAlgHom (fun _ : Fin (m + 1) => P k)) with hΨ
    have hshift : ∀ ℓ, shiftedFormalTestMap Ψ P (g ℓ) = C (P k ^ D ℓ) *
        shiftedFormalTestMap (coneTest k ψ (fun i => P i / P k))
          (conePoint k (fun i => P i / P k)) (g ℓ) := by
      intro ℓ
      have h1 := shiftedFormalTestMap_rescale_diagonal (hD ℓ) (coneTest k ψ (fun i => P i / P k))
        (conePoint k (fun i => P i / P k)) (fun _ => 1) (fun _ => P k) (P k) (fun _ => one_mul _)
      simp only [map_one, one_mul, MvPolynomial.aeval_X_left_apply, hpt] at h1
      exact h1
    have hprod : (∏ _i : Fin (m + 1), P k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun _ _ => hk
    refine affineSpace_modelThresholdBadAt_of_formalTest g hg P h hh Ψ ?_
      (chartExtendedWeight k w) hW ?_
    · rw [hΨ, powerSeriesJacobian_det_comp_rescale]
      exact mul_ne_zero ((isUnit_iff_ne_zero.mpr hprod).map (C (σ := Fin (m + 1)))).ne_zero hJ
    · intro ℓ
      rw [hshift ℓ, weightedOrder_mul, hunit _ (pow_ne_zero _ hk), zero_add, hΨ,
        powerSeriesJacobian_det_comp_rescale, weightedOrder_mul, hunit _ hprod, zero_add]
      exact hcone ℓ

end ModelCone

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Toric extraction of a rational ray in coordinates (§6.1). For a matrix M of natural numbers with
nonzero rows, the monomial substitution x_i ↦ u^(M_i) sends x^e to u^(e M). When e ↦ e M is
injective, the coefficient of u^(e M) in the image of f is the coefficient of x^e in f, so the
weighted order with weights w after substitution is the weighted order of f with weights M w.
The chart of the blow-up of the stratum {u_j = 0 : j ∈ S} where u_k generates, u_j ↦ u_j u_k for
j ∈ S \ {k}, has the matrix 1 + E whose column k is the indicator of S, and composites of charts
are products of their matrices, with injective e ↦ e M and nonzero rows. The stellar subdivision
algorithm reaches every nonzero ray: if c is supported on S with |S| ≥ 2 and c_k is minimal on S,
then c = C c' with c'_j = c_j - c_k on S \ {k} and Σ c' < Σ c. Hence every nonzero a ∈ ℕ^σ is
g times the column k of a composite M of blow-up charts, and the monomial valuation v_a is g
times the order along u_k = 0 after the substitution: v_a = g ord_E for the exceptional divisor E
of the composite, with Σ_i a_i = g Σ_i M_ik.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The exponent of the image of x_i under the monomial map with matrix M. -/
noncomputable def matrixRowExponent (M : Matrix σ σ ℕ) (i : σ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (M i)

/-- The monomial substitution x_i ↦ u^(M_i). -/
noncomputable def monomialSubstVars (M : Matrix σ σ ℕ) : σ → MvPowerSeries σ K :=
  fun i => monomial (matrixRowExponent M i) 1

/-- The exponent e M of the image of the monomial x^e. -/
noncomputable def monomialImageExponent (M : Matrix σ σ ℕ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Matrix.vecMul (⇑e) M)

theorem hasSubst_monomialSubstVars {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0) :
    HasSubst (monomialSubstVars (K := K) M) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  obtain ⟨j, hj⟩ := hrow i
  have hne : (0 : σ →₀ ℕ) ≠ matrixRowExponent M i := by
    intro h
    apply hj
    have := congrArg (fun x : σ →₀ ℕ => x j) h
    simpa [matrixRowExponent] using this.symm
  rw [monomialSubstVars, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial, ite_eq_right hne]

omit [DecidableEq σ] in
theorem sum_smul_matrixRowExponent (M : Matrix σ σ ℕ) (e : σ →₀ ℕ) :
    ∑ s ∈ e.support, e s • matrixRowExponent M s = monomialImageExponent M e := by
  ext j
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    matrixRowExponent, monomialImageExponent, Finsupp.coe_equivFunOnFinite_symm, Matrix.vecMul,
    dotProduct]
  rw [Finset.sum_subset (Finset.subset_univ e.support)]
  intro s _ hs
  rw [Finsupp.notMem_support_iff.mp hs, zero_mul]

omit [DecidableEq σ] in
/-- The monomial substitution sends x^e to u^(e M). -/
theorem prod_monomialSubstVars (M : Matrix σ σ ℕ) (e : σ →₀ ℕ) :
    (e.prod fun s n => (monomialSubstVars (K := K) M s) ^ n) =
      monomial (monomialImageExponent M e) 1 := by
  simp only [Finsupp.prod, monomialSubstVars, monomial_pow, one_pow]
  rw [prod_monomial, Finset.prod_const_one, sum_smul_matrixRowExponent]

theorem coeff_subst_monomialSubstVars {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0)
    (hinj : Function.Injective (monomialImageExponent M)) (f : MvPowerSeries σ K)
    (e : σ →₀ ℕ) :
    coeff (monomialImageExponent M e) (subst (monomialSubstVars (K := K) M) f) = coeff e f := by
  rw [coeff_subst (hasSubst_monomialSubstVars hrow)]
  simp only [prod_monomialSubstVars, coeff_monomial]
  rw [finsum_eq_single _ e]
  · simp
  · intro e' he'
    rw [ite_eq_right (fun h => he' (hinj h).symm), smul_zero]

theorem coeff_subst_monomialSubstVars_of_notMem {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0)
    (f : MvPowerSeries σ K) (d : σ →₀ ℕ) (hd : ∀ e, monomialImageExponent M e ≠ d) :
    coeff d (subst (monomialSubstVars (K := K) M) f) = 0 := by
  rw [coeff_subst (hasSubst_monomialSubstVars hrow)]
  simp only [prod_monomialSubstVars, coeff_monomial]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  rw [ite_eq_right (fun h => hd e h.symm), smul_zero]

omit [DecidableEq σ] in
theorem weight_monomialImageExponent (M : Matrix σ σ ℕ) (w : σ → ℕ) (e : σ →₀ ℕ) :
    Finsupp.weight w (monomialImageExponent M e) = Finsupp.weight (M.mulVec w) e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by simp)]
  simp only [monomialImageExponent, Finsupp.coe_equivFunOnFinite_symm, Matrix.vecMul,
    Matrix.mulVec, dotProduct, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The weighted order after the monomial substitution is the weighted order with weights M w. -/
theorem weightedOrder_subst_monomialSubstVars {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0)
    (hinj : Function.Injective (monomialImageExponent M)) (w : σ → ℕ) (f : MvPowerSeries σ K) :
    (subst (monomialSubstVars (K := K) M) f).weightedOrder w = f.weightedOrder (M.mulVec w) := by
  apply le_antisymm
  · by_cases hf : f = 0
    · rw [hf, weightedOrder_zero]
      exact le_top
    obtain ⟨e, he, hwe⟩ := exists_coeff_ne_zero_and_weightedOrder (M.mulVec w)
      ((ne_zero_iff_weightedOrder_finite (M.mulVec w)).mp hf)
    have hc : coeff (monomialImageExponent M e) (subst (monomialSubstVars (K := K) M) f) ≠ 0 := by
      rwa [coeff_subst_monomialSubstVars hrow hinj]
    calc (subst (monomialSubstVars (K := K) M) f).weightedOrder w
        ≤ Finsupp.weight w (monomialImageExponent M e) := weightedOrder_le w hc
      _ = f.weightedOrder (M.mulVec w) := by rw [weight_monomialImageExponent, hwe]
  · apply le_weightedOrder
    intro d hd
    by_cases him : ∃ e, monomialImageExponent M e = d
    · obtain ⟨e, rfl⟩ := him
      rw [coeff_subst_monomialSubstVars hrow hinj]
      apply coeff_eq_zero_of_lt_weightedOrder
      rwa [← weight_monomialImageExponent]
    · push Not at him
      exact coeff_subst_monomialSubstVars_of_notMem hrow f d him

omit [Fintype σ] [DecidableEq σ] in
/-- Scaling the weights by g ≥ 1 scales the weighted order. -/
theorem weightedOrder_nsmul_weight (g : ℕ) (hg : 1 ≤ g) (w : σ → ℕ) (f : MvPowerSeries σ K) :
    f.weightedOrder (fun i => g * w i) = g * f.weightedOrder w := by
  have hweight : ∀ d : σ →₀ ℕ, Finsupp.weight (fun i => g * w i) d = g * Finsupp.weight w d := by
    intro d
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  by_cases hf : f = 0
  · rw [hf, weightedOrder_zero, weightedOrder_zero, ENat.mul_top (by exact_mod_cast (by omega))]
  obtain ⟨d, hd, hwd⟩ := exists_coeff_ne_zero_and_weightedOrder w
    ((ne_zero_iff_weightedOrder_finite w).mp hf)
  apply le_antisymm
  · calc f.weightedOrder (fun i => g * w i) ≤ Finsupp.weight (fun i => g * w i) d :=
          weightedOrder_le _ hd
      _ = g * f.weightedOrder w := by rw [hweight, ← hwd]; push_cast; rfl
  · apply le_weightedOrder
    intro d' hd'
    apply coeff_eq_zero_of_lt_weightedOrder w
    rw [← hwd] at hd' ⊢
    rw [hweight] at hd'
    have h : g * Finsupp.weight w d' < g * Finsupp.weight w d := by exact_mod_cast hd'
    exact_mod_cast Nat.lt_of_mul_lt_mul_left h

section Charts

/-- The chart of the blow-up of the stratum {u_j = 0 : j ∈ S} in which u_k generates:
u_j ↦ u_j u_k for j ∈ S \ {k}. Its column k is the indicator of S. -/
def blowupChartMatrix (S : Finset σ) (k : σ) : Matrix σ σ ℕ :=
  1 + Matrix.of fun i l => if l = k ∧ i ∈ S ∧ i ≠ k then 1 else 0

/-- The composite of a list of blow-up charts. -/
def toricChartProduct (L : List (Finset σ × σ)) : Matrix σ σ ℕ :=
  (L.map fun p => blowupChartMatrix p.1 p.2).prod

theorem mulVec_blowupChartMatrix (S : Finset σ) (k : σ) (c : σ → ℕ) (i : σ) :
    (blowupChartMatrix S k).mulVec c i = c i + if i ∈ S ∧ i ≠ k then c k else 0 := by
  rw [blowupChartMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  by_cases hi : i ∈ S ∧ i ≠ k
  · have h1 : ∀ l, (if l = k ∧ i ∈ S ∧ i ≠ k then (1 : ℕ) else 0) * c l =
        if l = k then c k else 0 := by
      intro l
      by_cases hl : l = k
      · subst hl
        simp [hi]
      · simp [hl]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_ite_eq' Finset.univ k,
      ite_eq_left (Finset.mem_univ k), ite_eq_left hi]
  · have h1 : ∀ l, (if l = k ∧ i ∈ S ∧ i ≠ k then (1 : ℕ) else 0) * c l = 0 := by
      intro l
      rw [ite_eq_right (fun h => hi h.2), zero_mul]
    rw [Finset.sum_congr rfl (fun l _ => h1 l), Finset.sum_const_zero, ite_eq_right hi]

theorem vecMul_blowupChartMatrix_of_ne (S : Finset σ) {k l : σ} (hl : l ≠ k) (e : σ → ℕ) :
    Matrix.vecMul e (blowupChartMatrix S k) l = e l := by
  rw [blowupChartMatrix, Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply]
  have h0 : Matrix.vecMul e
      (Matrix.of fun i l => if l = k ∧ i ∈ S ∧ i ≠ k then (1 : ℕ) else 0) l = 0 := by
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (fun h => hl h.1), mul_zero]
  rw [h0, add_zero]

theorem vecMul_blowupChartMatrix_self (S : Finset σ) (k : σ) (e : σ → ℕ) :
    Matrix.vecMul e (blowupChartMatrix S k) k =
      e k + ∑ i, if i ∈ S ∧ i ≠ k then e i else 0 := by
  rw [blowupChartMatrix, Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply]
  congr 1
  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all

theorem vecMul_blowupChartMatrix_injective (S : Finset σ) (k : σ) :
    Function.Injective fun e : σ → ℕ => Matrix.vecMul e (blowupChartMatrix S k) := by
  intro e e' h
  have hne : ∀ l, l ≠ k → e l = e' l := by
    intro l hl
    have := congrFun h l
    simp only at this
    rwa [vecMul_blowupChartMatrix_of_ne S hl, vecMul_blowupChartMatrix_of_ne S hl] at this
  funext l
  by_cases hl : l = k
  · subst hl
    have h1 := congrFun h l
    simp only at h1
    rw [vecMul_blowupChartMatrix_self, vecMul_blowupChartMatrix_self] at h1
    have h2 : (∑ i, if i ∈ S ∧ i ≠ l then e i else 0) =
        ∑ i, if i ∈ S ∧ i ≠ l then e' i else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S ∧ i ≠ l
      · rw [ite_eq_left hi, ite_eq_left hi, hne i hi.2]
      · rw [ite_eq_right hi, ite_eq_right hi]
    rw [h2] at h1
    exact Nat.add_right_cancel h1
  · exact hne l hl

theorem toricChartProduct_cons (p : Finset σ × σ) (L : List (Finset σ × σ)) :
    toricChartProduct (p :: L) = blowupChartMatrix p.1 p.2 * toricChartProduct L := by
  simp [toricChartProduct]

theorem one_le_toricChartProduct_diag (L : List (Finset σ × σ)) (i : σ) :
    1 ≤ toricChartProduct L i i := by
  induction L with
  | nil => simp [toricChartProduct]
  | cons p L ih =>
    rw [toricChartProduct_cons, Matrix.mul_apply]
    have hdiag : 1 ≤ blowupChartMatrix p.1 p.2 i i := by
      simp [blowupChartMatrix]
    calc 1 ≤ blowupChartMatrix p.1 p.2 i i * toricChartProduct L i i := by nlinarith
      _ ≤ ∑ l, blowupChartMatrix p.1 p.2 i l * toricChartProduct L l i :=
        Finset.single_le_sum (f := fun l => blowupChartMatrix p.1 p.2 i l *
          toricChartProduct L l i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem toricChartProduct_row_ne_zero (L : List (Finset σ × σ)) (i : σ) :
    ∃ j, toricChartProduct L i j ≠ 0 :=
  ⟨i, by have := one_le_toricChartProduct_diag L i; omega⟩

theorem monomialImageExponent_toricChartProduct_injective (L : List (Finset σ × σ)) :
    Function.Injective (monomialImageExponent (toricChartProduct L)) := by
  have hfun : ∀ L : List (Finset σ × σ),
      Function.Injective fun e : σ → ℕ => Matrix.vecMul e (toricChartProduct L) := by
    intro L
    induction L with
    | nil =>
      intro e e' h
      simpa [toricChartProduct] using h
    | cons p L ih =>
      intro e e' h
      simp only [toricChartProduct_cons, ← Matrix.vecMul_vecMul] at h
      exact vecMul_blowupChartMatrix_injective p.1 p.2 (ih h)
  intro e e' h
  have h' := congrArg (fun x : σ →₀ ℕ => (x : σ → ℕ)) h
  simp only [monomialImageExponent, Finsupp.coe_equivFunOnFinite_symm] at h'
  exact DFunLike.coe_injective (hfun L h')

/-- Stellar subdivision: every nonzero ray is g times a column of a composite of blow-up
charts. -/
theorem exists_toricChart_column (c : σ → ℕ) (hc : c ≠ 0) :
    ∃ (L : List (Finset σ × σ)) (k : σ) (g : ℕ), 1 ≤ g ∧ ∀ i, c i = g * toricChartProduct L i k := by
  suffices h : ∀ n, ∀ c : σ → ℕ, ∑ i, c i = n → c ≠ 0 →
      ∃ (L : List (Finset σ × σ)) (k : σ) (g : ℕ), 1 ≤ g ∧
        ∀ i, c i = g * toricChartProduct L i k from h _ c rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hsum hc
    set S := Finset.univ.filter fun i => c i ≠ 0 with hS
    have hSne : S.Nonempty := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h
        push Not at h
        exact hc (funext h)
      exact ⟨i, by simp [hS, hi]⟩
    obtain ⟨k, hkS, hkmin⟩ := S.exists_min_image c hSne
    have hk0 : c k ≠ 0 := (Finset.mem_filter.mp hkS).2
    by_cases hone : ∀ j ∈ S, j = k
    · refine ⟨[], k, c k, Nat.pos_of_ne_zero hk0, fun i => ?_⟩
      simp only [toricChartProduct, List.map_nil, List.prod_nil, Matrix.one_apply]
      by_cases hik : i = k
      · subst hik
        simp
      · rw [ite_eq_right hik, mul_zero]
        by_contra hi
        exact hik (hone i (by simp [hS, hi]))
    · push Not at hone
      obtain ⟨j, hjS, hjk⟩ := hone
      set c' : σ → ℕ := fun i => if i ∈ S ∧ i ≠ k then c i - c k else c i with hc'
      have hc'k : c' k = c k := by simp [hc']
      have hcc' : ∀ i, c i = (blowupChartMatrix S k).mulVec c' i := by
        intro i
        rw [mulVec_blowupChartMatrix, hc'k]
        by_cases hi : i ∈ S ∧ i ≠ k
        · have h1 : c' i = c i - c k := ite_eq_left hi
          rw [h1, ite_eq_left hi]
          have := hkmin i hi.1
          omega
        · have h1 : c' i = c i := ite_eq_right hi
          rw [h1, ite_eq_right hi, add_zero]
      have hlt : ∑ i, c' i < n := by
        rw [← hsum]
        apply Finset.sum_lt_sum
        · intro i _
          simp only [hc']
          split_ifs <;> omega
        · refine ⟨j, Finset.mem_univ j, ?_⟩
          have hj0 : c j ≠ 0 := (Finset.mem_filter.mp hjS).2
          have h1 : c' j = c j - c k := ite_eq_left ⟨hjS, hjk⟩
          rw [h1]
          omega
      have hc'0 : c' ≠ 0 := by
        intro h
        apply hk0
        rw [← hc'k, h]
        rfl
      obtain ⟨L, k', g, hg, hL⟩ := ih _ hlt c' rfl hc'0
      refine ⟨(S, k) :: L, k', g, hg, fun i => ?_⟩
      rw [hcc' i, toricChartProduct_cons, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hL l]
      ring

/-- Toric extraction in coordinates: the monomial valuation with weights a ≠ 0 is g times the
order along u_k = 0 after the monomial substitution of a composite of blow-up charts, and
Σ_i a_i = g Σ_i M_ik. -/
theorem toric_extraction (a : σ → ℕ) (ha : a ≠ 0) :
    ∃ (L : List (Finset σ × σ)) (k : σ) (g : ℕ), 1 ≤ g ∧
      (∀ i, a i = g * toricChartProduct L i k) ∧
      (∑ i, a i = g * ∑ i, toricChartProduct L i k) ∧
      ∀ f : MvPowerSeries σ K, f.weightedOrder a =
        g * (subst (monomialSubstVars (K := K) (toricChartProduct L)) f).weightedOrder (Pi.single k 1) := by
  obtain ⟨L, k, g, hg, hL⟩ := exists_toricChart_column a ha
  refine ⟨L, k, g, hg, hL, by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hL i,
    fun f => ?_⟩
  rw [weightedOrder_subst_monomialSubstVars (toricChartProduct_row_ne_zero L)
    (monomialImageExponent_toricChartProduct_injective L)]
  have hcol : (toricChartProduct L).mulVec (Pi.single k 1) = fun i => toricChartProduct L i k := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol, ← weightedOrder_nsmul_weight g hg]
  congr 1
  funext i
  exact hL i

end Charts

end MixedFujita

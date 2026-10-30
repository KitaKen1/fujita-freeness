/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricDiscrepancy
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
Monomial substitutions on polynomial rings (step 12, section 6.1 of the manuscript). For a matrix
M of natural numbers the substitution x_i ↦ u^(M_i) is a map of polynomial rings. If M has an
integer inverse N, the Laurent monomials x^(N_l) invert it: the substitution is injective and
every element of a fraction field of the target is a quotient of images, so the map is
birational. Its Jacobian determinant is det M · u^κ with κ_j = Σ_i M_ij - 1. A composite of
blow-up charts has an integer inverse, and the stellar subdivision reaching a ray only blows up
strata inside the support of the ray, so the rows of the composite outside the support are unit
rows: the coordinates outside the support are not changed.
-/

@[expose] public section

namespace MixedFujita

open MvPolynomial

section Laurent

variable {σ F : Type*} [Fintype σ] [Field F]

omit [Fintype σ] in
theorem prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) {a : F} (ha : a ≠ 0) (f : ι → ℤ) :
    ∏ l ∈ s, a ^ f l = a ^ ∑ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert l s hl ih => rw [Finset.prod_insert hl, Finset.sum_insert hl, zpow_add₀ ha, ih]

/-- Laurent monomials compose by matrix multiplication. -/
theorem laurentMonomial_subst {y : σ → F} (hy : ∀ i, y i ≠ 0) (N : Matrix σ σ ℤ) (v : σ → ℤ) :
    ∏ l, (∏ i, y i ^ N l i) ^ v l = ∏ i, y i ^ Matrix.vecMul v N i := by
  have h1 : ∀ l, (∏ i, y i ^ N l i) ^ v l = ∏ i, y i ^ (N l i * v l) := by
    intro l
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
  rw [Finset.prod_congr rfl fun l _ => h1 l, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_zpow_eq_zpow_sum _ (hy i)]
  congr 1
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

variable [DecidableEq σ]

theorem laurentMonomial_single (y : σ → F) (j : σ) :
    ∏ i, y i ^ (Pi.single j 1 : σ → ℤ) i = y j := by
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, zpow_one]

theorem vecMul_row_of_mul_eq_one {A B : Matrix σ σ ℤ} (h : A * B = 1) (i : σ) :
    Matrix.vecMul (A i) B = Pi.single i 1 := by
  funext j
  have h1 := congrFun (congrFun h i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  rw [Pi.single_apply]
  simp only [Matrix.vecMul, dotProduct]
  rw [h1]
  exact if_congr eq_comm rfl rfl

/-- Substituting the Laurent monomials y^(N_l) into the monomial with exponents M_i gives y_i
when M N = 1. -/
theorem laurentMonomial_natPow_subst {y : σ → F} (hy : ∀ i, y i ≠ 0) (M : Matrix σ σ ℕ)
    (N : Matrix σ σ ℤ) (hMN : M.map (Nat.cast : ℕ → ℤ) * N = 1) (i : σ) :
    ∏ l, (∏ j, y j ^ N l j) ^ M i l = y i := by
  have h1 := laurentMonomial_subst hy N ((M.map (Nat.cast : ℕ → ℤ)) i)
  rw [vecMul_row_of_mul_eq_one hMN i, laurentMonomial_single] at h1
  simpa only [Matrix.map_apply, zpow_natCast] using h1

/-- Substituting the monomials w^(M_i) into the Laurent monomial with exponents N_l gives w_l
when N M = 1. -/
theorem laurentMonomial_subst_natPow {w : σ → F} (hw : ∀ i, w i ≠ 0) (M : Matrix σ σ ℕ)
    (N : Matrix σ σ ℤ) (hNM : N * M.map (Nat.cast : ℕ → ℤ) = 1) (l : σ) :
    ∏ i, (∏ j, w j ^ M i j) ^ N l i = w l := by
  have h1 := laurentMonomial_subst hw (M.map (Nat.cast : ℕ → ℤ)) (N l)
  rw [vecMul_row_of_mul_eq_one hNM l, laurentMonomial_single] at h1
  simpa only [Matrix.map_apply, zpow_natCast] using h1

end Laurent

section Substitution

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The monomial substitution x_i ↦ u^(M_i) on polynomials. -/
noncomputable def toricSubst (M : Matrix σ σ ℕ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun i => monomial (matrixRowExponent M i) (1 : K)

omit [DecidableEq σ] in
theorem toricSubst_X (M : Matrix σ σ ℕ) (i : σ) :
    toricSubst (K := K) M (X i) = monomial (matrixRowExponent M i) 1 :=
  aeval_X _ i

omit [DecidableEq σ] in
/-- A ring homomorphism sends the monomial u^e to the product of the images of the variables. -/
theorem ringHom_monomial_one {S G : Type*} [CommSemiring S] [FunLike G (MvPolynomial σ K) S]
    [RingHomClass G (MvPolynomial σ K) S] (g : G) (e : σ →₀ ℕ) :
    g (monomial e 1) = ∏ l, g (X l) ^ e l := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod]
  exact Finset.prod_congr rfl fun l _ => map_pow g _ _

omit [DecidableEq σ] in
/-- A ring homomorphism sends the image of x_i to the monomial in the images of the variables with
exponents M_i. -/
theorem ringHom_toricSubst_X {S G : Type*} [CommSemiring S] [FunLike G (MvPolynomial σ K) S]
    [RingHomClass G (MvPolynomial σ K) S] (g : G) (M : Matrix σ σ ℕ) (i : σ) :
    g (toricSubst M (X i)) = ∏ l, g (X l) ^ M i l := by
  rw [toricSubst_X, ringHom_monomial_one]
  rfl

/-- A coordinate whose row is a unit row is not changed. -/
theorem toricSubst_X_of_row (M : Matrix σ σ ℕ) (i : σ)
    (h : ∀ l, M i l = if i = l then 1 else 0) : toricSubst (K := K) M (X i) = X i := by
  rw [toricSubst_X]
  have he : matrixRowExponent M i = Finsupp.single i 1 := by
    ext l
    simp only [matrixRowExponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.single_apply]
    exact h l
  rw [he]
  rfl

/-- A monomial substitution with an integer right inverse is injective. -/
theorem toricSubst_injective (M : Matrix σ σ ℕ) (N : Matrix σ σ ℤ)
    (hMN : M.map (Nat.cast : ℕ → ℤ) * N = 1) : Function.Injective (toricSubst (K := K) M) := by
  let y : σ → FractionRing (MvPolynomial σ K) := fun i =>
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i)
  have hy : ∀ i, y i ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) _)).mpr (X_ne_zero i)
  let θ : MvPolynomial σ K →ₐ[K] FractionRing (MvPolynomial σ K) :=
    aeval fun l => ∏ i, y i ^ N l i
  have hθX : ∀ l, θ (X l) = ∏ i, y i ^ N l i := fun l => aeval_X _ l
  have hθ : θ.comp (toricSubst M) =
      IsScalarTower.toAlgHom K (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change θ (toricSubst M (X i)) = y i
    rw [ringHom_toricSubst_X θ M i, Finset.prod_congr rfl fun l _ => by rw [hθX l]]
    exact laurentMonomial_natPow_subst hy M N hMN i
  intro p q hpq
  apply IsFractionRing.injective (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))
  have hp : θ (toricSubst M p) = algebraMap _ _ p := congrArg (fun g => g p) hθ
  have hq : θ (toricSubst M q) = algebraMap _ _ q := congrArg (fun g => g q) hθ
  rw [← hp, ← hq, hpq]

/-- A monomial substitution with an integer inverse is birational: every element of a fraction
field of the polynomial ring is a quotient of images of polynomials. -/
theorem toricSubst_exists_div (M : Matrix σ σ ℕ) (N : Matrix σ σ ℤ)
    (hMN : M.map (Nat.cast : ℕ → ℤ) * N = 1) (hNM : N * M.map (Nat.cast : ℕ → ℤ) = 1)
    {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (z : F) : ∃ p q : MvPolynomial σ K, q ≠ 0 ∧
      z = algebraMap (MvPolynomial σ K) F (toricSubst M p) /
        algebraMap (MvPolynomial σ K) F (toricSubst M q) := by
  have hinj := toricSubst_injective (K := K) M N hMN
  let g : MvPolynomial σ K →+* F :=
    (algebraMap (MvPolynomial σ K) F).comp (toricSubst (K := K) M : MvPolynomial σ K →+* _)
  have hg : Function.Injective g := (IsFractionRing.injective (MvPolynomial σ K) F).comp hinj
  let ι : FractionRing (MvPolynomial σ K) →+* F := IsFractionRing.lift hg
  have hι : ∀ a : MvPolynomial σ K, ι (algebraMap _ _ a) =
      algebraMap (MvPolynomial σ K) F (toricSubst M a) := fun a =>
    IsFractionRing.lift_algebraMap hg a
  let y : σ → FractionRing (MvPolynomial σ K) := fun i =>
    algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (X i)
  let θ : MvPolynomial σ K →ₐ[K] FractionRing (MvPolynomial σ K) :=
    aeval fun l => ∏ i, y i ^ N l i
  have hθX : ∀ l, θ (X l) = ∏ i, y i ^ N l i := fun l => aeval_X _ l
  let w : σ → F := fun j => algebraMap (MvPolynomial σ K) F (X j)
  have hw : ∀ j, w j ≠ 0 := fun j =>
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) F)).mpr (X_ne_zero j)
  have hιθ : ∀ a : MvPolynomial σ K, ι (θ a) = algebraMap (MvPolynomial σ K) F a := by
    have h : ι.comp (θ : MvPolynomial σ K →+* FractionRing (MvPolynomial σ K)) =
        algebraMap (MvPolynomial σ K) F := by
      apply MvPolynomial.ringHom_ext
      · intro k
        change ι (θ (C k)) = algebraMap (MvPolynomial σ K) F (C k)
        have h1 : θ (C k) = algebraMap (MvPolynomial σ K) _ (C k) := by
          rw [show (C k : MvPolynomial σ K) = algebraMap K _ k from rfl, AlgHom.commutes,
            ← IsScalarTower.algebraMap_apply]
        rw [h1, hι]
        congr 1
        rw [show (C k : MvPolynomial σ K) = algebraMap K _ k from rfl, AlgHom.commutes]
      · intro l
        change ι (θ (X l)) = w l
        rw [hθX l, map_prod]
        have h2 : ∀ i, ι (y i ^ N l i) = (∏ j, w j ^ M i j) ^ N l i := by
          intro i
          rw [map_zpow₀, hι, ringHom_toricSubst_X (algebraMap (MvPolynomial σ K) F) M i]
        rw [Finset.prod_congr rfl fun i _ => h2 i]
        exact laurentMonomial_subst_natPow hw M N hNM l
    exact fun a => congrArg (fun f => f a) h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) z
  obtain ⟨p₁, q₁, hq₁, h₁⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) (θ a)
  obtain ⟨p₂, q₂, hq₂, h₂⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) (θ b)
  have hb0 : algebraMap (MvPolynomial σ K) F b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial σ K) F)).mpr
      (nonZeroDivisors.ne_zero hb)
  have hp₂ : p₂ ≠ 0 := by
    rintro rfl
    apply hb0
    rw [← hιθ b, ← h₂, map_zero, zero_div, map_zero]
  refine ⟨p₁ * q₂, q₁ * p₂, mul_ne_zero (nonZeroDivisors.ne_zero hq₁) hp₂, ?_⟩
  rw [← hιθ a, ← hιθ b, ← h₁, ← h₂, map_div₀, map_div₀, hι, hι, hι, hι, div_div_div_eq,
    map_mul, map_mul, map_mul, map_mul]

end Substitution

section Jacobian

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The Jacobian of the monomial substitution on polynomials. -/
noncomputable def toricSubstJacobian (M : Matrix σ σ ℕ) : Matrix σ σ (MvPolynomial σ K) :=
  Matrix.of fun i j => pderiv j (toricSubst (K := K) M (X i))

/-- det J = det M · u^κ when no row of M vanishes and every column sum of M is positive. -/
theorem det_toricSubstJacobian {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0)
    (hcol : ∀ j, 1 ≤ ∑ i, M i j) :
    (toricSubstJacobian (K := K) M).det =
      C (M.map (Nat.cast : ℕ → K)).det * monomial (jacobianExponent M) 1 := by
  apply MvPolynomial.coe_injective
  have h := det_jacobian_monomialSubst (K := K) hrow hcol
  have hJ : powerSeriesJacobian
      (MvPowerSeries.substAlgHom (R := K) (hasSubst_monomialSubstVars hrow)) =
        (MvPolynomial.coeToMvPowerSeries.ringHom (R := K) (σ := σ)).mapMatrix
          (toricSubstJacobian M) := by
    ext i j
    simp only [powerSeriesJacobian, Matrix.of_apply, MvPowerSeries.substAlgHom_X,
      monomialSubstVars, RingHom.mapMatrix_apply, Matrix.map_apply, toricSubstJacobian,
      toricSubst_X]
    rw [← MvPolynomial.coe_monomial, MvPowerSeries.pderiv_coe]
    rfl
  rw [hJ, ← RingHom.map_det] at h
  rw [MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_monomial]
  exact h

end Jacobian

section Charts

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A composite of blow-up charts has an integer inverse. -/
theorem exists_int_inverse_toricChartProduct (L : List (Finset σ × σ)) :
    ∃ N : Matrix σ σ ℤ, (toricChartProduct L).map (Nat.cast : ℕ → ℤ) * N = 1 ∧
      N * (toricChartProduct L).map (Nat.cast : ℕ → ℤ) = 1 := by
  have hdet : ((toricChartProduct L).map (Nat.cast : ℕ → ℤ)).det = 1 := by
    have h := det_toricChartProduct (K := ℚ) L
    have hmap : (toricChartProduct L).map (Nat.cast : ℕ → ℚ) =
        (Int.castRingHom ℚ).mapMatrix ((toricChartProduct L).map (Nat.cast : ℕ → ℤ)) := by
      ext i j
      simp
    rw [hmap, ← RingHom.map_det] at h
    have h' : ((((toricChartProduct L).map (Nat.cast : ℕ → ℤ)).det : ℤ) : ℚ) = 1 := h
    exact_mod_cast h'
  refine ⟨Matrix.adjugate ((toricChartProduct L).map (Nat.cast : ℕ → ℤ)), ?_, ?_⟩
  · rw [Matrix.mul_adjugate, hdet, one_smul]
  · rw [Matrix.adjugate_mul, hdet, one_smul]

/-- A row of a composite of blow-up charts whose index lies in none of the blown-up strata is a
unit row. -/
theorem toricChartProduct_apply_of_forall_notMem (L : List (Finset σ × σ)) (i : σ)
    (hi : ∀ p ∈ L, i ∉ p.1) (l : σ) : toricChartProduct L i l = if i = l then 1 else 0 := by
  induction L with
  | nil => simp [toricChartProduct, Matrix.one_apply]
  | cons p L ih =>
    have hip : i ∉ p.1 := hi p List.mem_cons_self
    have hC : ∀ j, blowupChartMatrix p.1 p.2 i j = if i = j then 1 else 0 := by
      intro j
      simp [blowupChartMatrix, Matrix.one_apply, hip]
    rw [toricChartProduct_cons, Matrix.mul_apply, Finset.sum_congr rfl fun j _ => by rw [hC j],
      Finset.sum_eq_single i (fun j _ hji => by rw [ite_eq_right (Ne.symm hji), zero_mul])
        (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl, one_mul]
    exact ih fun q hq => hi q (List.mem_cons_of_mem _ hq)

/-- Stellar subdivision inside the support: every nonzero ray is g times a column of a composite
of blow-up charts of strata contained in the support of the ray. -/
theorem exists_toricChart_column_supported (c : σ → ℕ) (hc : c ≠ 0) :
    ∃ (L : List (Finset σ × σ)) (k : σ) (g : ℕ), 1 ≤ g ∧
      (∀ i, c i = g * toricChartProduct L i k) ∧ ∀ p ∈ L, ∀ i ∈ p.1, c i ≠ 0 := by
  suffices h : ∀ n, ∀ c : σ → ℕ, ∑ i, c i = n → c ≠ 0 →
      ∃ (L : List (Finset σ × σ)) (k : σ) (g : ℕ), 1 ≤ g ∧
        (∀ i, c i = g * toricChartProduct L i k) ∧ ∀ p ∈ L, ∀ i ∈ p.1, c i ≠ 0 from
    h _ c rfl hc
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
    · refine ⟨[], k, c k, Nat.pos_of_ne_zero hk0, fun i => ?_, fun p hp => absurd hp List.not_mem_nil⟩
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
      have hsupp : ∀ i, c' i ≠ 0 → c i ≠ 0 := by
        intro i hi h0
        apply hi
        simp only [hc']
        split_ifs <;> omega
      obtain ⟨L, k', g, hg, hL, hLS⟩ := ih _ hlt c' rfl hc'0
      refine ⟨(S, k) :: L, k', g, hg, fun i => ?_, fun p hp i hi => ?_⟩
      · rw [hcc' i, toricChartProduct_cons, Matrix.mul_apply, Matrix.mulVec, dotProduct,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hL l]
        ring
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact (Finset.mem_filter.mp hi).2
        · exact hsupp i (hLS p hp i hi)

end Charts

end MixedFujita

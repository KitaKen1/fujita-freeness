/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedKoszulCartier
public import MixedFujita.EtaleInverseCartier

/-!
The Cartier isomorphism of a twisted logarithmic de Rham complex on an étale chart (step 10, R2).

On a domain `S` with étale coordinates `y_1, …, y_n` over a field of characteristic `p`, fix the
logarithmic directions `A` and twists `0 ≤ r_j < p` (`j ∈ A`). In the basis `dy_j / y_j` (`j ∈ A`),
`dy_j` (`j ∉ A`) of the logarithmic forms, the de Rham complex of `y^{-r}`-twisted logarithmic
forms is the coordinate model `S ⊗ ⋀Kⁿ` with the operators `y_j ∂_j − r_j` (`j ∈ A`) and `∂_j`
(`j ∉ A`) (`logTwistedPartial`). It is a mixed model of check 477's kind, with homotopy
coefficients `1` and Cartan scalars `0` in the logarithmic directions (`logCoordFun`,
`logCartanScalar`); the hypotheses of the mixed decomposition hold (`logTwistedPartial_comm`,
`logTwistedPartial_mul`, `logEuler_pow_char`, `logPartial_comp_euler_pow_pred`), so every cocycle is
uniquely a form with all mixed weights zero plus a coboundary (`log_etale_cartier_decomposition`).

The forms with all mixed weights zero are `Σ_s c_s y^{β(s)} ⊗ e_s` with `c_s ∈ K·S^p`, where
`β(s)_j = r_j` for `j ∈ A` and `β(s)_j = (p - 1) [j ∈ s]` otherwise (`logEtaleCartierSubspace_iff`,
from the weight decomposition of check 400). Hence the logarithmic inverse Cartier operator
`Σ_s ω_s e_s ↦ Σ_s ω_s^p y^{β(s)} e_s` (`logInverseCartier`) is, over a perfect field, an isomorphism
onto the cohomology (`log_etale_cartier_isomorphism`, as check 401).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Exterior

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}

theorem mixedKoszulWeight_tmul_basis (D : Fin n → S →ₗ[K] S) (x : Fin n → S) (c : Fin n → K)
    (j : Fin n) (a : S) (s : Finset (Fin n)) :
    mixedKoszulWeight D x c j (a ⊗ₜ coordExteriorBasis K n s) =
      (eulerOperator D x j a + ((if j ∈ s then (1 : K) else 0) * c j) • a) ⊗ₜ
        coordExteriorBasis K n s := by
  rw [mixedKoszulWeight_eq_add, LinearMap.add_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.id_apply, coordWedgeContract_basis,
    TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_smul, ← TensorProduct.add_tmul]

end Exterior

section Etale

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) (A : Finset (Fin n))
  (r : Fin n → ℕ)

/-- **The operators of the twisted logarithmic de Rham complex**: `y_j ∂_j − r_j` in the
logarithmic directions, `∂_j` otherwise. -/
noncomputable def logTwistedPartial (j : Fin n) : S →ₗ[K] S :=
  if j ∈ A then
    eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j - ((r j : ℕ) : K) • LinearMap.id
  else etaleCoordPartial y hy j

/-- The homotopy coefficients: `1` in the logarithmic directions, the coordinate otherwise. -/
noncomputable def logCoordFun (j : Fin n) : S := if j ∈ A then 1 else etaleCoordFun y j

variable (K) in
/-- The Cartan scalars: `0` in the logarithmic directions, `1` otherwise. -/
def logCartanScalar (j : Fin n) : K := if j ∈ A then 0 else 1

omit hy in
theorem logCoordFun_of_mem {j : Fin n} (hj : j ∈ A) : logCoordFun y A j = 1 := by
  rw [logCoordFun, ite_eq_left hj]

omit hy in
theorem logCoordFun_of_not_mem {j : Fin n} (hj : j ∉ A) :
    logCoordFun y A j = etaleCoordFun y j := by
  rw [logCoordFun, ite_eq_right hj]

theorem logTwistedPartial_of_mem {j : Fin n} (hj : j ∈ A) :
    logTwistedPartial y hy A r j =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j - ((r j : ℕ) : K) • LinearMap.id := by
  rw [logTwistedPartial, ite_eq_left hj]

theorem logTwistedPartial_of_not_mem {j : Fin n} (hj : j ∉ A) :
    logTwistedPartial y hy A r j = etaleCoordPartial y hy j := by
  rw [logTwistedPartial, ite_eq_right hj]

theorem eulerOperator_logTwisted_of_mem {j : Fin n} (hj : j ∈ A) :
    eulerOperator (logTwistedPartial y hy A r) (logCoordFun y A) j =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j - ((r j : ℕ) : K) • LinearMap.id := by
  refine LinearMap.ext fun a => ?_
  rw [eulerOperator_apply, logCoordFun_of_mem y A hj, one_mul, logTwistedPartial_of_mem y hy A r hj]

theorem eulerOperator_logTwisted_of_not_mem {j : Fin n} (hj : j ∉ A) :
    eulerOperator (logTwistedPartial y hy A r) (logCoordFun y A) j =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j := by
  refine LinearMap.ext fun a => ?_
  rw [eulerOperator_apply, eulerOperator_apply, logCoordFun_of_not_mem y A hj,
    logTwistedPartial_of_not_mem y hy A r hj]

/-- `∂_j (y_i ∂_i a) = y_i ∂_i (∂_j a)` for `i ≠ j`. -/
theorem etaleCoordPartial_euler_comm {i j : Fin n} (hij : i ≠ j) (a : S) :
    etaleCoordPartial y hy j (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) i a) =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) i (etaleCoordPartial y hy j a) := by
  rw [eulerOperator_apply, eulerOperator_apply, etaleCoordPartial_mul y hy j i,
    ite_eq_right (Ne.symm hij), add_zero]
  congr 1
  exact LinearMap.congr_fun (etaleCoordPartial_comm y hy j i) a

theorem logTwistedPartial_comm (i j : Fin n) :
    logTwistedPartial y hy A r i ∘ₗ logTwistedPartial y hy A r j =
      logTwistedPartial y hy A r j ∘ₗ logTwistedPartial y hy A r i := by
  refine LinearMap.ext fun a => ?_
  have hEE := LinearMap.congr_fun (eulerOperator_comm (etaleCoordPartial y hy) (etaleCoordFun y)
    (etaleCoordPartial_comm y hy) (etaleCoordPartial_mul y hy) i j) a
  simp only [LinearMap.comp_apply] at hEE ⊢
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
  · rw [logTwistedPartial_of_mem y hy A r hi, logTwistedPartial_of_mem y hy A r hj]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hEE]
    module
  · have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [logTwistedPartial_of_mem y hy A r hi, logTwistedPartial_of_not_mem y hy A r hj]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
      etaleCoordPartial_euler_comm y hy hij]
  · have hij : j ≠ i := fun h => hi (h ▸ hj)
    rw [logTwistedPartial_of_not_mem y hy A r hi, logTwistedPartial_of_mem y hy A r hj]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
      etaleCoordPartial_euler_comm y hy hij]
  · rw [logTwistedPartial_of_not_mem y hy A r hi, logTwistedPartial_of_not_mem y hy A r hj]
    exact LinearMap.congr_fun (etaleCoordPartial_comm y hy i j) a

theorem logTwistedPartial_mul (i j : Fin n) (a : S) :
    logTwistedPartial y hy A r i (logCoordFun y A j * a) =
      logCoordFun y A j * logTwistedPartial y hy A r i a +
        (if i = j then logCartanScalar K A j • a else 0) := by
  by_cases hj : j ∈ A
  · rw [logCoordFun_of_mem y A hj, one_mul, one_mul, logCartanScalar, ite_eq_left hj, zero_smul,
      ite_self, add_zero]
  · rw [logCoordFun_of_not_mem y A hj, logCartanScalar, ite_eq_right hj, one_smul]
    by_cases hi : i ∈ A
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      rw [logTwistedPartial_of_mem y hy A r hi, ite_eq_right hij, add_zero]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, eulerOperator_apply,
        etaleCoordPartial_mul y hy i j, ite_eq_right hij, add_zero]
      rw [mul_sub, Algebra.smul_def, Algebra.smul_def]
      ring
    · rw [logTwistedPartial_of_not_mem y hy A r hi]
      exact etaleCoordPartial_mul y hy i j a

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

include hp in
theorem logEuler_pow_char (j : Fin n) :
    eulerOperator (logTwistedPartial y hy A r) (logCoordFun y A) j ^ p =
      eulerOperator (logTwistedPartial y hy A r) (logCoordFun y A) j := by
  by_cases hj : j ∈ A
  · rw [eulerOperator_logTwisted_of_mem y hy A r hj]
    have hc : Commute (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j)
        ((-((r j : ℕ) : K)) • (LinearMap.id : S →ₗ[K] S)) :=
      (Commute.one_right _).smul_right _
    have hpE : ((p : ℕ) : Module.End K S) = 0 := by
      rw [← map_natCast (algebraMap K (Module.End K S)), CharP.cast_eq_zero, map_zero]
    have hsub : eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j -
        ((r j : ℕ) : K) • LinearMap.id = eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
          (-((r j : ℕ) : K)) • LinearMap.id := by
      rw [sub_eq_add_neg]
      congr 1
      exact (neg_smul _ _).symm
    rw [hsub, hc.add_pow_prime_eq hp.out, etaleEuler_pow_char y hy p j, smul_pow, linearMap_id_pow,
      neg_pow, neg_one_pow_char K p, natCast_pow_char p (r j), neg_one_mul]
    simp only [hpE, zero_mul, add_zero]
  · rw [eulerOperator_logTwisted_of_not_mem y hy A r hj]
    exact etaleEuler_pow_char y hy p j

omit [CharP K p] in
theorem logCartanScalar_pow (j : Fin n) : logCartanScalar K A j ^ p = logCartanScalar K A j := by
  rw [logCartanScalar]
  split_ifs
  · exact zero_pow hp.out.ne_zero
  · exact one_pow p

include hp in
theorem logPartial_comp_euler_pow_pred [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (j : Fin n) :
    logTwistedPartial y hy A r j ∘ₗ
        (eulerOperator (logTwistedPartial y hy A r) (logCoordFun y A) j ^ (p - 1)) =
      logTwistedPartial y hy A r j := by
  by_cases hj : j ∈ A
  · have h := logEuler_pow_char y hy A r p j
    rw [eulerOperator_logTwisted_of_mem y hy A r hj] at h ⊢
    rw [logTwistedPartial_of_mem y hy A r hj, ← Module.End.mul_eq_comp, ← pow_succ',
      Nat.sub_add_cancel hp.out.one_lt.le, h]
  · rw [eulerOperator_logTwisted_of_not_mem y hy A r hj, logTwistedPartial_of_not_mem y hy A r hj]
    exact etalePartial_comp_euler_pow_pred y hy p hy0 j

include hp in
/-- **The Cartier decomposition of a twisted logarithmic de Rham complex on an étale chart.** -/
theorem log_etale_cartier_decomposition [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : S ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff (logTwistedPartial y hy A r) z = 0) :
    ∃! w : S ⊗[K] CoordExterior K n,
      (∀ j, mixedKoszulWeight (logTwistedPartial y hy A r) (logCoordFun y A) (logCartanScalar K A) j
        w = 0) ∧ z - w ∈ LinearMap.range (koszulDeRhamDiff (logTwistedPartial y hy A r)) :=
  mixedKoszul_cartier_decomposition (logTwistedPartial y hy A r) (logCoordFun y A)
    (logCartanScalar K A) (logTwistedPartial_comm y hy A r) (logTwistedPartial_mul y hy A r) p
    (CharP.cast_eq_zero K p) (logEuler_pow_char y hy A r p) (logCartanScalar_pow A p)
    (logPartial_comp_euler_pow_pred y hy A r p hy0) z hz

/-- The shifts of the weights of `a ⊗ e_s`: `p - r_j` in the logarithmic directions,
`[j ∈ s]` otherwise. -/
def logShift (A : Finset (Fin n)) (r : Fin n → ℕ) (s : Finset (Fin n)) (j : Fin n) : ℕ :=
  if j ∈ A then p - r j else if j ∈ s then 1 else 0

/-- **The logarithmic Cartier exponent** `β(s)`: `r_j` in the logarithmic directions,
`(p - 1) [j ∈ s]` otherwise. -/
noncomputable def logCartierExponent (A : Finset (Fin n)) (r : Fin n → ℕ) (s : Finset (Fin n)) :
    Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if j ∈ A then r j else if j ∈ s then p - 1 else 0

omit hp [CharP K p] in
theorem logCartierExponent_apply (A : Finset (Fin n)) (r : Fin n → ℕ) (s : Finset (Fin n))
    (j : Fin n) :
    logCartierExponent p A r s j = if j ∈ A then r j else if j ∈ s then p - 1 else 0 := by
  simp [logCartierExponent]

include hp in
/-- The exponents `β` with `p ∣ β_j + (shift)` are `p γ + β(s)`. -/
theorem dvd_add_logShift_iff (hr : ∀ j ∈ A, r j < p) (s : Finset (Fin n)) (j : Fin n) (b : ℕ) :
    p ∣ b + logShift p A r s j ↔ ∃ g, b = p * g + logCartierExponent p A r s j := by
  have hp2 := hp.out.two_le
  rw [logCartierExponent_apply, logShift]
  by_cases hjA : j ∈ A
  · have hrj := hr j hjA
    simp only [hjA, ite_true]
    constructor
    · rintro ⟨k, hk⟩
      rcases k with _ | k
      · rw [mul_zero] at hk
        omega
      · rw [Nat.mul_succ] at hk
        exact ⟨k, by omega⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g + 1, by rw [Nat.mul_succ]; omega⟩
  · simp only [hjA, ite_false]
    by_cases hjs : j ∈ s
    · simp only [hjs, ite_true]
      constructor
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · rw [mul_zero] at hk
          omega
        · rw [Nat.mul_succ] at hk
          exact ⟨k, by omega⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g + 1, by rw [Nat.mul_succ]; omega⟩
    · simp only [hjs, ite_false, add_zero]
      exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨g, hg⟩⟩

omit hp in
/-- The mixed weights act on `a ⊗ e_s` by the shifted Euler operators. -/
theorem logWeight_tmul_basis (hr : ∀ j ∈ A, r j < p) (j : Fin n) (a : S) (s : Finset (Fin n)) :
    mixedKoszulWeight (logTwistedPartial y hy A r) (logCoordFun y A) (logCartanScalar K A) j
        (a ⊗ₜ coordExteriorBasis K n s) =
      ((eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
        ((logShift p A r s j : ℕ) : K) • LinearMap.id : S →ₗ[K] S) a) ⊗ₜ coordExteriorBasis K n s := by
  rw [mixedKoszulWeight_tmul_basis, logShift, logCartanScalar]
  by_cases hjA : j ∈ A
  · have hrj := hr j hjA
    rw [eulerOperator_logTwisted_of_mem y hy A r hjA]
    simp only [hjA, ite_true, mul_zero, zero_smul, add_zero, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [Nat.cast_sub hrj.le, CharP.cast_eq_zero K p, zero_sub, neg_smul, sub_eq_add_neg]
  · rw [eulerOperator_logTwisted_of_not_mem y hy A r hjA]
    simp only [hjA, ite_false, mul_one, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply]
    split_ifs <;> simp

include hp in
/-- **Coefficients of the logarithmic Cartier subspace.** If the shifted Euler operators kill `a`,
then `a = c · y^{β(s)}` with `c ∈ K·S^p`. -/
theorem exists_mem_frobeniusSubalgebra_mul_logCartierMonomial [Algebra.FiniteType K S]
    (hr : ∀ j ∈ A, r j < p) (s : Finset (Fin n)) (a : S)
    (ha : ∀ j, (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
      ((logShift p A r s j : ℕ) : K) • LinearMap.id : S →ₗ[K] S) a = 0) :
    ∃ c ∈ frobeniusSubalgebra K S p,
      a = c * y (MvPolynomial.monomial (logCartierExponent p A r s) 1) := by
  classical
  obtain ⟨q, hq⟩ := exists_aeval_frobeniusSubalgebra_eq p y hy a
  have hq' : MvPolynomial.aeval (etaleCoordFun y) q = a := hq
  have hw : ∀ j, (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
      ((logShift p A r s j : ℕ) : K) • LinearMap.id : S →ₗ[K] S)
        (MvPolynomial.aeval (etaleCoordFun y) q) = 0 := fun j => by rw [hq']; exact ha j
  have hY : y (MvPolynomial.monomial (logCartierExponent p A r s) 1) =
      ∏ i, etaleCoordFun y i ^ logCartierExponent p A r s i := by
    rw [coordinate_monomial_eq_prod, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  rw [← hq', aeval_eq_sum_filter_of_shifted_weights y hy p (logShift p A r s) q hw]
  refine Finset.sum_induction _
    (fun x => ∃ c ∈ frobeniusSubalgebra K S p,
      x = c * y (MvPolynomial.monomial (logCartierExponent p A r s) 1))
    (fun x z ⟨c, hc, hx⟩ ⟨d, hd, hz⟩ => ⟨c + d, Subalgebra.add_mem _ hc hd, by rw [hx, hz, add_mul]⟩)
    ⟨0, Subalgebra.zero_mem _, by rw [zero_mul]⟩ fun β hβ => ?_
  have hdec : ∀ i, ∃ g, β i = p * g + logCartierExponent p A r s i := fun i =>
    (dvd_add_logShift_iff A r p hr s i (β i)).mp ((Finset.mem_filter.mp hβ).2 i)
  choose γ hγ using hdec
  refine ⟨(q.coeff β : S) * ∏ i, (etaleCoordFun y i ^ γ i) ^ p,
    Subalgebra.mul_mem _ (q.coeff β).2
      (Subalgebra.prod_mem _ fun i _ => pow_mem_frobeniusSubalgebra p _), ?_⟩
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), hY, mul_assoc,
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hγ i, pow_add, ← pow_mul, mul_comm (γ i) p]

include hp in
/-- The forms `c · y^{β(s)} e_s` with `c ∈ K·S^p` are killed by the shifted Euler operators. -/
theorem logShiftedEuler_logCartierMonomial (hr : ∀ j ∈ A, r j < p) (s : Finset (Fin n))
    (j : Fin n) {c : S} (hc : c ∈ frobeniusSubalgebra K S p) :
    (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
      ((logShift p A r s j : ℕ) : K) • LinearMap.id : S →ₗ[K] S)
        (c * y (MvPolynomial.monomial (logCartierExponent p A r s) 1)) = 0 := by
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    mul_coordinate_monomial_eq_aeval y p _ hc, etaleEuler_aeval_monomial y hy p, ← add_smul,
    ← Nat.cast_add]
  have hdvd : p ∣ logCartierExponent p A r s j + logShift p A r s j :=
    (dvd_add_logShift_iff A r p hr s j _).mpr ⟨0, by rw [mul_zero, zero_add]⟩
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul]

include hp in
/-- **The logarithmic Cartier subspace of an étale chart.** A form of the twisted logarithmic
model is killed by all mixed weights exactly when it is `Σ_s c_s y^{β(s)} ⊗ e_s` with all
`c_s ∈ K·S^p`. -/
theorem logEtaleCartierSubspace_iff [Algebra.FiniteType K S] (hr : ∀ j ∈ A, r j < p)
    (ω : S ⊗[K] CoordExterior K n) :
    (∀ j, mixedKoszulWeight (logTwistedPartial y hy A r) (logCoordFun y A) (logCartanScalar K A) j
        ω = 0) ↔
      ∃ c : Finset (Fin n) → S, (∀ s, c s ∈ frobeniusSubalgebra K S p) ∧
        ω = ∑ s, (c s * y (MvPolynomial.monomial (logCartierExponent p A r s) 1)) ⊗ₜ[K]
          coordExteriorBasis K n s := by
  classical
  constructor
  · intro hω
    have hexp := eq_sum_tmul_coordExteriorBasis ω
    set b := Algebra.TensorProduct.basis S (coordExteriorBasis K n)
    have hcoef : ∀ s j, (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j +
        ((logShift p A r s j : ℕ) : K) • LinearMap.id : S →ₗ[K] S) (b.repr ω s) = 0 := by
      intro s j
      have h := hω j
      rw [hexp, map_sum] at h
      simp only [logWeight_tmul_basis y hy A r p hr] at h
      exact (sum_tmul_coordExteriorBasis_eq_zero_iff _).mp h s
    choose c hc hcω using fun s =>
      exists_mem_frobeniusSubalgebra_mul_logCartierMonomial y hy A r p hr s (b.repr ω s) (hcoef s)
    refine ⟨c, hc, ?_⟩
    conv_lhs => rw [hexp]
    exact Finset.sum_congr rfl fun s _ => by rw [hcω s]
  · rintro ⟨c, hc, rfl⟩ j
    rw [map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [logWeight_tmul_basis y hy A r p hr, logShiftedEuler_logCartierMonomial y hy A r p hr s j (hc s),
      TensorProduct.zero_tmul]

/-- **The logarithmic inverse Cartier operator**: `Σ_s ω_s e_s ↦ Σ_s ω_s^p y^{β(s)} e_s`. -/
noncomputable def logInverseCartier (A : Finset (Fin n)) (r : Fin n → ℕ)
    (ω : S ⊗[K] CoordExterior K n) : S ⊗[K] CoordExterior K n :=
  ∑ s, (coordExteriorCoeff ω s ^ p * y (MvPolynomial.monomial (logCartierExponent p A r s) 1)) ⊗ₜ[K]
    coordExteriorBasis K n s

omit hy in
theorem logInverseCartier_add (ω η : S ⊗[K] CoordExterior K n) :
    logInverseCartier y p A r (ω + η) = logInverseCartier y p A r ω + logInverseCartier y p A r η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [logInverseCartier, coordExteriorCoeff_add,
    add_pow_prime_of_natCast_eq_zero hp.out hpS, add_mul, TensorProduct.add_tmul,
    Finset.sum_add_distrib]

omit hy in
theorem logInverseCartier_sub (ω η : S ⊗[K] CoordExterior K n) :
    logInverseCartier y p A r (ω - η) = logInverseCartier y p A r ω - logInverseCartier y p A r η := by
  have hpS : (p : S) = 0 := natCast_char_eq_zero_of_algebra (K := K) p
  simp only [logInverseCartier, coordExteriorCoeff_sub,
    sub_pow_prime_of_natCast_eq_zero hp.out hpS, sub_mul, TensorProduct.sub_tmul,
    Finset.sum_sub_distrib]

omit hy hp [CharP K p] in
/-- The logarithmic inverse Cartier operator is Frobenius-semilinear. -/
theorem logInverseCartier_smul (a : S) (ω : S ⊗[K] CoordExterior K n) :
    logInverseCartier y p A r (a • ω) = a ^ p • logInverseCartier y p A r ω := by
  simp only [logInverseCartier, coordExteriorCoeff_smul, mul_pow, Finset.smul_sum,
    TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]

omit hy hp [CharP K p] in
theorem coordExteriorCoeff_logInverseCartier (ω : S ⊗[K] CoordExterior K n) (s : Finset (Fin n)) :
    coordExteriorCoeff (logInverseCartier y p A r ω) s =
      coordExteriorCoeff ω s ^ p * y (MvPolynomial.monomial (logCartierExponent p A r s) 1) :=
  coordExteriorCoeff_sum_tmul _ s

/-- The values of the logarithmic inverse Cartier operator are killed by all mixed weights. -/
theorem logInverseCartier_weights [Algebra.FiniteType K S] (hr : ∀ j ∈ A, r j < p)
    (ω : S ⊗[K] CoordExterior K n) (j : Fin n) :
    mixedKoszulWeight (logTwistedPartial y hy A r) (logCoordFun y A) (logCartanScalar K A) j
      (logInverseCartier y p A r ω) = 0 :=
  (logEtaleCartierSubspace_iff y hy A r p hr _).mpr ⟨fun s => coordExteriorCoeff ω s ^ p,
    fun _ => pow_mem_frobeniusSubalgebra p _, rfl⟩ j

/-- The values of the logarithmic inverse Cartier operator are cocycles. -/
theorem logInverseCartier_cocycle [Algebra.FiniteType K S] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (hr : ∀ j ∈ A, r j < p)
    (ω : S ⊗[K] CoordExterior K n) :
    koszulDeRhamDiff (logTwistedPartial y hy A r) (logInverseCartier y p A r ω) = 0 :=
  mixedKoszulDiff_eq_zero_of_weights (logTwistedPartial y hy A r) (logCoordFun y A)
    (logCartanScalar K A) p (logPartial_comp_euler_pow_pred y hy A r p hy0) _
    (logInverseCartier_weights y hy A r p hr ω)

omit hy hp [CharP K p] in
/-- The monomials `y^{β(s)}` are nonzero on a domain with nonzero coordinates. -/
theorem logCartierMonomial_ne_zero [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (s : Finset (Fin n)) : y (MvPolynomial.monomial (logCartierExponent p A r s) 1) ≠ 0 := by
  rw [coordinate_monomial_eq_prod, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hy0 j)

omit hy in
/-- On a domain with nonzero coordinates the logarithmic inverse Cartier operator is injective. -/
theorem logInverseCartier_injective [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) :
    Function.Injective (logInverseCartier y p A r : S ⊗[K] CoordExterior K n → _) := by
  intro ω η h
  rw [← sub_eq_zero]
  apply eq_zero_of_coordExteriorCoeff
  intro s
  have h1 : logInverseCartier y p A r (ω - η) = 0 := by
    rw [logInverseCartier_sub y A r p, h, sub_self]
  have h2 := coordExteriorCoeff_logInverseCartier y A r p (ω - η) s
  rw [h1, coordExteriorCoeff, map_zero, Finsupp.zero_apply] at h2
  exact pow_eq_zero_iff hp.out.ne_zero |>.mp
    ((mul_eq_zero.mp h2.symm).resolve_right (logCartierMonomial_ne_zero y A r p hy0 s))

/-- Over a perfect field every form killed by the mixed weights is a value of the logarithmic
inverse Cartier operator. -/
theorem exists_logInverseCartier_eq [PerfectRing K p] [Algebra.FiniteType K S]
    (hr : ∀ j ∈ A, r j < p) (w : S ⊗[K] CoordExterior K n)
    (hw : ∀ j, mixedKoszulWeight (logTwistedPartial y hy A r) (logCoordFun y A)
      (logCartanScalar K A) j w = 0) :
    ∃ ω, logInverseCartier y p A r ω = w := by
  obtain ⟨a, ha, rfl⟩ := (logEtaleCartierSubspace_iff y hy A r p hr w).mp hw
  choose b hb using fun s => exists_pow_eq_of_mem_frobeniusSubalgebra p (ha s)
  refine ⟨∑ s, b s ⊗ₜ[K] coordExteriorBasis K n s, ?_⟩
  rw [logInverseCartier]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coordExteriorCoeff_sum_tmul, hb s]

/-- **The Cartier isomorphism of a twisted logarithmic de Rham complex on an étale chart.** Over a
perfect field of characteristic `p`, for a domain of finite type with nonzero formally étale
coordinates, logarithmic directions `A` and twists `r_j < p`, every cocycle is `C⁻¹ ω` plus a
coboundary for a unique form `ω`. -/
theorem log_etale_cartier_isomorphism [PerfectRing K p] [Algebra.FiniteType K S] [IsDomain S]
    (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0) (hr : ∀ j ∈ A, r j < p)
    (z : S ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff (logTwistedPartial y hy A r) z = 0) :
    ∃! ω : S ⊗[K] CoordExterior K n,
      z - logInverseCartier y p A r ω ∈
        LinearMap.range (koszulDeRhamDiff (logTwistedPartial y hy A r)) := by
  obtain ⟨w, ⟨hww, hwr⟩, huniq⟩ := log_etale_cartier_decomposition y hy A r p hy0 z hz
  obtain ⟨ω₀, hω₀⟩ := exists_logInverseCartier_eq y hy A r p hr w hww
  refine ⟨ω₀, ?_, fun ω hω => ?_⟩
  · show z - logInverseCartier y p A r ω₀ ∈ _
    rw [hω₀]
    exact hwr
  have h := huniq (logInverseCartier y p A r ω) ⟨logInverseCartier_weights y hy A r p hr ω, hω⟩
  exact logInverseCartier_injective y A r p hy0 (h.trans hω₀.symm)

end Etale

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCModelPrimeOrders
public import MixedFujita.RationalIsolationArithmetic
public import MixedFujita.PrincipalizedIdealCoefficients

/-!
The coefficient comparison (28)–(29) of section 6.2 of the manuscript on actual models (step 12).

Let X be smooth over a field with a simple normal crossing family ξ_j, a boundary B supported on
it with coefficients below the denominator d, and Cartier divisors D_i supported on the family
with nonnegative coefficients. Let ρ : T → X be a birational morphism from a smooth T and t a
codimension-one point of T, with log discrepancy A_t = (d + coefficient of the discrepancy
divisor at t)/d and v_i the coefficient of ρ*D_i at t. Let c_i > 0 and q⁰_i ≥ 0 be real numbers
with c · q⁰ = 1 such that, for every member ξ_j whose closure contains ρ(t), the profile
z_j = (coefficient of D_i at ξ_j / log discrepancy of ξ_j)_i satisfies c · z_j ≤ 1. Let g be a
real number with g ≤ (M/q⁰_i) v_i for all i with q⁰_i > 0 (the coefficient at t of the divisor G
of the principalized ideal). Then, for 0 ≤ η ≤ 1,

  (1 − η) Σ_i c_i v_i + (η/M) g ≤ A_t,

and for 0 < η < 1 equality holds only if v_i = A_t q⁰_i for all i; conversely this profile and
g = (M/q⁰_k) v_k for some k give equality. The proof combines the orders of the family along t
with elementary inequalities; no division by the retraction r_t is needed.
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

section Arithmetic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The chain g/M ≤ min ≤ Σ_{q⁰_i > 0} c_i v_i ≤ c · v ≤ Σ_j A_j o_j for a vector v = e · o of
coefficients computed from orders o_j ≥ 0, when c · e_j ≤ A_j for every j with o_j ≠ 0. -/
theorem isolation_chain_of_orders {c q₀ v : ι → ℝ} {e : ι → κ → ℝ} {Aj o : κ → ℝ}
    (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hI : (profileSupport q₀).Nonempty) (ho : ∀ j, 0 ≤ o j) (he : ∀ i j, 0 ≤ e i j)
    (hv : ∀ i, v i = ∑ j, e i j * o j) (hpoly : ∀ j, o j ≠ 0 → ∑ i, c i * e i j ≤ Aj j)
    {M : ℝ} (hM : 0 < M) (g : ℝ) (hg : ∀ i ∈ profileSupport q₀, g ≤ M / q₀ i * v i) :
    (∀ i, 0 ≤ v i) ∧
      g / M ≤ (profileSupport q₀).inf' hI (fun i => v i / q₀ i) ∧
      (profileSupport q₀).inf' hI (fun i => v i / q₀ i) ≤ ∑ i ∈ profileSupport q₀, c i * v i ∧
      ∑ i ∈ profileSupport q₀, c i * v i ≤ ∑ i, c i * v i ∧
      ∑ i, c i * v i ≤ ∑ j, Aj j * o j := by
  have hv0 : ∀ i, 0 ≤ v i := fun i => by
    rw [hv i]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (he i j) (ho j)
  refine ⟨hv0, ?_, isolation_min_ratio_le hc hq₀ hcq₀ hI, isolation_partial_le_dot hc hv0 _, ?_⟩
  · apply Finset.le_inf'
    intro i hi
    have hpos := mem_profileSupport.mp hi
    rw [div_le_iff₀ hM]
    calc g ≤ M / q₀ i * v i := hg i hi
      _ = v i / q₀ i * M := by field_simp
  · calc ∑ i, c i * v i = ∑ j, (∑ i, c i * e i j) * o j := by
          simp only [hv, Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ j, Aj j * o j := by
          apply Finset.sum_le_sum
          intro j _
          by_cases hoj : o j = 0
          · rw [hoj, mul_zero, mul_zero]
          · exact mul_le_mul_of_nonneg_right (hpoly j hoj) (ho j)

/-- §6.2 (28) from orders: (1 − η) c · v + (η/M) g ≤ A. -/
theorem isolation_coefficient_le_of_orders {c q₀ v : ι → ℝ} {e : ι → κ → ℝ} {Aj o : κ → ℝ}
    (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hI : (profileSupport q₀).Nonempty) (ho : ∀ j, 0 ≤ o j) (he : ∀ i j, 0 ≤ e i j)
    (hv : ∀ i, v i = ∑ j, e i j * o j) (hpoly : ∀ j, o j ≠ 0 → ∑ i, c i * e i j ≤ Aj j)
    {A : ℝ} (hRA : ∑ j, Aj j * o j ≤ A) {M η : ℝ} (hM : 0 < M) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (g : ℝ) (hg : ∀ i ∈ profileSupport q₀, g ≤ M / q₀ i * v i) :
    (1 - η) * ∑ i, c i * v i + η / M * g ≤ A := by
  obtain ⟨-, h1, h2, h3, h4⟩ := isolation_chain_of_orders hc hq₀ hcq₀ hI ho he hv hpoly hM g hg
  have hgX : g / M ≤ ∑ i, c i * v i := h1.trans (h2.trans h3)
  have hXA : ∑ i, c i * v i ≤ A := h4.trans hRA
  have hmul := mul_le_mul_of_nonneg_left hgX hη0
  have hmul' := mul_le_mul_of_nonneg_left hXA (sub_nonneg.mpr hη1)
  calc (1 - η) * ∑ i, c i * v i + η / M * g
      = (1 - η) * ∑ i, c i * v i + η * (g / M) := by ring
    _ ≤ (1 - η) * A + η * ∑ i, c i * v i := by linarith
    _ ≤ (1 - η) * A + η * A := by nlinarith [mul_le_mul_of_nonneg_left hXA hη0]
    _ = A := by ring

/-- §6.2 (29) from orders: for 0 < η < 1, equality in (28) forces the profile v = A q⁰. -/
theorem isolation_profile_of_coefficient_eq_of_orders {c q₀ v : ι → ℝ} {e : ι → κ → ℝ}
    {Aj o : κ → ℝ} (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hI : (profileSupport q₀).Nonempty) (ho : ∀ j, 0 ≤ o j) (he : ∀ i j, 0 ≤ e i j)
    (hv : ∀ i, v i = ∑ j, e i j * o j) (hpoly : ∀ j, o j ≠ 0 → ∑ i, c i * e i j ≤ Aj j)
    {A : ℝ} (hRA : ∑ j, Aj j * o j ≤ A) {M η : ℝ} (hM : 0 < M) (hη0 : 0 < η) (hη1 : η < 1)
    (g : ℝ) (hg : ∀ i ∈ profileSupport q₀, g ≤ M / q₀ i * v i)
    (heq : (1 - η) * ∑ i, c i * v i + η / M * g = A) : ∀ i, v i = A * q₀ i := by
  classical
  obtain ⟨hv0, h1, h2, h3, h4⟩ :=
    isolation_chain_of_orders hc hq₀ hcq₀ hI ho he hv hpoly hM g hg
  set X := ∑ i, c i * v i with hX
  set XI := ∑ i ∈ profileSupport q₀, c i * v i with hXI
  set μ := (profileSupport q₀).inf' hI (fun i => v i / q₀ i) with hμ
  have hXA : X ≤ A := h4.trans hRA
  have hgA : g / M ≤ A := h1.trans (h2.trans (h3.trans hXA))
  have heq' : (1 - η) * X + η * (g / M) = A := by
    rw [← heq]
    ring
  have ht1 : 0 ≤ (1 - η) * (A - X) := mul_nonneg (by linarith) (by linarith)
  have ht2 : 0 ≤ η * (A - g / M) := mul_nonneg hη0.le (by linarith)
  have hsum0 : (1 - η) * (A - X) + η * (A - g / M) = 0 := by
    rw [← heq']
    ring
  have hz1 : (1 - η) * (A - X) = 0 := by linarith
  have hz2 : η * (A - g / M) = 0 := by linarith
  have hXeq : X = A := by
    have := (mul_eq_zero.mp hz1).resolve_left (by linarith)
    linarith
  have hgeq : g / M = A := by
    have := (mul_eq_zero.mp hz2).resolve_left hη0.ne'
    linarith
  have hμeq : μ = A := le_antisymm (h2.trans (h3.trans hXA)) (hgeq ▸ h1)
  have hXIeq : XI = A := le_antisymm (h3.trans hXA) (hμeq ▸ h2)
  have hsuppsum : ∑ i ∈ profileSupport q₀, c i * q₀ i = 1 := by
    rw [← hcq₀]
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have h0 : q₀ i = 0 :=
      le_antisymm (not_lt.mp fun h => hi (mem_profileSupport.mpr h)) (hq₀ i)
    rw [h0, mul_zero]
  -- on the support the profile is A q⁰
  have hge : ∀ i ∈ profileSupport q₀, A * q₀ i ≤ v i := by
    intro i hi
    have hpos := mem_profileSupport.mp hi
    have hle : μ ≤ v i / q₀ i := Finset.inf'_le _ hi
    rw [hμeq, le_div_iff₀ hpos] at hle
    exact hle
  have hzero : ∑ i ∈ profileSupport q₀, c i * (v i - A * q₀ i) = 0 := by
    have : ∑ i ∈ profileSupport q₀, c i * (v i - A * q₀ i) =
        XI - A * ∑ i ∈ profileSupport q₀, c i * q₀ i := by
      rw [hXI, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hsuppsum, hXIeq]
    ring
  have hterm : ∀ i ∈ profileSupport q₀, c i * (v i - A * q₀ i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i hi =>
      mul_nonneg (hc i).le (sub_nonneg.mpr (hge i hi))).mp hzero
  -- off the support the coefficients vanish
  have hcompl : ∑ i ∈ Finset.univ \ profileSupport q₀, c i * v i = 0 := by
    have hsplit := Finset.sum_sdiff (f := fun i => c i * v i)
      (Finset.subset_univ (profileSupport q₀))
    have hXuniv : ∑ i ∈ (Finset.univ : Finset ι), c i * v i = X := rfl
    rw [hXuniv, ← hXI, hXIeq, hXeq] at hsplit
    linarith
  have hterm' : ∀ i ∈ Finset.univ \ profileSupport q₀, c i * v i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (hv0 i)).mp hcompl
  intro i
  by_cases hi : i ∈ profileSupport q₀
  · have h := (mul_eq_zero.mp (hterm i hi)).resolve_left (hc i).ne'
    linarith
  · have h := (mul_eq_zero.mp (hterm' i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩))).resolve_left
      (hc i).ne'
    have h0 : q₀ i = 0 :=
      le_antisymm (not_lt.mp fun h => hi (mem_profileSupport.mpr h)) (hq₀ i)
    rw [h, h0, mul_zero]

omit [Fintype κ] in
/-- Conversely the profile v = A q⁰, with g attaining one of the bounds (M/q⁰_k) v_k, gives
equality in (28). -/
theorem isolation_coefficient_eq_of_profile {c q₀ v : ι → ℝ} (hcq₀ : ∑ i, c i * q₀ i = 1)
    {A M η : ℝ} (hM : 0 < M) (hprof : ∀ i, v i = A * q₀ i) (g : ℝ)
    (hg : ∃ k ∈ profileSupport q₀, g = M / q₀ k * v k) :
    (1 - η) * ∑ i, c i * v i + η / M * g = A := by
  obtain ⟨k, hk, hgk⟩ := hg
  have hpos := mem_profileSupport.mp hk
  have hgA : g = M * A := by
    rw [hgk, hprof k]
    field_simp
  have hsum : ∑ i, c i * v i = A := by
    have : ∑ i, c i * v i = A * ∑ i, c i * q₀ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hprof i]; ring
    rw [this, hcq₀, mul_one]
  rw [hsum, hgA]
  field_simp
  ring

end Arithmetic

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The real data attached to a prime divisor of a smooth birational model of a simple normal
crossing pair and to divisors supported on the family: nonnegative orders o_j of the family along
the prime, vanishing unless the closure of ξ_j contains the image of the prime, computing the
coefficients of the pullbacks, and with Σ_j (log discrepancy of ξ_j) o_j at most the log
discrepancy of the prime. -/
theorem exists_real_snc_orders_at_prime {ι : Type*} {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) :
    ∃ o : Fin r → ℝ, (∀ j, 0 ≤ o j) ∧
      (∀ j, o j ≠ 0 → ρ (t : T) ∈ closure ({ξ j} : Set X)) ∧
      (∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) =
        ∑ j, (cartierCoefficient (Dv i) (ξ j) : ℝ) * o j) ∧
      ∑ j, ((d : ℝ) - cartierCoefficient B (ξ j)) / d * o j ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T)) / d := by
  obtain ⟨o, ho, hosupp, hpull, hdisc⟩ := exists_snc_orders_at_prime ρ hρ ξ hinj hξ hsnc t
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨fun j => (o j : ℝ), fun j => ?_, fun j hj => ?_, fun i => ?_, ?_⟩
  · change (0 : ℝ) ≤ (o j : ℝ)
    exact_mod_cast ho j
  · apply hosupp j
    intro h0
    apply hj
    change ((o j : ℤ) : ℝ) = 0
    rw [h0, Int.cast_zero]
  · rw [hpull (Dv i) (hD i)]
    push_cast
    rfl
  · have h := hdisc c₀ f₀ d B hB c'₀
    have h' : (d : ℝ) * ∑ j, (o j : ℝ) - ∑ j, (cartierCoefficient B (ξ j) : ℝ) * (o j : ℝ) ≤
        (d : ℝ) + (cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T) : ℝ) := by
      exact_mod_cast h
    rw [le_div_iff₀ hdpos]
    refine le_trans (le_of_eq ?_) h'
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by field_simp

/-- §6.2 (28) on an actual model: the coefficient of Ψ at a prime divisor of a smooth birational
model of a simple normal crossing pair is at most the log discrepancy of the prime. -/
theorem isolation_coefficient_le_on_model {ι : Type*} [Fintype ι] {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j))
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) {c q₀ : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1) (hI : (profileSupport q₀).Nonempty)
    (hpoly : ∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    {M η : ℝ} (hM : 0 < M) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (g : ℝ)
    (hg : ∀ i ∈ profileSupport q₀,
      g ≤ M / q₀ i * cartierCoefficient (cartierPullback ρ (Dv i)) (t : T)) :
    (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
        η / M * g ≤
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T)) / d := by
  obtain ⟨o, ho, hosupp, hpull, hRA⟩ :=
    exists_real_snc_orders_at_prime ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB Dv hD c'₀ t
  exact isolation_coefficient_le_of_orders (e := fun i j => (cartierCoefficient (Dv i) (ξ j) : ℝ))
    (Aj := fun j => ((d : ℝ) - cartierCoefficient B (ξ j)) / d) hc hq₀ hcq₀ hI ho
    (fun i j => by exact_mod_cast hDnn i j) hpull (fun j hj => hpoly j (hosupp j hj)) hRA hM hη0
    hη1 g hg

/-- §6.2 (29) on an actual model: for 0 < η < 1, equality in (28) at a prime divisor forces its
profile to be q⁰: the coefficient of the pullback of every D_i is the log discrepancy of the
prime times q⁰_i. -/
theorem isolation_profile_of_coefficient_eq_on_model {ι : Type*} [Fintype ι] {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j))
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) {c q₀ : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1) (hI : (profileSupport q₀).Nonempty)
    (hpoly : ∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    {M η : ℝ} (hM : 0 < M) (hη0 : 0 < η) (hη1 : η < 1) (g : ℝ)
    (hg : ∀ i ∈ profileSupport q₀,
      g ≤ M / q₀ i * cartierCoefficient (cartierPullback ρ (Dv i)) (t : T))
    (heq : (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
        η / M * g =
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T)) / d) :
    ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) =
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T)) / d * q₀ i := by
  obtain ⟨o, ho, hosupp, hpull, hRA⟩ :=
    exists_real_snc_orders_at_prime ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB Dv hD c'₀ t
  exact isolation_profile_of_coefficient_eq_of_orders
    (e := fun i j => (cartierCoefficient (Dv i) (ξ j) : ℝ))
    (Aj := fun j => ((d : ℝ) - cartierCoefficient B (ξ j)) / d) hc hq₀ hcq₀ hI ho
    (fun i j => by exact_mod_cast hDnn i j) hpull (fun j hj => hpoly j (hosupp j hj)) hRA hM hη0
    hη1 g hg heq

/-- §6.2 (28)–(29) on a principalizing model. Let G be the effective Cartier divisor of T whose
ideal sheaf is the inverse image of the sum of the ideal sheaves of the divisors n_i D_i, for the
indices i with q⁰_i > 0, where n_i = M/q⁰_i. Then the coefficient of
Ψ = (1 − η) Σ_i c_i ρ*D_i + (η/M) G at every prime divisor of T is at most the log discrepancy
of the prime, and for 0 < η < 1 equality holds exactly for the primes with profile q⁰. -/
theorem isolation_coefficient_on_principalized_model {ι : Type*} [Fintype ι] {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j))
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) {c q₀ : ι → ℝ} (hc : ∀ i, 0 < c i)
    (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1) (hI : (profileSupport q₀).Nonempty)
    (hpoly : ∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    {M η : ℝ} (hM : 0 < M) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (nn : ι → ℕ)
    (hnn : ∀ i ∈ profileSupport q₀, (nn i : ℝ) = M / q₀ i)
    (hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hGcI : effectiveCartierIdealSheaf Gc hGc =
      (⨆ k : {i // i ∈ profileSupport q₀},
        effectiveCartierIdealSheaf (nn k.1 • Dv k.1) (hAeff k)).comap ρ) :
    (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
        η / M * (cartierCoefficient Gc (t : T) : ℝ) ≤
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T)) / d ∧
    (0 < η → η < 1 →
      ((1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / M * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T)) / d ↔
      ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          c'₀ etaleCharts_cover) (t : T)) / d * q₀ i)) := by
  obtain ⟨hle, k, hk⟩ :=
    cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ
      (fun k : {i // i ∈ profileSupport q₀} => nn k.1 • Dv k.1) hAeff Gc hGc hGcI (t : T)
  have hcoef : ∀ i, (cartierCoefficient (cartierPullback ρ (nn i • Dv i)) (t : T) : ℝ) =
      (nn i : ℝ) * cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) := by
    intro i
    simp only [cartierPullback_nsmul, cartierCoefficient_nsmul, Int.cast_mul, Int.cast_natCast]
  have hg : ∀ i ∈ profileSupport q₀, (cartierCoefficient Gc (t : T) : ℝ) ≤
      M / q₀ i * cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) := by
    intro i hi
    have h' : (cartierCoefficient Gc (t : T) : ℝ) ≤
        (cartierCoefficient (cartierPullback ρ (nn i • Dv i)) (t : T) : ℝ) := by
      exact_mod_cast hle ⟨i, hi⟩
    rw [hcoef i, hnn i hi] at h'
    exact h'
  have hgk : ∃ i ∈ profileSupport q₀, (cartierCoefficient Gc (t : T) : ℝ) =
      M / q₀ i * cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) := by
    refine ⟨k.1, k.2, ?_⟩
    have h' : (cartierCoefficient Gc (t : T) : ℝ) =
        (cartierCoefficient (cartierPullback ρ (nn k.1 • Dv k.1)) (t : T) : ℝ) := by
      exact_mod_cast hk
    rw [h', hcoef k.1, hnn k.1 k.2]
  exact ⟨isolation_coefficient_le_on_model ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB Dv hD hDnn c'₀ t
      hc hq₀ hcq₀ hI hpoly hM hη0 hη1 _ hg,
    fun hη0' hη1' => ⟨fun heq => isolation_profile_of_coefficient_eq_on_model ρ hρ ξ hinj hξ hsnc
        c₀ f₀ d hd B hB Dv hD hDnn c'₀ t hc hq₀ hcq₀ hI hpoly hM hη0' hη1' _ hg heq,
      fun hprof => isolation_coefficient_eq_of_profile hcq₀ hM hprof _ hgk⟩⟩

end Model

end MixedFujita

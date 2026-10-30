/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MonomialValuationBound
public import MixedFujita.LinearSystemCommonDenominator
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
lct ≥ 1/mult for monomial valuations on other smooth models, through the Jacobian. Let
ψ : K[[x]] → K[[z]] be a K-algebra map with ψ(x_i) in the maximal ideal, such as the map of
completed local rings of a morphism of smooth varieties at p ↦ z in regular coordinates,
J = (∂_j ψ(x_i)) its Jacobian, and v the monomial valuation with weights w in the coordinates z.
Then A(v) = Σ w_j + v(det J) is the log discrepancy of v over the target. In characteristic zero
the chain rule ∂_j ψ(G) = Σ_i ψ(∂_i G) J_ij holds for every G: Euler's identity writes a series
without constant term as Σ_i x_i ∂_i G', so ψ preserves the order, and the defect of the chain
rule vanishes on monomials and has arbitrarily large order on the tails. Multiplying by the
adjugate gives det J · ψ(∂_i G) = Σ_j ∂_j ψ(G) adj(J)_ji, so one derivative lowers v by at most
max w + v(det J). Some derivative of order ord(f) of f is a unit, whose image has v = 0; hence
v(ψ f) ≤ ord(f) (max w + v(det J)) ≤ A(v) ord(f). This is lct_z(f) ≥ 1/mult_z(f) for these test
valuations, without resolution of singularities, inversion of adjunction or integration.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries Finset

variable {σ K : Type*} [Field K]

/-- A partial derivative lowers the weighted order by at most the weight of the variable. -/
theorem weightedOrder_le_pderiv_add (w : σ → ℕ) (j : σ) (H : MvPowerSeries σ K) :
    H.weightedOrder w ≤ (pderiv j H).weightedOrder w + w j := by
  by_cases h0 : pderiv j H = 0
  · rw [h0, weightedOrder_zero, top_add]
    exact le_top
  · have hfin := (ne_zero_iff_weightedOrder_finite w).mp h0
    obtain ⟨d, hd, hdw⟩ := exists_coeff_ne_zero_and_weightedOrder w hfin
    rw [coeff_pderiv] at hd
    have hc : coeff (d + Finsupp.single j 1) H ≠ 0 := left_ne_zero_of_mul hd
    calc H.weightedOrder w ≤ (Finsupp.weight w (d + Finsupp.single j 1) : ℕ∞) :=
          weightedOrder_le w hc
      _ = (Finsupp.weight w d : ℕ∞) + w j := by
          rw [map_add, Finsupp.weight_single, smul_eq_mul, one_mul, Nat.cast_add]
      _ = (pderiv j H).weightedOrder w + w j := by rw [hdw]

theorem order_le_pderiv_add_one (j : σ) (H : MvPowerSeries σ K) :
    H.order ≤ (pderiv j H).order + 1 := by
  have h := weightedOrder_le_pderiv_add (fun _ : σ => 1) j H
  simp only [Nat.cast_one] at h
  exact h

theorem enat_le_of_succ_le_add_one {N : ℕ} {x : ℕ∞} (h : ((N + 1 : ℕ) : ℕ∞) ≤ x + 1) :
    (N : ℕ∞) ≤ x := by
  induction x using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    have h' : N + 1 ≤ m + 1 := by exact_mod_cast h
    exact_mod_cast Nat.le_of_succ_le_succ h'

theorem le_weightedOrder_sum (w : σ → ℕ) {ι : Type*} (s : Finset ι) (t : ι → MvPowerSeries σ K)
    {a : ℕ∞} (h : ∀ j ∈ s, a ≤ (t j).weightedOrder w) : a ≤ (∑ j ∈ s, t j).weightedOrder w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (le_min (h j (mem_insert_self j s)) (ih fun l hl => h l (mem_insert_of_mem hl))).trans
      (min_weightedOrder_le_add w)

theorem le_weightedOrder_sum_add (w : σ → ℕ) {ι : Type*} (s : Finset ι)
    (t : ι → MvPowerSeries σ K) {a M : ℕ∞} (h : ∀ j ∈ s, a ≤ (t j).weightedOrder w + M) :
    a ≤ (∑ j ∈ s, t j).weightedOrder w + M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := h j (mem_insert_self j s)
    have h2 := ih fun l hl => h l (mem_insert_of_mem hl)
    calc a ≤ min ((t j).weightedOrder w) ((∑ l ∈ s, t l).weightedOrder w) + M := by
          rcases min_choice ((t j).weightedOrder w) ((∑ l ∈ s, t l).weightedOrder w) with hm | hm <;>
            rw [hm] <;> assumption
      _ ≤ (t j + ∑ l ∈ s, t l).weightedOrder w + M := by
          gcongr
          exact min_weightedOrder_le_add w

section Taylor

/-- The iterated partial derivative along a list of variables. -/
noncomputable def iteratedPDeriv : List σ → MvPowerSeries σ K → MvPowerSeries σ K
  | [], f => f
  | i :: L, f => pderiv i (iteratedPDeriv L f)

/-- The exponent of a list of variables. -/
noncomputable def listExponent : List σ → σ →₀ ℕ
  | [] => 0
  | i :: L => Finsupp.single i 1 + listExponent L

theorem listExponent_degree (L : List σ) : (listExponent L).degree = L.length := by
  induction L with
  | nil =>
    change (0 : σ →₀ ℕ).degree = 0
    exact map_zero _
  | cons i L ih =>
    change (Finsupp.single i 1 + listExponent L).degree = L.length + 1
    rw [map_add, Finsupp.degree_single, ih, Nat.add_comm]

theorem exists_listExponent_eq : ∀ (k : ℕ) (d : σ →₀ ℕ), d.degree = k →
    ∃ L : List σ, listExponent L = d := by
  classical
  intro k
  induction k with
  | zero =>
    intro d hd
    exact ⟨[], ((Finsupp.degree_eq_zero_iff d).mp hd).symm⟩
  | succ k ih =>
    intro d hd
    have hsupp : d.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      rintro rfl
      have h0 : (0 : σ →₀ ℕ).degree = 0 := map_zero _
      omega
    obtain ⟨i, hi⟩ := hsupp
    have hle : Finsupp.single i 1 ≤ d :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
    set d' := d - Finsupp.single i 1 with hd'
    have hsum : Finsupp.single i 1 + d' = d := add_tsub_cancel_of_le hle
    have hdeg : d'.degree = k := by
      have h2 := congrArg Finsupp.degree hsum
      rw [map_add, Finsupp.degree_single, hd] at h2
      omega
    obtain ⟨L, hL⟩ := ih d' hdeg
    exact ⟨i :: L, by change Finsupp.single i 1 + listExponent L = d; rw [hL, hsum]⟩

theorem coeff_iteratedPDeriv (L : List σ) (f : MvPowerSeries σ K) (n : σ →₀ ℕ) :
    ∃ c : ℕ, 0 < c ∧ coeff n (iteratedPDeriv L f) = (c : K) * coeff (n + listExponent L) f := by
  induction L generalizing n with
  | nil => exact ⟨1, one_pos, by simp [iteratedPDeriv, listExponent]⟩
  | cons i L ih =>
    obtain ⟨c, hc, hcoeff⟩ := ih (n + Finsupp.single i 1)
    refine ⟨c * (n i + 1), Nat.mul_pos hc (Nat.succ_pos _), ?_⟩
    change coeff n (pderiv i (iteratedPDeriv L f)) =
      ((c * (n i + 1) : ℕ) : K) * coeff (n + (Finsupp.single i 1 + listExponent L)) f
    rw [coeff_pderiv, hcoeff, ← add_assoc]
    push_cast
    ring

/-- In characteristic zero some derivative of order ord(f) of a nonzero f is a unit. -/
theorem exists_iteratedPDeriv_isUnit [CharZero K] {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    ∃ L : List σ, (L.length : ℕ∞) = f.order ∧ IsUnit (iteratedPDeriv L f) := by
  have hfin : (f.order.toNat : ℕ∞) = f.order := by
    apply ENat.natCast_toNat
    rwa [ne_eq, order_eq_top_iff]
  obtain ⟨p, hp, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  obtain ⟨L, hL⟩ := exists_listExponent_eq p.degree p rfl
  refine ⟨L, ?_, ?_⟩
  · rw [← hdeg, ← hL, listExponent_degree]
  · obtain ⟨c, hc, hcoeff⟩ := coeff_iteratedPDeriv L f 0
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, hcoeff, zero_add, hL]
    exact (mul_ne_zero (by exact_mod_cast hc.ne') hp).isUnit

end Taylor

section Chain

variable [Fintype σ]

omit [Fintype σ] in
theorem coeff_X_mul_pderiv (G : MvPowerSeries σ K) (d : σ →₀ ℕ) (i : σ) :
    coeff d (X i * pderiv i G) = (d i : K) * coeff d G := by
  classical
  rw [X_def, coeff_monomial_mul]
  by_cases hi : Finsupp.single i 1 ≤ d
  · rw [ite_eq_left hi, one_mul, coeff_pderiv, tsub_add_cancel_of_le hi]
    have h1 : 1 ≤ d i := by simpa using Finsupp.single_le_iff.mp hi
    have h2 : (d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 = d i := by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    rw [mul_comm]
    congr 1
    have h3 : (((d - Finsupp.single i 1 : σ →₀ ℕ) i + 1 : ℕ) : K) = (d i : K) := by rw [h2]
    rw [← h3, Nat.cast_add, Nat.cast_one]
  · rw [ite_eq_right hi]
    have h0 : d i = 0 := by
      by_contra h
      exact hi (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))
    rw [h0, Nat.cast_zero, zero_mul]

/-- Euler's identity on coefficients. -/
theorem coeff_euler (G : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    coeff d (∑ i, X i * pderiv i G) = (d.degree : K) * coeff d G := by
  rw [map_sum]
  simp_rw [coeff_X_mul_pderiv]
  rw [← Finset.sum_mul, Finsupp.degree_eq_sum, Nat.cast_sum]

/-- A power series without constant term is the Euler operator of a series of no smaller
order. -/
theorem exists_euler_preimage [CharZero K] {G : MvPowerSeries σ K} (hG : constantCoeff G = 0) :
    ∃ G' : MvPowerSeries σ K, G.order ≤ G'.order ∧ G = ∑ i, X i * pderiv i G' := by
  let G' : MvPowerSeries σ K := fun d => (d.degree : K)⁻¹ * coeff d G
  have hG' : ∀ d, coeff d G' = (d.degree : K)⁻¹ * coeff d G := fun d => rfl
  refine ⟨G', ?_, ?_⟩
  · apply le_order
    intro d hd
    rw [hG', coeff_of_lt_order hd, mul_zero]
  · ext d
    rw [coeff_euler, hG']
    by_cases hd : d.degree = 0
    · have h0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp hd
      subst h0
      simp [coeff_zero_eq_constantCoeff_apply, hG]
    · have h : (d.degree : K) ≠ 0 := by exact_mod_cast hd
      rw [mul_inv_cancel_left₀ h]

variable (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)

/-- A K-algebra map sending the variables into the maximal ideal does not lower the order. -/
theorem order_le_order_algHom [CharZero K] (hψ : ∀ i, constantCoeff (ψ (X i)) = 0) :
    ∀ (k : ℕ) (G : MvPowerSeries σ K), (k : ℕ∞) ≤ G.order → (k : ℕ∞) ≤ (ψ G).order := by
  intro k
  induction k with
  | zero =>
    intro G _
    simp
  | succ k ih =>
    intro G hG
    have hc : constantCoeff G = 0 := by
      rw [← one_le_order_iff_constCoeff_eq_zero]
      exact le_trans (by exact_mod_cast Nat.succ_pos k) hG
    obtain ⟨G', hG'ord, hG'eq⟩ := exists_euler_preimage hc
    rw [hG'eq, map_sum]
    apply le_weightedOrder_sum (fun _ => 1)
    intro i _
    rw [map_mul]
    have hX : (1 : ℕ∞) ≤ (ψ (X i)).order := one_le_order_iff_constCoeff_eq_zero.mpr (hψ i)
    have hd : (k : ℕ∞) ≤ (pderiv i G').order :=
      enat_le_of_succ_le_add_one ((hG.trans hG'ord).trans (order_le_pderiv_add_one i G'))
    have hk := ih _ hd
    calc ((k + 1 : ℕ) : ℕ∞) = 1 + k := by push_cast; ring
      _ ≤ (ψ (X i)).order + (ψ (pderiv i G')).order := add_le_add hX hk
      _ ≤ (ψ (X i) * ψ (pderiv i G')).order := le_order_mul

/-- The Jacobian matrix J i j = ∂_j ψ(X_i). -/
noncomputable def powerSeriesJacobian : Matrix σ σ (MvPowerSeries σ K) :=
  Matrix.of fun i j => pderiv j (ψ (X i))

/-- The chain rule for ψ at G. -/
def PowerSeriesChainRuleAt (G : MvPowerSeries σ K) : Prop :=
  ∀ j, pderiv j (ψ G) = ∑ i, ψ (pderiv i G) * powerSeriesJacobian ψ i j

theorem chainRuleAt_zero : PowerSeriesChainRuleAt ψ 0 := by
  intro j
  simp

theorem chainRuleAt_add {G H : MvPowerSeries σ K} (hG : PowerSeriesChainRuleAt ψ G)
    (hH : PowerSeriesChainRuleAt ψ H) : PowerSeriesChainRuleAt ψ (G + H) := by
  intro j
  rw [map_add, map_add, hG j, hH j, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_add, map_add, add_mul]

theorem chainRuleAt_smul (a : K) {G : MvPowerSeries σ K} (hG : PowerSeriesChainRuleAt ψ G) :
    PowerSeriesChainRuleAt ψ (a • G) := by
  intro j
  simp only [map_smul, Derivation.map_smul, hG j, Finset.smul_sum, smul_mul_assoc]

theorem chainRuleAt_mul {G H : MvPowerSeries σ K} (hG : PowerSeriesChainRuleAt ψ G)
    (hH : PowerSeriesChainRuleAt ψ H) : PowerSeriesChainRuleAt ψ (G * H) := by
  intro j
  rw [map_mul, Derivation.leibniz, hG j, hH j, smul_eq_mul, smul_eq_mul, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul]
  ring

theorem chainRuleAt_X [DecidableEq σ] (l : σ) : PowerSeriesChainRuleAt ψ (X l) := by
  intro j
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, map_one, one_mul]
    rfl
  · intro i _ hil
    rw [pderiv_X_of_ne (Ne.symm hil), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem chainRuleAt_monomial_list [DecidableEq σ] (L : List σ) :
    PowerSeriesChainRuleAt ψ (monomial (listExponent L) (1 : K)) := by
  induction L with
  | nil =>
    change PowerSeriesChainRuleAt ψ (monomial (0 : σ →₀ ℕ) (1 : K))
    rw [monomial_zero_one]
    intro j
    simp
  | cons i L ih =>
    have h : monomial (listExponent (i :: L)) (1 : K) = X i * monomial (listExponent L) 1 := by
      change monomial (Finsupp.single i 1 + listExponent L) (1 : K) = _
      rw [X_def, monomial_mul_monomial, one_mul]
    rw [h]
    exact chainRuleAt_mul ψ (chainRuleAt_X ψ i) ih

theorem chainRuleAt_monomial [DecidableEq σ] (e : σ →₀ ℕ) (a : K) :
    PowerSeriesChainRuleAt ψ (monomial e a) := by
  obtain ⟨L, rfl⟩ := exists_listExponent_eq e.degree e rfl
  have h : monomial (listExponent L) a = a • monomial (listExponent L) (1 : K) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h]
  exact chainRuleAt_smul ψ a (chainRuleAt_monomial_list ψ L)

theorem chainRuleAt_sum {ι : Type*} (s : Finset ι) (G : ι → MvPowerSeries σ K)
    (h : ∀ i ∈ s, PowerSeriesChainRuleAt ψ (G i)) : PowerSeriesChainRuleAt ψ (∑ i ∈ s, G i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact chainRuleAt_zero ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact chainRuleAt_add ψ (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

/-- The defect of the chain rule on a tail of order above N has order at least N. -/
theorem chainRule_defect_order [CharZero K] (hψ : ∀ i, constantCoeff (ψ (X i)) = 0) {N : ℕ}
    {R : MvPowerSeries σ K} (hR : ((N + 1 : ℕ) : ℕ∞) ≤ R.order) (j : σ) :
    (N : ℕ∞) ≤ (pderiv j (ψ R) - ∑ i, ψ (pderiv i R) * powerSeriesJacobian ψ i j).order := by
  have h1 : ((N + 1 : ℕ) : ℕ∞) ≤ (ψ R).order := order_le_order_algHom ψ hψ (N + 1) R hR
  have h2 : (N : ℕ∞) ≤ (pderiv j (ψ R)).order :=
    enat_le_of_succ_le_add_one (h1.trans (order_le_pderiv_add_one j (ψ R)))
  have h3 : ∀ i ∈ (univ : Finset σ),
      (N : ℕ∞) ≤ (ψ (pderiv i R) * powerSeriesJacobian ψ i j).order := by
    intro i _
    have hi : (N : ℕ∞) ≤ (pderiv i R).order :=
      enat_le_of_succ_le_add_one (hR.trans (order_le_pderiv_add_one i R))
    exact (order_le_order_algHom ψ hψ N _ hi).trans (le_self_add.trans le_order_mul)
  have h4 : (N : ℕ∞) ≤ (∑ i, ψ (pderiv i R) * powerSeriesJacobian ψ i j).order :=
    le_weightedOrder_sum (fun _ => 1) univ _ h3
  calc (N : ℕ∞) ≤ min (pderiv j (ψ R)).order
        (-(∑ i, ψ (pderiv i R) * powerSeriesJacobian ψ i j)).order := by
        rw [order_neg]
        exact le_min h2 h4
    _ ≤ (pderiv j (ψ R) + -(∑ i, ψ (pderiv i R) * powerSeriesJacobian ψ i j)).order :=
        min_order_le_add
    _ = _ := by rw [sub_eq_add_neg]

/-- The chain rule for every K-algebra map sending the variables into the maximal ideal. -/
theorem powerSeries_chainRule [CharZero K] [DecidableEq σ] (hψ : ∀ i, constantCoeff (ψ (X i)) = 0)
    (G : MvPowerSeries σ K) : PowerSeriesChainRuleAt ψ G := by
  intro j
  rw [← sub_eq_zero]
  ext d
  rw [coeff_zero]
  set N := d.degree + 1 with hN
  let p : MvPowerSeries σ K := ∑ e ∈ lowMonomials (σ := σ) (N + 1), monomial e (coeff e G)
  have hp : PowerSeriesChainRuleAt ψ p :=
    chainRuleAt_sum ψ _ _ fun e _ => chainRuleAt_monomial ψ e _
  have hcoeffp : ∀ e : σ →₀ ℕ, e.degree < N + 1 → coeff e p = coeff e G := by
    intro e he
    simp only [p, map_sum, coeff_monomial, Finset.sum_ite_eq, mem_lowMonomials, he, ↓reduceIte]
  have hR : ((N + 1 : ℕ) : ℕ∞) ≤ (G - p).order := by
    apply le_order
    intro e he
    rw [map_sub, hcoeffp e (by exact_mod_cast he), sub_self]
  have hdef := chainRule_defect_order ψ hψ hR j
  have hsplit : pderiv j (ψ G) - ∑ i, ψ (pderiv i G) * powerSeriesJacobian ψ i j =
      (pderiv j (ψ p) - ∑ i, ψ (pderiv i p) * powerSeriesJacobian ψ i j) +
      (pderiv j (ψ (G - p)) - ∑ i, ψ (pderiv i (G - p)) * powerSeriesJacobian ψ i j) := by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hp j, sub_self, zero_add]
  exact coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (show d.degree < N by omega)) hdef)

variable [DecidableEq σ]

/-- The adjugate inverts the chain rule. -/
theorem jacobian_adjugate_identity {G : MvPowerSeries σ K} (hG : PowerSeriesChainRuleAt ψ G)
    (i : σ) : ∑ j, pderiv j (ψ G) * (powerSeriesJacobian ψ).adjugate j i =
      (powerSeriesJacobian ψ).det * ψ (pderiv i G) := by
  set J := powerSeriesJacobian ψ with hJdef
  simp_rw [hG _, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hJ := Matrix.mul_adjugate J
  calc ∑ l, ∑ j, ψ (pderiv l G) * J l j * J.adjugate j i
      = ∑ l, ψ (pderiv l G) * (J * J.adjugate) l i := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = J.det * ψ (pderiv i G) := by
        rw [hJ, Finset.sum_eq_single i]
        · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, mul_comm]
        · intro l _ hli
          rw [Matrix.smul_apply, Matrix.one_apply_ne hli, smul_zero, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h

/-- One derivative lowers the valuation of the image by at most max w + v(det J). -/
theorem weightedOrder_algHom_le_pderiv (w : σ → ℕ) {G : MvPowerSeries σ K}
    (hG : PowerSeriesChainRuleAt ψ G) (i : σ) :
    (ψ G).weightedOrder w ≤ (ψ (pderiv i G)).weightedOrder w +
      (((univ.sup w : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) := by
  set J := powerSeriesJacobian ψ with hJdef
  have hterm : ∀ j ∈ (univ : Finset σ), (ψ G).weightedOrder w ≤
      (pderiv j (ψ G) * J.adjugate j i).weightedOrder w + ((univ.sup w : ℕ) : ℕ∞) := by
    intro j _
    calc (ψ G).weightedOrder w ≤ (pderiv j (ψ G)).weightedOrder w + w j :=
          weightedOrder_le_pderiv_add w j (ψ G)
      _ ≤ (pderiv j (ψ G) * J.adjugate j i).weightedOrder w + ((univ.sup w : ℕ) : ℕ∞) := by
          gcongr
          · exact le_self_add.trans (le_weightedOrder_mul w)
          · exact Finset.le_sup (f := w) (Finset.mem_univ j)
  have hsum := le_weightedOrder_sum_add w univ _ hterm
  rw [hJdef, jacobian_adjugate_identity ψ hG i, weightedOrder_mul] at hsum
  calc (ψ G).weightedOrder w ≤ J.det.weightedOrder w + (ψ (pderiv i G)).weightedOrder w +
        ((univ.sup w : ℕ) : ℕ∞) := hsum
    _ = _ := by ring

theorem weightedOrder_algHom_le_iteratedPDeriv (w : σ → ℕ)
    (hchain : ∀ G, PowerSeriesChainRuleAt ψ G) (L : List σ) (f : MvPowerSeries σ K) :
    (ψ f).weightedOrder w ≤ (ψ (iteratedPDeriv L f)).weightedOrder w +
      L.length * (((univ.sup w : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) := by
  set c : ℕ∞ := ((univ.sup w : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w with hc
  induction L with
  | nil => simp [iteratedPDeriv]
  | cons i L ih =>
    calc (ψ f).weightedOrder w ≤ (ψ (iteratedPDeriv L f)).weightedOrder w + L.length * c := ih
      _ ≤ ((ψ (pderiv i (iteratedPDeriv L f))).weightedOrder w + c) + L.length * c := by
          gcongr
          exact weightedOrder_algHom_le_pderiv ψ w (hchain _) i
      _ = (ψ (iteratedPDeriv (i :: L) f)).weightedOrder w + ((i :: L).length : ℕ) * c := by
          change _ = (ψ (pderiv i (iteratedPDeriv L f))).weightedOrder w + ((L.length + 1 : ℕ) : ℕ∞) * c
          push_cast
          ring

/-- lct ≥ 1/mult through the Jacobian: v(ψ f) ≤ ord(f) (max w + v(det J)). -/
theorem weightedOrder_algHom_le_order_mul [CharZero K] (w : σ → ℕ)
    (hψ : ∀ i, constantCoeff (ψ (X i)) = 0) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    (ψ f).weightedOrder w ≤
      f.order * (((univ.sup w : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) := by
  obtain ⟨L, hL, hunit⟩ := exists_iteratedPDeriv_isUnit hf
  have h := weightedOrder_algHom_le_iteratedPDeriv ψ w (powerSeries_chainRule ψ hψ) L f
  have h0 : (ψ (iteratedPDeriv L f)).weightedOrder w = 0 := by
    have hc : coeff (0 : σ →₀ ℕ) (ψ (iteratedPDeriv L f)) ≠ 0 := by
      rw [coeff_zero_eq_constantCoeff_apply]
      exact (isUnit_iff_constantCoeff.mp (hunit.map ψ)).ne_zero
    refine le_antisymm ?_ zero_le
    calc (ψ (iteratedPDeriv L f)).weightedOrder w ≤ (Finsupp.weight w 0 : ℕ∞) :=
          weightedOrder_le w hc
      _ = 0 := by simp
  rw [h0, zero_add, hL] at h
  exact h

/-- The same with the log discrepancy A(v) = Σ w + v(det J) of the monomial valuation:
v(ψ f) ≤ A(v) ord(f), that is lct ≥ 1/mult for these test valuations. -/
theorem weightedOrder_algHom_le_logDiscrepancy_mul_order [CharZero K] (w : σ → ℕ)
    (hψ : ∀ i, constantCoeff (ψ (X i)) = 0) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    (ψ f).weightedOrder w ≤
      (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) * f.order := by
  refine (weightedOrder_algHom_le_order_mul ψ w hψ hf).trans ?_
  rw [mul_comm]
  gcongr
  exact_mod_cast Finset.sup_le fun i _ =>
    Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i)

end Chain

end MixedFujita

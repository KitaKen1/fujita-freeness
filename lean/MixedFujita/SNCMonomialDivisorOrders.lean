/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateDivisorFormalMap

/-! Exact natural weighted orders of a unit times selected coordinate
powers, before and after restriction to a coordinate divisor. Zero
normal exponent derives nonvanishing of the restriction, and a single
tangent weight reads exactly the coefficient of its selected component. -/

@[expose] public section
open MvPowerSeries
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ K : Type*} [Field K] {r : ℕ}

theorem weightedOrder_selected_coordinate_unit_product
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ) (w : σ → ℕ) :
    ((u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i).weightedOrder w =
      ((∑ i, m i * (χ i).elim 0 w : ℕ) : ℕ∞) := by
  classical
  rw [weightedOrder_mul, weightedOrder_eq_zero_of_isUnit w u.isUnit, zero_add, weightedOrder_prod]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  cases hχ : χ i with
  | none => simp [hχ, weightedOrder_one]
  | some j =>
    simp only [hχ, Option.elim_some]
    rw [X_pow_eq, weightedOrder_monomial_of_ne_zero w one_ne_zero]
    simp [Finsupp.weight_single, nsmul_eq_mul]

theorem weightedOrder_restrict_selected_coordinate_unit_product
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (k : σ) (hzero : ∀ i, χ i = some k → m i = 0) (w : σ → ℕ) :
    (powerSeriesDivisorRestriction k ((u : MvPowerSeries σ K) *
      ∏ i, ((χ i).elim 1 X) ^ m i)).weightedOrder (fun i => w i.val) =
      ((∑ i, m i * (χ i).elim 0 w : ℕ) : ℕ∞) := by
  classical
  rw [map_mul, map_prod, weightedOrder_mul,
    weightedOrder_eq_zero_of_isUnit _ (u.isUnit.map (powerSeriesDivisorRestriction k)),
    zero_add, weightedOrder_prod]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_pow]
  cases hχ : χ i with
  | none => simp [hχ, weightedOrder_one]
  | some j =>
    simp only [hχ, Option.elim_some]
    by_cases hj : j = k
    · subst j
      rw [hzero i hχ]
      simp [weightedOrder_one]
    · rw [powerSeriesDivisorRestriction_X k ⟨j, hj⟩, X_pow_eq,
        weightedOrder_monomial_of_ne_zero _ one_ne_zero]
      simp [Finsupp.weight_single, nsmul_eq_mul]

theorem restrict_selected_coordinate_unit_product_ne_zero
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (k : σ) (hzero : ∀ i, χ i = some k → m i = 0) :
    powerSeriesDivisorRestriction k ((u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i) ≠ 0 := by
  intro hz
  have he := weightedOrder_restrict_selected_coordinate_unit_product u χ m k hzero (fun _ => 0)
  rw [hz, weightedOrder_zero] at he
  exact ENat.natCast_ne_top _ he.symm

theorem weightedOrder_restrict_selected_coordinate_single [DecidableEq σ]
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (hinj : ∀ i j a, χ i = some a → χ j = some a → i = j)
    (k l : σ) (hlk : l ≠ k) (hzero : ∀ i, χ i = some k → m i = 0)
    (t : Fin r) (ht : χ t = some l) :
    (powerSeriesDivisorRestriction k ((u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i)).weightedOrder
      (Pi.single (⟨l, hlk⟩ : {i : σ // i ≠ k}) 1) = (m t : ℕ∞) := by
  classical
  have hw : (fun i : {i : σ // i ≠ k} => (Pi.single l 1 : σ → ℕ) i.val) =
      Pi.single ⟨l, hlk⟩ 1 := by
    funext i
    simp only [Pi.single_apply]
    by_cases hi : i.val = l
    · have he : i = ⟨l, hlk⟩ := Subtype.ext hi
      simp only [hi, he, ite_eq_left rfl]
    · have he : i ≠ ⟨l, hlk⟩ := fun h => hi (congrArg Subtype.val h)
      simp only [ite_eq_right hi, ite_eq_right he]
  rw [← hw, weightedOrder_restrict_selected_coordinate_unit_product u χ m k hzero]
  congr 1
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro i hi hit
    cases hχ : χ i with
    | none => simp [hχ]
    | some a =>
      have hal : a ≠ l := by
        intro hal
        exact hit (hinj i t l (by simpa only [hal] using hχ) ht)
      simp [hχ, Pi.single_apply, hal]
  · intro ht'
    exact (ht' (Finset.mem_univ t)).elim

theorem selected_coordinate_unit_product_remove_normal_power
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (e : Fin r) (k : σ) (he : χ e = some k) :
    (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i =
      X k ^ m e * ((u : MvPowerSeries σ K) *
        ∏ i, ((χ i).elim 1 X) ^ (if i = e then 0 else m i)) := by
  classical
  have hprod : (∏ i, ((χ i).elim 1 (X : σ → MvPowerSeries σ K)) ^ m i) =
      X k ^ m e * ∏ i, ((χ i).elim 1 X) ^ (if i = e then 0 else m i) := by
    calc
      _ = ∏ i, (if i = e then X k ^ m e else 1) *
          ((χ i).elim 1 X) ^ (if i = e then 0 else m i) := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hie : i = e
        · simp [hie, he]
        · simp [hie]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hprod]
  ring

theorem selected_coordinate_unit_product_remove_normal
    (u : (MvPowerSeries σ K)ˣ) (χ : Fin r → Option σ) (m : Fin r → ℕ)
    (e : Fin r) (k : σ) (he : χ e = some k) (hm : m e = 1) :
    (u : MvPowerSeries σ K) * ∏ i, ((χ i).elim 1 X) ^ m i =
      X k * ((u : MvPowerSeries σ K) *
        ∏ i, ((χ i).elim 1 X) ^ (if i = e then 0 else m i)) := by
  simpa only [hm, pow_one] using selected_coordinate_unit_product_remove_normal_power u χ m e k he

end MixedFujita

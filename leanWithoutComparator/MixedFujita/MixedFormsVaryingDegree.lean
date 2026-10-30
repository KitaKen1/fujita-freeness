/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureForms
public import MixedFujita.MixedFormCubeBound

/-!
The mixed bound (13) with a different degree for each summand (step 4). For ample divisors that
are not very ample, the i-th embedding is given by a multiple k_i L_i, so the forms of the i-th
embedding must be taken in degree about j / k_i to give sections of j L_i. The partial product
space U_k depends only on S_0, …, S_k, and the Brunn–Minkowski bound holds with a separate lower
bound λ_i for each summand: Σ_{i ≤ k} λ_i ≤ ((D+1)! dim U_k)^(1/(D+1)). On the closure W of a
point, with restricted forms of degree q_i for the i-th embedding, U_k lies in the image of the
sections on X of the divisor of multidegree (q_l + k (d+1))_{l ≤ k}, exactly as for equal
degrees.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

section Abstract

variable {K : Type*} [Field K] {σ : Type*}

/-- The partial product space U_k depends only on S_0, …, S_k. -/
theorem mixedProductSpace_congr {S S' : ℕ → Submodule K (MvPowerSeries σ K)}
    (C : Submodule K (MvPowerSeries σ K)) (k : ℕ) (h : ∀ i ≤ k, S i = S' i) :
    mixedProductSpace S C k = mixedProductSpace S' C k := by
  induction k with
  | zero => exact h 0 le_rfl
  | succ k ih =>
    change mixedProductSpace S C k * S (k + 1) * C = mixedProductSpace S' C k * S' (k + 1) * C
    rw [ih fun i hi => h i (by omega), h (k + 1) le_rfl]

variable {D : ℕ}

/-- The mixed bound with hypotheses on S_0, …, S_k only and a lower bound λ_i for each summand:
Σ_{i ≤ k} λ_i ≤ ((D+1)! dim U_k)^(1/(D+1)). -/
theorem mixedProductSpace_root_sum_lower (m : MonomialOrder (Fin (D + 1)))
    (S : ℕ → Submodule K (MvPowerSeries (Fin (D + 1)) K))
    (C : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [∀ i, FiniteDimensional K (S i)]
    [FiniteDimensional K C]
    (hcube : binaryVectors (D + 1) ⊆ initialExponentSet m C) (k : ℕ)
    (hpos : ∀ i ≤ k, 0 < Module.finrank K (S i)) (lam : ℕ → ℝ)
    (hlow : ∀ i ≤ k, lam i ≤
      (((D + 1).factorial * Module.finrank K (S i) : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹) :
    ∑ i ∈ Finset.range (k + 1), lam i ≤
      (((D + 1).factorial * Module.finrank K (mixedProductSpace S C k) : ℕ) : ℝ) ^
        ((D : ℝ) + 1)⁻¹ := by
  set S' : ℕ → Submodule K (MvPowerSeries (Fin (D + 1)) K) := fun i => S (min i k) with hS'
  have hSS' : ∀ i ≤ k, S i = S' i := fun i hi => by
    change S i = S (min i k)
    rw [Nat.min_eq_left hi]
  have := finiteDimensional_mixedProductSpace S' C
  have hsum := mixed_root_sum m S' (mixedProductSpace S' C) C le_rfl
    (fun k φ hφ ψ hψ χ hχ => Submodule.mul_mem_mul (Submodule.mul_mem_mul hφ hψ) hχ) hcube
    (fun i => hpos (min i k) (Nat.min_le_right i k)) k
  rw [← mixedProductSpace_congr C k hSS'] at hsum
  set c : ℝ := ((D + 1).factorial : ℝ) ^ ((D : ℝ) + 1)⁻¹ with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hfac : ∀ x : ℕ, (((D + 1).factorial * x : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹ =
      c * (x : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
    intro x
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
  calc ∑ i ∈ Finset.range (k + 1), lam i
      ≤ ∑ i ∈ Finset.range (k + 1), c * (Module.finrank K (S' i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [← hSS' i hik, ← hfac]
        exact hlow i hik
    _ = c * ∑ i ∈ Finset.range (k + 1), (Module.finrank K (S' i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ c * (Module.finrank K (mixedProductSpace S C k) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ = _ := (hfac _).symm

end Abstract

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

variable {η : X} (y : pointClosureScheme η)
  {n : ℕ → ℕ} (e : ∀ i, X ⟶ polynomialProjectiveScheme (n i) K)
  (g : ∀ i, MvPolynomial (Fin (n i)) K) (hg : ∀ i, (g i).IsHomogeneous 1)
  (hggen : ∀ i, g i ∉ ((e i) (genericPoint X)).asHomogeneousIdeal)
  (hgW : ∀ i, g i ∉
    ((pointClosureι η ≫ e i) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
  (he : ∀ i, e i ≫ polynomialProjectiveToBase (n i) K = X ↘ Spec (CommRingCat.of K))
  (jW : ∀ i,
    {k : Fin (n i) // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) k)})
  (hyj : ∀ i, y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) (jW i).val)
  {d : ℕ}
  (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
    ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin (d + 1)) K)

/-- With restricted forms of degree q_i for the i-th embedding: for k < s, the partial product
space U_k lies in the image of the sections of every divisor of multidegree b with
b_l ≥ q_l + k (d+1) for l ≤ k. -/
theorem mixedProductSpace_le_pointClosureHyperplaneRange_varying (q : ℕ → ℕ) (s k : ℕ)
    (hk : k < s) (b : ℕ → ℕ) (hb : ∀ l ≤ k, q l + k * (d + 1) ≤ b l) :
    mixedProductSpace
        (fun i => mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj (q i) i)
        (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) k ≤
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s b := by
  have h1 := one_mem_range_pointClosureSectionTaylor_chart y e g hg hggen jW hyj coords
  have hform : ∀ D i, i < s → mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
      (pointClosureι_comp_toBase e he) y coords jW hyj D i ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s (Pi.single i D) :=
    fun D i hi =>
      (mixedFormTaylorSpace_le_pointClosureSectionTaylor_range y e g hg hggen hgW he jW hyj coords
        D i).trans (pointClosureSectionTaylor_range_le_multiRange y coords
          (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
          (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
            (pointClosureChart y e jW hyj i))
          (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) s i hi D)
  have hmono : ∀ {a b : ℕ → ℕ}, (∀ l < s, a l ≤ b l) →
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s a ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s b := fun hab =>
    pointClosureMultiRange_mono y coords
      (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
      (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
        (pointClosureChart y e jW hyj i))
      (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) h1 s hab
  have hmul : ∀ a b : ℕ → ℕ,
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s a *
          pointClosureHyperplaneRange y e g hg hggen jW hyj coords s b ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s (a + b) := fun a b =>
    pointClosureMultiRange_mul y coords
      (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
      (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
        (pointClosureChart y e jW hyj i))
      (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) s a b
  -- the multidegree (q_l + k (d+1))_{l ≤ k}
  have key : ∀ k, k < s → mixedProductSpace
      (fun i => mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
        (pointClosureι_comp_toBase e he) y coords jW hyj (q i) i)
      (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
        (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) k ≤
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s
        (fun l => if l ≤ k then q l + k * (d + 1) else 0) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine (hform (q 0) 0 hk).trans (hmono fun l _ => ?_)
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · simp
      · rw [Pi.single_eq_of_ne (by omega)]
        exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hU := mul_le_mul' (mul_le_mul' (ih (by omega)) (hform (q (k + 1)) (k + 1) hk))
        (hform (d + 1) 0 (by omega))
      refine hU.trans ((mul_le_mul' (hmul _ _) le_rfl).trans ((hmul _ _).trans
        (hmono fun l _ => ?_)))
      simp only [Pi.add_apply, Pi.single_apply]
      rw [add_one_mul]
      by_cases hl1 : l = k + 1
      · subst hl1
        simp
      · have hq : ∀ c : ℕ, (if l = k + 1 then c else 0) = 0 := fun c => by simp [hl1]
        rw [hq]
        split_ifs <;> omega
  refine (key k hk).trans (hmono fun l _ => ?_)
  split_ifs with hl
  · exact hb l hl
  · exact Nat.zero_le _

end MixedFujita

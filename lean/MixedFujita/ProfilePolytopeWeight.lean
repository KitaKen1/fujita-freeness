/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationDivisorStructure

/-!
A normalized profile in the polytope of a point is realized by a weight on the members through
the point (used to pass from the point-centre property to weights with a positive-dimensional
centre, section 5).

Let p = (a, v) with a > 0, and let the normalized profile v / a lie in the polytope of the point
pt: a convex combination with coefficients μ_j, supported on the members ξ_j through pt, of the
profiles (e_ij / A_j)_i, where A_j > 0 is the log discrepancy of ξ_j. Then the weight
w_j = a μ_j / A_j is nonnegative, nonzero, supported on the members through pt, and has the
datum p: Σ_j w_j A_j = a and Σ_j w_j e_ij = v_i.
-/

@[expose] public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A normalized profile in the polytope of a point is the profile of a weight on the members
through the point. -/
theorem exists_weight_of_inSNCProfilePolytope {ι : Type*} {r : ℕ} (ξ : Fin r → X) (d : ℕ)
    (B : CartierDivisor X) (Dv : ι → CartierDivisor X) (p : ℝ × (ι → ℝ)) (hp : 0 < p.1)
    (pt : X) (hA : ∀ j, 0 < ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (h : InSNCProfilePolytope ξ d B Dv (fun i => p.2 i / p.1) pt) :
    ∃ w : Fin r → ℝ, (∀ j, 0 ≤ w j) ∧ w ≠ 0 ∧
      (∀ j, w j ≠ 0 → pt ∈ closure ({ξ j} : Set X)) ∧
      p.1 = ∑ j, w j * (((d : ℝ) - cartierCoefficient B (ξ j)) / d) ∧
      ∀ i, p.2 i = ∑ j, w j * (cartierCoefficient (Dv i) (ξ j) : ℝ) := by
  obtain ⟨μ, hμ0, hμ1, hsupp, hq⟩ := h
  refine ⟨fun j => p.1 * μ j / (((d : ℝ) - cartierCoefficient B (ξ j)) / d),
    fun j => div_nonneg (mul_nonneg hp.le (hμ0 j)) (hA j).le, ?_, ?_, ?_, ?_⟩
  · intro hw
    obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero fun j _ => hall j] at hμ1
      exact zero_ne_one hμ1
    have h1 := congrFun hw j
    have hne : p.1 * μ j / (((d : ℝ) - cartierCoefficient B (ξ j)) / d) ≠ 0 :=
      div_ne_zero (mul_ne_zero hp.ne' hj) (hA j).ne'
    exact hne h1
  · intro j hj
    refine hsupp j fun hμ => hj ?_
    simp only [hμ, mul_zero, zero_div]
  · have h1 : ∀ j, p.1 * μ j / (((d : ℝ) - cartierCoefficient B (ξ j)) / d) *
        (((d : ℝ) - cartierCoefficient B (ξ j)) / d) = p.1 * μ j := fun j =>
      div_mul_cancel₀ _ (hA j).ne'
    simp only [h1]
    rw [← Finset.mul_sum, hμ1, mul_one]
  · intro i
    have h1 := hq i
    have h2 : ∀ j, p.1 * μ j / (((d : ℝ) - cartierCoefficient B (ξ j)) / d) *
        (cartierCoefficient (Dv i) (ξ j) : ℝ) = p.1 * (μ j * ((cartierCoefficient (Dv i) (ξ j) : ℝ) /
          (((d : ℝ) - cartierCoefficient B (ξ j)) / d))) := fun j => by ring
    simp only [h2]
    rw [← Finset.mul_sum, ← h1]
    field_simp

end MixedFujita

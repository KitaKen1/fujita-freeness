/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierEulerPolynomial
public import MixedFujita.AmpleCartierSerreVanishing

/-! 元ample Cartier方向の実Hilbert多項式・有限性とSerre消滅の内部供給。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset

/-- If positive ACTUAL cohomology vanishes, the full Euler characteristic
is the original base-field dimension of global sections. -/
theorem moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero
    (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
    (M : Y.Modules) (hvan : ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology M (q + 1))) :
    Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) M =
      (Module.finrank K Γ(M, ⊤) : ℤ) := by
  rw [Scheme.Modules.eulerChar_eq_sum _ M ({0} : Finset ℕ) (by
    intro q hq
    have hq0 : q ≠ 0 := by simpa only [mem_singleton] using hq
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0
    let := hvan r
    rw [sgaFinrankH_eq_actual_finrank K M (r + 1), Module.finrank_zero_of_subsingleton])]
  simp only [sum_singleton, pow_zero, one_mul]
  rw [sgaFinrankH_eq_actual_finrank K M 0,
    Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections K M]


/-- For any ORIGINAL ample Cartier direction the explicit Euler polynomial
is eventually the actual Hilbert function of every fixed Cartier twist.
Finiteness and Serre vanishing are proved internally, over any field. -/
theorem proper_ample_cartierEulerPolynomial_eventually_eq_sections
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (H E : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) :
    (∀ j : ℕ, FiniteDimensional K Γ((E + j • H).sheaf, ⊤)) ∧
      ∃ j₀ : ℕ, ∀ j ≥ j₀,
        (cartierEulerPolynomial K n H E).eval (j : ℚ) =
          (Module.finrank K Γ((E + j • H).sheaf, ⊤) : ℚ) := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_cohomology_subsingleton hH E
  refine ⟨fun j => proper_cartier_sections_finite K _, j₀, fun j hj => ?_⟩
  have h := proper_cartierEulerPolynomial_eval_int K n hdim H E (j : ℤ)
  simp only [natCast_zsmul, Int.cast_natCast] at h
  rw [moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K _ (hj₀ j hj)] at h
  simpa only [Int.cast_natCast] using h

end MixedFujita

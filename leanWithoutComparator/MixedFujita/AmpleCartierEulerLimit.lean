/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleCartierHilbertPolynomial
public import MixedFujita.PolynomialLeadingLimit

/-! 実ample切断の先頭極限と対角Euler係数の同定・基礎体線形比較。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Polynomial Finset

/-- The actual ample Hilbert function has highest coefficient equal to the
original n-fold Cartier Euler difference divided by n!, without assuming a
Hilbert polynomial, cohomology vanishing or a leading coefficient. -/
theorem proper_ample_cartier_sections_scaled_limit
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (H E : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) :
    Filter.Tendsto (fun j : ℕ =>
      (Module.finrank K Γ((E + j • H).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
      Filter.atTop (nhds
        ((cartierMixedEulerDifference K (List.replicate n H) E : ℝ) / n.factorial)) := by
  obtain ⟨hfin, j₀, hj₀⟩ := proper_ample_cartierEulerPolynomial_eventually_eq_sections
    K n hdim H E hH
  have h := rationalPolynomial_tendsto_eval_div_pow_nat (cartierEulerPolynomial K n H E) n
    (cartierEulerPolynomial_natDegree_le K n H E)
  have hcoeff : ((cartierEulerPolynomial K n H E).coeff n : ℝ) =
      (cartierMixedEulerDifference K (List.replicate n H) E : ℝ) / n.factorial := by
    have hc := cartierEulerPolynomial_coeff_top K n H E
    have hc' : (n.factorial : ℝ) * ((cartierEulerPolynomial K n H E).coeff n : ℝ) =
        (cartierMixedEulerDifference K (List.replicate n H) E : ℝ) := by exact_mod_cast hc
    exact (eq_div_iff (by exact_mod_cast n.factorial_ne_zero)).mpr (by simpa only [mul_comm] using hc')
  rw [hcoeff] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop j₀] with j hj
  have heq := congrArg (fun q : ℚ => (q : ℝ)) (hj₀ j hj)
  simpa only [Rat.cast_natCast] using congrArg (fun a : ℝ => a / (j : ℝ) ^ n) heq


/-- An actual module-sheaf isomorphism preserves base-field dimensions of
sections, through the existing K-linear cohomology-zero dictionary. -/
theorem moduleSections_finrank_congr
    (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
    {M N : Y.Modules} (a : M ≅ N) :
    Module.finrank K Γ(M, ⊤) = Module.finrank K Γ(N, ⊤) := by
  rw [← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections K M,
    ← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections K N]
  exact Scheme.Modules.finrank_cohomology_congr K a 0

end MixedFujita

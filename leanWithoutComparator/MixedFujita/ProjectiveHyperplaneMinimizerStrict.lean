/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightSpecializationComparison
public import MixedFujita.ProjectiveMultipleInteriorStart

/-!
The data of the minimizer for the hyperplane class when the volume inequality is strict (steps 11
and 13).

Let Y be a smooth closed subvariety of dimension m of projective space with hyperplane divisor J,
cut by a linear form g that does not vanish at the closed point x, over an uncountable
algebraically closed field of characteristic zero, and take the zero boundary. The numerical
hypothesis at the generic point gives J^m ≥ (m + 1)^m. If the inequality is strict, the interior
condition (7) holds at every closed point with b = 1 (`projectiveHyperplane_multiple_interior_start`
with k = 1: (m/(m+1)) (J^m)^(1/m) > m). So the data of the minimizer exist at x for every m₀ ≥ 1
from the numerical hypothesis for J, the strict inequality J^m > (m + 1)^m and the closedness of
the realization sets in the tuple and in the point at all large degrees. The equality case
J^m = (m + 1)^m needs Lemma 5 (section 8).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer at x for the hyperplane class with zero boundary, for every m₀ ≥ 1,
from the numerical hypothesis for J, the strict volume inequality J^m > (m + 1)^m and the
closedness of the realization sets in the tuple and in the point at all large degrees. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_of_strictVolume
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V)
    (hvol : ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
        (𝓝 ((r : ℝ) / m.factorial)) → (m + 1) ^ m < r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen)
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (projectiveHyperplaneCartier e g hg hggen) m₀ x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  -- every multiple of J has a nonzero section
  have hsec : ∀ q : ℕ, 0 ≤ q → ∃ σ : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      σ ≠ 0 := by
    intro q _
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x q
    refine ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  -- the interior condition (7) with b = 1, from the strict volume inequality
  obtain ⟨r, -, -, hlim, hstart⟩ := projectiveHyperplane_multiple_interior_start e g hg hggen he
    hdimY hm (projectiveHyperplaneCartier e g hg hggen) (k := 1) one_pos (one_nsmul _) 0 hsec
  have hlim' : Tendsto (fun D : ℕ => (Module.finrank K
      Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
      (𝓝 ((r : ℝ) / m.factorial)) := by
    simpa using hlim
  have hvolr : ((m : ℝ) + 1) ^ m < (r : ℝ) := by exact_mod_cast hvol r hlim'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hroot : (m : ℝ) + 1 < (r : ℝ) ^ ((m : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hm0, Real.rpow_natCast]
    exact hvolr
  have hb : (m : ℝ) / 1 < (m : ℝ) / (m + 1) * ((r : ℝ) / ((1 : ℕ) : ℝ) ^ m) ^ (m : ℝ)⁻¹ := by
    rw [Nat.cast_one, one_pow, div_one, div_one, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t₀, -, ht₀1, ζ, hζ, δ, hδ, hev⟩ := hstart one_pos hb x hxc
  refine projectiveHyperplane_kltIsolationMinimizerData_of_realizationClosed e g hg hggen he hm
    cY x hxc hgx (t₀ := t₀) (δ := min δ (1 / 2)) ht₀1 (lt_min hδ (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hgrow hclosed hclosedPt ?_ m₀ hm₀
  filter_upwards [hev] with j hj t ht₀t ht1
  obtain ⟨B, hB⟩ := hj t ht₀t ht1.le
  exact ⟨B, ζ, hζ.le, hB.trans (by linarith [min_le_left δ (1 / 2)])⟩

end Hyperplane

end MixedFujita

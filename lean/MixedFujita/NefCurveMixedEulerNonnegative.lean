/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteDominantMixedIntersectionMultiplier
public import MixedFujita.IntegralProjectiveCurveSmoothCover
public import MixedFujita.NefCartierPullbackRepresentatives
public import MixedFujita.CurveMixedEulerDegree
public import MixedFujita.SemiampleCartierMixedIntersection

/-! 有限smooth被覆による特異曲線上の元nef混合次数の非負性。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A full actual singleton mixed coefficient on a smooth proper curve
is the ORIGINAL curve pullback degree, with every base translate allowed. -/
theorem properSmoothCurve_pulled_singleton_eq_curvePullbackDegree
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim C = 1) (p : C ⟶ X) (N E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule C) [N] E =
      cartierCurvePullbackDegree (K := K) N p := by
  obtain ⟨F, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor N p
  obtain ⟨G, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E p
  rw [cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K p (.cons ⟨a⟩ .nil) E G b,
    properSmoothCurve_cartierMixedEulerDifference_singleton_eq_degree K hdim F G]
  exact (cartierCurvePullbackDegree_eq_representation_degree (K := K) hdim N p F a).symm


/-- ORIGINAL curve-test nefness forces nonnegative mixed degree on EVERY
integral projective curve, including singular ones. The smooth finite cover,
positive multiplier and degree comparison are internally constructed. -/
theorem proper_integral_curve_pulled_nef_unit_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y = 1)
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (p : Y ⟶ X) [p.IsOver (Spec (CommRingCat.of K))]
    (N : CartierDivisor X) (hN : CartierIsNef K N) (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) [N] E := by
  obtain ⟨C, hC, hCO, f, hf, hfd, hfo, hprop, hsm, hdimC⟩ :=
    proper_integral_curve_exists_finite_smooth_cover K hdim hProj
  let := hC
  let := hCO
  let := hf
  let := hfd
  let := hfo
  let := hprop
  let := hsm
  obtain ⟨k, hk, hformula⟩ := finite_dominant_exists_positive_top_mixed_multiplier K 1 (by decide)
    hdim hdimC hProj f
  have hnn : 0 ≤ cartierPulledModuleMixedEulerDifference K (f ≫ p)
      (CohomologyAux.unitModule C) [N] E := by
    rw [properSmoothCurve_pulled_singleton_eq_curvePullbackDegree K hdimC]
    exact hN C hdimC (f ≫ p) (HomIsOver.comp_over (f := f ≫ p))
  rw [hformula X p [N] rfl E] at hnn
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hk : (0 : ℤ) < k)).mp hnn


/-- The same singleton nef coefficient is nonnegative when the source
has dimension AT MOST one; zero-dimensional sources contribute zero. -/
theorem proper_dim_le_one_pulled_nef_unit_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y ≤ 1)
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (p : Y ⟶ X) [p.IsOver (Spec (CommRingCat.of K))]
    (N : CartierDivisor X) (hN : CartierIsNef K N) (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) [N] E := by
  have hnat : ∃ d : ℕ, topologicalKrullDim Y = d :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  obtain ⟨d, hd⟩ := hnat
  have hdle : d ≤ 1 := by exact_mod_cast hd ▸ hdim
  by_cases hd0 : d = 0
  · have hz : topologicalKrullDim Y ≤ 0 := by simp [hd, hd0]
    rw [proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K 0 hz p
      (CohomologyAux.unitModule Y) [N] (by simp) E]
  · have hd1 : d = 1 := by omega
    exact proper_integral_curve_pulled_nef_unit_nonneg K (by simpa [hd1] using hd) hProj p N hN E

end MixedFujita

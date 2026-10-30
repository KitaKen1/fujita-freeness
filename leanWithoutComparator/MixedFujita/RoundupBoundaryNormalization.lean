/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSourceRoundupIntegerKlt
public import MixedFujita.SNCBoundaryRoundup

/-!
Normalize an actual signed SNC boundary by adding its integer roundup.
The resulting boundary has coefficients in [0,1), is effective and klt.
The klt assertion reuses the integer criterion on E-E=0 on the same model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Adding the integer negative-boundary roundup puts the numerator in [0,d). -/
theorem boundary_add_roundup_coefficient_mem_Ico (b : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ b + (d : ℤ) * ⌈-((b : ℝ) / (d : ℝ))⌉ ∧
      b + (d : ℤ) * ⌈-((b : ℝ) / (d : ℝ))⌉ < (d : ℤ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · have hceil : -(b : ℝ) / (d : ℝ) ≤ (⌈-((b : ℝ) / (d : ℝ))⌉ : ℝ) := by
      simpa only [neg_div] using (Int.le_ceil (-((b : ℝ) / (d : ℝ))))
    have hmul := (div_le_iff₀ hdR).mp hceil
    have h : (0 : ℝ) ≤ (b : ℝ) + (d : ℝ) * (⌈-((b : ℝ) / (d : ℝ))⌉ : ℝ) := by
      nlinarith
    exact_mod_cast h
  · exact (boundary_roundup_sub_integer_nonneg_iff b ⌈-((b : ℝ) / (d : ℝ))⌉ d hd).mp
      (by omega)

/-- Integral coefficient shifts translate the actual negative-boundary roundup exactly. -/
theorem boundary_roundup_add_integral_coefficient (b k : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    ⌈-(((b + (d : ℤ) * k : ℤ) : ℝ) / (d : ℝ))⌉ =
      ⌈-((b : ℝ) / (d : ℝ))⌉ - k := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h : -(((b + (d : ℤ) * k : ℤ) : ℝ) / (d : ℝ)) =
      -((b : ℝ) / (d : ℝ)) - (k : ℝ) := by
    push_cast
    field_simp <;> ring
  rw [h, Int.ceil_sub_intCast]

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The same actual source boundary plus d times its roundup has every numerator
in [0,d), with no new resolution or component support assumption. -/
theorem crepant_source_roundup_normalized_boundary_coefficients
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n) (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) :
    ∀ t : CodimensionOnePoint T,
      0 ≤ cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover + d • E) (t : T) ∧
      cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover + d • E) (t : T) < (d : ℤ) := by
  intro t
  rw [cartierCoefficient_add, cartierCoefficient_nsmul, hE t]
  exact boundary_add_roundup_coefficient_mem_Ico _ d hd

/-- The actual same-source integer normalization has effective boundary and
is all-model klt. The klt proof is the existing E-E=0 integer criterion. -/
theorem crepant_source_roundup_normalized_pair_effective_klt
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (E : CartierDivisor T) (heff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) :
    LogPairBoundaryEffective cT (crepantPullbackFormUnit ρ hρ c f cT) d
      (cartierPullback ρ D + d • E) ∧
    LogPairIsKlt cT (crepantPullbackFormUnit ρ hρ c f cT) d
      (cartierPullback ρ D + d • E) := by
  have hrec := crepantBoundaryCartier_smooth_recombine ρ hρ c f d D cT
  have heq : cartierPullback ρ D + d • E =
      d • (smoothCanonicalDivisor cT +
        principalCartierDivisor T (crepantPullbackFormUnit ρ hρ c f cT)) +
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover + d • E) := by
    rw [← hrec]
    abel
  constructor
  · rw [heq]
    intro e t ht hcoh
    rw [cartierCoefficient_add]
    exact (smooth_logPairBoundaryEffective_zero cT
      (crepantPullbackFormUnit ρ hρ c f cT) d e t ht hcoh).trans
      (le_add_of_nonneg_right
        ((crepant_source_roundup_normalized_boundary_coefficients ρ hρ c f d hd D cT E hE
          ⟨t, hcoh⟩).1))
  · have h := (crepant_source_roundup_sub_integer_isEffective_iff_klt ρ hρ hnormT
      c f d hd D cT ξ hinj hξ hsnc hsupport E hE E heff 1).mp
        (by simpa only [one_nsmul, sub_self] using
          (CartierDivisor.isEffective_zero (X := T)))
    simpa only [mul_one] using h

end MixedFujita

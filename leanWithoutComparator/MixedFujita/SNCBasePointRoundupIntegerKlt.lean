/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RoundupIntegerThresholdArithmetic
public import MixedFujita.SNCBasePointRationalThreshold

/-!
On an actual joint SNC model, nonnegativity of the integer-twisted roundup
at exactly the primes specializing over a base point is equivalent to the
all-model klt condition over that point. This is a local coefficient lattice
criterion; it does not assert a direct-image sheaf extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (g : X ⟶ Y) (η : Y)

/-- The actual roundup integer coefficient lattice over a chosen base point
is exactly the all-model klt integer perturbation interval over that point. -/
theorem snc_roundup_integer_coefficients_overBasePoint_iff_klt
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (p : ℕ) :
    (∀ t : CodimensionOnePoint T, η ∈ closure ({(ρ ≫ g) (t : T)} : Set Y) →
      0 ≤ cartierCoefficient (E - p • cartierPullback ρ G) (t : T)) ↔
      LogPairIsKltOverBasePoint g η c f d (D + (d * p) • G) := by
  have htest : LogPairIsKltOverBasePoint g η c f d (D + (d * p) • G) ↔
      ∀ i, η ∈ closure ({(ρ ≫ g) (ξ i)} : Set Y) →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) +
          ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ G) (ξ i) < (d : ℤ) := by
    simpa only [one_mul, one_nsmul, Nat.cast_one, one_mul] using
      logPairIsKltOverBasePoint_rational_perturbation_iff_snc_coefficients ρ hρ g η
        c f d hd D G cT ξ hinj hξ hsnc hsupport hGsupport p 1 (by omega)
  have hcoef (t : CodimensionOnePoint T) :
      0 ≤ cartierCoefficient (E - p • cartierPullback ρ G) (t : T) ↔
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) +
          ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ G) (t : T) < (d : ℤ) := by
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, hE t]
    simpa only [Nat.cast_mul, mul_assoc] using boundary_roundup_sub_integer_nonneg_iff
      (cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T))
      ((p : ℤ) * cartierCoefficient (cartierPullback ρ G) (t : T)) d hd
  constructor
  · intro h
    apply htest.mpr
    intro i hi
    exact (hcoef ⟨ξ i, hξ i⟩).mp (h ⟨ξ i, hξ i⟩ hi)
  · intro h t ht
    apply (hcoef t).mpr
    by_cases hmem : (t : T) ∈ Set.range ξ
    · obtain ⟨i, hi⟩ := hmem
      simpa only [hi] using htest.mp h i (by simpa only [hi] using ht)
    · rw [hsupport t hmem, hGsupport t hmem, mul_zero, add_zero]
      exact_mod_cast (show 0 < d by omega)

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCSignedRoundupSplit
public import MixedFujita.PrincipalizedFunctionNef
public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.ExceptionalCartierPushforwardIso

/-!
The actual signed boundary used for strict-transform connectedness has no negative
coefficient over a source prime divisor. Its unrestricted SNC roundup therefore
splits into an effective exceptional part E and a possibly nonreduced non-klt cut S.
The canonical unit O_X -> rho_* O_T(E) is an isomorphism. The relative anti-adjoint
is globally generated when H is principal and -G is globally generated.
Relative vanishing and connectedness of the cut fibres are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (cX : EtaleChart K X n) (cT : EtaleChart K T n)

/-- The denominator-cleared boundary d(H-K_{T/X})+G on the actual model. -/
noncomputable def strictTransformConnectednessBoundary (H G : CartierDivisor T) (d : ℕ) :
    CartierDivisor T :=
  d • (H + crepantBoundaryCartier ρ hρ cX 1 1
    (1 • (smoothCanonicalDivisor cX + principalCartierDivisor X 1)) cT etaleCharts_cover) + G

/-- Its coefficients are exactly the numerator in StrictTransformConnectednessStatement. -/
theorem strictTransformConnectednessBoundary_coefficient (H G : CartierDivisor T) (d : ℕ) (t : T) :
    cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d) t =
      (d : ℤ) * (cartierCoefficient H t + cartierCoefficient
        (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor X 1)) cT etaleCharts_cover) t) +
        cartierCoefficient G t := by
  simp only [strictTransformConnectednessBoundary, cartierCoefficient_add, cartierCoefficient_nsmul]

/-- The three support conditions already returned by the original model support this boundary. -/
theorem strictTransformConnectednessBoundary_supported (H G : CartierDivisor T) (d : ℕ)
    {r : ℕ} (ξ : Fin r → T)
    (hH : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient H (t : T) = 0)
    (hB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient
      (crepantBoundaryCartier ρ hρ cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor X 1)) cT etaleCharts_cover) (t : T) = 0)
    (hG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) :
    ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d) (t : T) = 0 := by
  intro t ht
  rw [strictTransformConnectednessBoundary_coefficient, hH t ht, hB t ht, hG t ht]
  simp

/-- A negative coefficient can occur only away from the primes of the original smooth space. -/
theorem strictTransformConnectednessBoundary_nonneg_over_prime
    (H G : CartierDivisor T) (hH : H.IsEffective) (hG : G.IsEffective) (d : ℕ)
    (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
    0 ≤ cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d) (t : T) := by
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := K) x
  have hb := stalkMap_bijective_of_birational_over_normal_prime hnorm ρ hρ (t : T) ht
  rw [strictTransformConnectednessBoundary_coefficient,
    crepantBoundaryCartier_coefficient_eq_zero_of_stalkMap_bijective ρ hρ cX cT t ht hb, add_zero]
  exact add_nonneg (mul_nonneg (Int.natCast_nonneg d)
    (cartierCoefficient_nonneg_of_isEffective H hH _)) (cartierCoefficient_nonneg_of_isEffective G hG _)

/-- Construct the exceptional part, the exact non-klt cut and the canonical direct-image
isomorphism from the actual smooth model. No lc bound or exceptional-divisor witness is supplied. -/
theorem exists_strictTransform_roundup_exceptional_pushforward [IsProper ρ]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (H G : CartierDivisor T) (hH : H.IsEffective) (hG : G.IsEffective)
    (d : ℕ) (hd : 1 ≤ d) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d) (t : T) = 0) :
    ∃ (E S : CartierDivisor T) (hE : E.IsEffective) (_ : S.IsEffective),
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) ↔
        (d : ℤ) ≤ cartierCoefficient (strictTransformConnectednessBoundary ρ hρ cX cT H G d) (t : T)) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = 0 ∨
        cartierCoefficient S (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0) ∧
      IsIso (effectiveCartierPushforwardUnitMap ρ E hE) := by
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := K) x
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨E, S, hE, hS, hEc, hSc, hround, hdisj⟩ := exists_effective_snc_signed_roundup_split
    (strictTransformConnectednessBoundary ρ hρ cX cT H G d) d ξ hinj hξ hsnc hsupport
  have hexc (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
      cartierCoefficient E (t : T) = 0 := by
    rw [hEc]
    exact signed_roundup_exceptional_eq_zero _ d hd
      (strictTransformConnectednessBoundary_nonneg_over_prime ρ hρ cX cT H G hH hG d t ht)
  refine ⟨E, S, hE, hS, hround, fun t => ?_, hdisj, hexc,
    effectiveExceptionalCartierPushforwardUnitMap_isIso hnormX hnormT ρ hρ E hE hexc⟩
  rw [hSc]
  exact signed_roundup_cut_positive_iff _ d hd

/-- Exact cancellation of the relative canonical divisor, before passing to any numerical class. -/
theorem strictTransform_relativeAntiAdjoint_eq (H G : CartierDivisor T) (d : ℕ) :
    -(d • birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover +
        strictTransformConnectednessBoundary ρ hρ cX cT H G d) = -(d • H + G) := by
  have hR : birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover =
      -crepantBoundaryCartier ρ hρ cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor X 1)) cT etaleCharts_cover := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, neg_neg, logDiscrepancyDivisor_boundary_zero,
      one_nsmul]
  rw [hR, strictTransformConnectednessBoundary]
  simp only [smul_add, smul_neg, one_nsmul]
  abel

/-- The negative relative adjoint is globally generated if the hyperplane is principal
and -G is globally generated. This does not imply the still-needed relative vanishing. -/
theorem strictTransform_relativeAntiAdjoint_globallyGenerated
    (v : T.functionFieldˣ) (G : CartierDivisor T) (hgen : CartierIsGloballyGenerated (-G)) (d : ℕ) :
    CartierIsGloballyGenerated
      (-(d • birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover +
        strictTransformConnectednessBoundary ρ hρ cX cT (principalCartierDivisor T v) G d)) := by
  rw [strictTransform_relativeAntiAdjoint_eq, neg_add_rev]
  apply cartierIsGloballyGenerated_add _ _ hgen
  rw [← smul_neg, ← principalCartierDivisor_inv]
  exact cartierIsGloballyGenerated_nsmul _ (cartierIsGloballyGenerated_principal _) d

end MixedFujita

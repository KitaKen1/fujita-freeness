/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.StrictTransformConnectednessPreparation
public import MixedFujita.ExceptionalCutConnectedness

/-!
Reduce the original geometric connectedness input to actual H1 vanishing on an
affine birational SNC model. The cut, support comparison, exceptional unit,
untwisting, surjectivity and fibre topology are all supplied by proved results.
The vanishing statement below remains an explicit unproved input. The model is
not required to be proper over the base field.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- Remaining cohomological input on an affine birational model: the relative
anti-adjoint is nef and the actual Cartier kernel has the negative-boundary roundup
coefficients. This does not assume properness over K or fibre connectedness. -/
def AffineBirationalSNCRoundupVanishing (K : Type u) [Field K] : Prop :=
  ∀ (n : ℕ) (X T : Scheme.{u}) [IsIntegral X] [IsIntegral T]
    [IsAffine X] [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [IsProjective ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (cT : EtaleChart K T n)
    (B : CartierDivisor T) (d : ℕ), 1 ≤ d → ∀ {r : ℕ} (ξ : Fin r → T),
    Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K n ξ →
    (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0) →
    CartierIsNef K (-(d • birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover + B)) →
    ∀ C : CartierDivisor T,
    (∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉) →
    Subsingleton (Scheme.Modules.Cohomology C.sheaf 1)

set_option maxHeartbeats 1600000 in
/-- Actual roundup H1 vanishing implies the original strict-transform connectedness
statement. All supporting divisor, cut, pushforward and fibre witnesses are internal. -/
theorem strictTransformConnectednessStatement_of_roundupVanishing
    {K : Type u} [Field K] (hvan : AffineBirationalSNCRoundupVanishing K) :
    StrictTransformConnectednessStatement K := by
  intro A _ _ _ _ N _ cX φ hφ _ J _ g _hnd χ M _hN hM T _ _ _ _
    ρ _ _ _ _ hρ cT r ξ hinj hξ hsnc hcrep hH G hG hGsupport hI
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (N + 1) _
  let H := cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
    (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))
  let B := strictTransformConnectednessBoundary ρ hρ cX cT H G M
  have hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0 :=
    strictTransformConnectednessBoundary_supported ρ hρ cX cT H G M ξ hH hcrep hGsupport
  obtain ⟨_hgen, _hGnef, hnef, E, S, hE, hS, hround, hSc, hdisj, _hexc, hunit⟩ :=
    original_function_connectedness_preparation cX φ hφ g ρ hρ cT ξ hinj hξ hsnc G hG hI M hM hsupp
  let : IsIso (effectiveCartierPushforwardUnitMap ρ E hE) := hunit
  have hcoho := hvan (N + 1) (Spec (CommRingCat.of A)) T ρ hρ cX cT B M hM
    ξ hinj hξ hsnc hsupp hnef (E - S) hround
  have hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hES (t : CodimensionOnePoint T) (ht : 0 < cartierCoefficient S (t : T)) :
      cartierCoefficient E (t : T) = 0 := by
    rcases hdisj t with h | h
    · exact h
    · omega
  have hc := threshold_member_union_fibre_preconnected_of_H1 ρ hnorm B E S hE hS
    M hM ξ hξ hsupp hSc hES hcoho
    (specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))
  simp only [B, strictTransformConnectednessBoundary_coefficient, H] at hc
  convert hc using 1

/-- The original F1 endpoint now follows from sum KV and the explicit affine roundup
vanishing statement. Neither vanishing theorem is proved by this implication. -/
theorem mixedFujitaFreeness_of_kvSum_of_affineRoundupVanishing
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ), KawamataViehwegVanishingSNCSum K n)
    (hvan : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], AffineBirationalSNCRoundupVanishing K) :
    MixedFujitaFreeness.{u} := by
  apply mixedFujitaFreeness_of_kvSum_of_strictTransformConnectedness hKV
  intro K _ _ _
  exact strictTransformConnectednessStatement_of_roundupVanishing (hvan K)

end MixedFujita

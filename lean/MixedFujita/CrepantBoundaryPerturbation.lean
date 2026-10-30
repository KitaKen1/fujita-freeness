/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GloballyGeneratedKltPerturbation

/-!
For an actual proper smooth birational model of a klt pair, construct the signed
cleared crepant boundary from the Cartier pullback and pulled-back rational top
form. Its coefficients are below the clearing denominator by the source's
all-model klt condition. If this actual boundary has a supplied SNC support,
ordinary global generation gives klt perturbations on the model.

Existence of an SNC resolution and descent of the perturbed klt pair to the
singular source are not asserted. Negative crepant coefficients are allowed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}}
  [IsIntegral Y] [IsIntegral T] [Y.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ Y) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The actual rational coefficient of the pulled-back top form in the model's chart. -/
noncomputable def crepantPullbackFormUnit (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (c'₀ : EtaleChart K T n) : T.functionFieldˣ :=
  Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f₀ *
    (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ c'₀).unit

/-- The signed denominator-cleared crepant boundary on the actual model. -/
noncomputable def crepantBoundaryCartier (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor Y) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) : CartierDivisor T :=
  cartierPullback ρ D - d • pullbackFormDivisor ρ hρ c₀ f₀ c'₀ hT

/-- The crepant boundary is the negative of the actual discrepancy divisor. -/
theorem crepantBoundaryCartier_eq_neg_discrepancy (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ hT =
      -logDiscrepancyDivisor n ρ hρ c₀ f₀ d D c'₀ hT := by
  unfold crepantBoundaryCartier logDiscrepancyDivisor
  abel

/-- Recombining the actual pulled top form and crepant boundary gives the Cartier pullback. -/
theorem crepantBoundaryCartier_recombine (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    d • pullbackFormDivisor ρ hρ c₀ f₀ c'₀ hT +
      crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ hT = cartierPullback ρ D := by
  unfold crepantBoundaryCartier
  abel

variable [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

/-- Express the crepant boundary using the actual canonical divisor and rational coefficient. -/
theorem crepantBoundaryCartier_smooth_recombine (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y) (c'₀ : EtaleChart K T n) :
    d • (smoothCanonicalDivisor c'₀ +
      principalCartierDivisor T (crepantPullbackFormUnit ρ hρ c₀ f₀ c'₀)) +
      crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover = cartierPullback ρ D :=
  crepantBoundaryCartier_recombine ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover

variable [IsLocallyNoetherian T] [IsProper ρ]

/-- The source's all-model klt condition gives the strict bound on every crepant coefficient. -/
theorem logPairIsKlt_crepantBoundary_coefficient_lt (c₀ : EtaleChart K Y n)
    (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y)
    (hklt : LogPairIsKlt c₀ f₀ d D) (c'₀ : EtaleChart K T n)
    (t : CodimensionOnePoint T) :
    cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover)
      (t : T) < (d : ℤ) := by
  have h := hklt T ρ hρ c'₀ (t : T) t.property
  rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
  omega

attribute [local instance] Classical.propDecidable

/-- On a supplied actual proper smooth model with SNC crepant support, global
generation constructs a signed klt perturbation of the actual Cartier pullback.
The source Y may be singular. This does not assert the existence of such a model
or descent of the perturbed klt pair back to Y. -/
theorem logPairIsKlt_exists_crepant_klt_perturbation [CharZero K] [IsNoetherian T]
    (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y)
    (hklt : LogPairIsKlt c₀ f₀ d D) (c'₀ : EtaleChart K T n)
    (H : CartierDivisor T) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover)
        (t : T) = 0) (k : ℕ) (hk : k < d) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → T),
      Smooth (cartierSectionZeroSchemeι H s hs ≫ (T ↘ Spec (CommRingCat.of K))) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ t : CodimensionOnePoint T,
        cartierCoefficient (cartierSectionZeroDivisor H s hs) (t : T) =
          if (t : T) ∈ Set.range η then 1 else 0) ∧
      LogPairIsKlt c'₀ (crepantPullbackFormUnit ρ hρ c₀ f₀ c'₀) d
        (cartierPullback ρ D + k • cartierSectionZeroDivisor H s hs) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨s, hs, q, η, hsm, hsnc', hcoeff, hklt'⟩ :=
    cartierIsGloballyGenerated_exists_klt_perturbation c'₀
      (crepantPullbackFormUnit ρ hρ c₀ f₀ c'₀)
      (crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover) H hH
      ξ hinj hξ hsnc hsupport d k hk
      (logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c₀ f₀ d D hklt c'₀)
  refine ⟨s, hs, q, η, hsm, hsnc', hcoeff, ?_⟩
  have heq :
      d • (smoothCanonicalDivisor c'₀ +
        principalCartierDivisor T (crepantPullbackFormUnit ρ hρ c₀ f₀ c'₀)) +
        (crepantBoundaryCartier ρ hρ c₀ f₀ d D c'₀ etaleCharts_cover +
          k • cartierSectionZeroDivisor H s hs) =
      cartierPullback ρ D + k • cartierSectionZeroDivisor H s hs := by
    rw [← add_assoc, crepantBoundaryCartier_smooth_recombine]
  simpa only [heq] using hklt'

end MixedFujita

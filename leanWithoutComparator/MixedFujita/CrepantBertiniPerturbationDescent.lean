/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.CartierBirationalZeroDivisors

/-!
On a normal source, an ordinarily globally generated divisor has an actual
small klt perturbation, provided an actual proper smooth model with SNC crepant
support is available. Pullback global generation, the actual Bertini section,
its zero divisor and its descent are proved internally. Comparison with all
test models uses local valuative extension instead of common resolutions.

The existence of the original SNC model is still an explicit input. The normal
source hypothesis is explicit; this module does not infer it from our klt predicate.
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

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Adding a source Cartier divisor adds its actual pullback to the crepant boundary. -/
theorem crepantBoundaryCartier_add_source (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D E : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) :
    crepantBoundaryCartier ρ hρ c f d (D + E) cT hT =
      crepantBoundaryCartier ρ hρ c f d D cT hT + cartierPullback ρ E := by
  unfold crepantBoundaryCartier
  rw [cartierPullback_add]
  abel

variable [CharZero K] [IsLocallyNoetherian X] [IsNoetherian T] [IsProper ρ]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

/-- Actual globally generated sections give source klt perturbations from a supplied proper
SNC model. No pulled section, zero-divisor identity, common model or descent proof is supplied. -/
theorem logPairIsKlt_exists_source_perturbation_of_crepant_snc_model
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (k : ℕ) (hk : k < d) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      LogPairIsKlt c f d (D + k • cartierSectionZeroDivisor H s hs) := by
  classical
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  obtain ⟨s, hs, q, η, hη, hηinj, _, _, hsnc', _, hdis, _, hcoeff, _, _⟩ :=
    cartierIsGloballyGenerated_exists_boundary_compatible_perturbation B (cartierPullback ρ H)
      (cartierIsGloballyGenerated_cartierPullback ρ H hH) ξ hsnc hsupport
  obtain ⟨t, ht, _, hzero⟩ := proper_birational_exists_section_zeroDivisor_descent
    ρ hnorm hρ.2 H s hs
  refine ⟨t, ht, ?_⟩
  have hinj' : Function.Injective (Fin.append ξ η) :=
    Fin.append_injective_iff.mpr ⟨hinj, hηinj, fun i j h =>
      Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨j, h.symm⟩⟩
  have hprime : ∀ i, Order.coheight (Fin.append ξ η i) = 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hξ j
    · simpa using hη j
  have hboundary : crepantBoundaryCartier ρ hρ c f d
      (D + k • cartierSectionZeroDivisor H t ht) cT etaleCharts_cover =
        B + k • cartierSectionZeroDivisor (cartierPullback ρ H) s hs := by
    rw [crepantBoundaryCartier_add_source, cartierPullback_nsmul, hzero]
  have hsupp' : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range (Fin.append ξ η) →
      cartierCoefficient (B + k • cartierSectionZeroDivisor (cartierPullback ρ H) s hs) (z : T) = 0 := by
    intro z hz
    have hold : (z : T) ∉ Set.range ξ := by
      rintro ⟨i, hi⟩
      exact hz ⟨Fin.castAdd q i, by simpa using hi⟩
    have hnew : (z : T) ∉ Set.range η := by
      rintro ⟨j, hj⟩
      exact hz ⟨Fin.natAdd r j, by simpa using hj⟩
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, hsupport z hold, hcoeff z,
      ite_eq_right hnew, mul_zero, add_zero]
  have hupper := cartierSection_signed_perturbation_coefficient_lt B (cartierPullback ρ H)
    s hs ξ η hdis hsupport hcoeff d k hk
      (logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT)
  apply logPairIsKlt_of_crepant_snc_model ρ hρ c f d (by omega)
    (D + k • cartierSectionZeroDivisor H t ht) cT (Fin.append ξ η) hinj' hprime hsnc'
  · simpa only [hboundary] using hsupp'
  · intro i
    simpa only [hboundary] using hupper ⟨Fin.append ξ η i, hprime i⟩

end MixedFujita

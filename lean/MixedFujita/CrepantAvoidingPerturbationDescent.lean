/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionPullbackAvoidance
public import MixedFujita.CartierAvoidingSNCBoundaryPerturbation

/-!
Actual klt perturbations on a normal source can simultaneously avoid finitely
many arbitrary source points. Proper dominance chooses finite representatives
on the supplied SNC model, Bertini avoids them, and the actual stalk criterion
descends nonvanishing. Existence of the original SNC model remains an input.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Given an actual SNC model, ordinary source global generation supplies an actual source
klt perturbation avoiding any finite set of arbitrary scheme points. -/
theorem logPairIsKlt_exists_source_perturbation_avoiding_of_crepant_snc_model
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (k : ℕ) (hk : k < d) (Z : Set X) (hZ : Z.Finite) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      LogPairIsKlt c f d (D + k • cartierSectionZeroDivisor H s hs) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  obtain ⟨W, hW, hlifts⟩ := proper_dominant_exists_finite_point_lifts ρ Z hZ
  obtain ⟨s, hs, q, η, _, hinj', hprime, hsnc', hsupp, hupper, havoid⟩ :=
    cartierIsGloballyGenerated_exists_signed_snc_perturbation_avoiding B (cartierPullback ρ H)
      (cartierIsGloballyGenerated_cartierPullback ρ H hH) ξ hinj hξ hsnc hsupport d k hk
      (logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT) W hW
  obtain ⟨t, ht, hpull, hzero⟩ := proper_birational_exists_section_zeroDivisor_descent
    ρ hnorm hρ.2 H s hs
  refine ⟨t, ht, ?_, ?_⟩
  · have hboundary : crepantBoundaryCartier ρ hρ c f d
        (D + k • cartierSectionZeroDivisor H t ht) cT etaleCharts_cover =
          B + k • cartierSectionZeroDivisor (cartierPullback ρ H) s hs := by
      rw [crepantBoundaryCartier_add_source, cartierPullback_nsmul, hzero]
    apply logPairIsKlt_of_crepant_snc_model ρ hρ c f d (by omega)
      (D + k • cartierSectionZeroDivisor H t ht) cT (Fin.append ξ η) hinj' hprime hsnc'
    · simpa only [hboundary] using hsupp
    · intro i
      simpa only [hboundary] using hupper ⟨Fin.append ξ η i, hprime i⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hlifts x hx
    have h := havoid y hy
    rw [← hpull, cartierDominantPullbackSection_zeroLocus] at h
    simpa only [Set.mem_preimage, hxy] using h

end MixedFujita

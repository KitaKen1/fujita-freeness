/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBasePointRoundupIntegerKlt
public import MixedFujita.CanonicalSubKltGlobalBaseTests
public import MixedFujita.SubKltDiscriminantCoefficients
public import MixedFujita.SNCBoundaryRoundup

/-!
Identify the actual relevant-prime integer coefficient lattice with the
roundup of the negative canonical discriminant coefficient. The threshold
is the existing canonical local base-prime threshold, not a global fixed-
divisor threshold. The joint SNC model and its actual effective roundup can
also be constructed internally from the original signed klt pair. Global
direct-image sheaf extension and moduli positivity are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (η : CodimensionOnePoint Y)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
  (H : CartierDivisor Y) (hH : H.IsEffective) (hHη : cartierCoefficient H (η : Y) = 1)

include hH hHη

/-- On a supplied actual joint model, the local integer coefficient lattice
is cut out exactly by the negative canonical discriminant roundup. -/
theorem snc_roundup_integer_coefficients_iff_canonical_base_prime_bound
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hHsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (cartierPullback g H)) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (p : ℕ) :
    (∀ t : CodimensionOnePoint T, (η : Y) ∈ closure ({(ρ ≫ g) (t : T)} : Set Y) →
      0 ≤ cartierCoefficient (E - p • cartierPullback (ρ ≫ g) H) (t : T)) ↔
        (p : ℤ) ≤ ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉ := by
  letI := hnormY (η : Y)
  letI : Nonempty (⊤ : Y.Opens) := ⟨⟨(η : Y), by trivial⟩⟩
  letI : IsDominant (⊤ : Y.Opens).ι :=
    ⟨(⊤ : Y.Opens).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have htest : LogPairIsKltOverBasePoint g (η : Y) c f d
      (D + (d * p) • cartierPullback g H) ↔
      (p : ℚ) < canonicalSubKltBasePrimeThreshold g η c f d hd D hklt := by
    simpa only [one_mul, one_nsmul, Nat.cast_one, div_one] using
      canonicalSubKltBasePrimeThreshold_global_klt_tests g η c f d hd D hklt
        ⊤ (by trivial) H hHη (cartierPullback_effective_of_effective _ H hH) p 1 (by omega)
  have hlocal := snc_roundup_integer_coefficients_overBasePoint_iff_klt ρ hρ g (η : Y)
    c f d hd D (cartierPullback g H) cT ξ hinj hξ hsnc hsupport hHsupport E hE p
  have hbound := (hlocal.trans htest).trans
    (integer_lt_threshold_iff_le_discriminant_roundup (p : ℤ)
      (canonicalSubKltBasePrimeThreshold g η c f d hd D hklt))
  simpa only [cartierPullback_comp, subKltBasePrimeDiscriminantCoefficients] using hbound

/-- From the original signed klt pair and a normalized effective base divisor,
construct the actual joint SNC source, effective roundup and all integer local
pole bounds with the canonical discriminant coefficient, without supplying
any model or threshold-computing prime. -/
theorem exists_snc_roundup_canonical_base_prime_integer_bound :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (E : CartierDivisor T),
      E.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
        ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      ∀ p : ℕ,
        (∀ t : CodimensionOnePoint T, (η : Y) ∈ closure ({(ρ ≫ g) (t : T)} : Set Y) →
          0 ≤ cartierCoefficient (E - p • cartierPullback (ρ ≫ g) H) (t : T)) ↔
          (p : ℤ) ≤ ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉ := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hHsupp⟩ :=
    exists_proper_snc_model_with c f d D (fun _ : PUnit.{1} => cartierPullback g H)
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  haveI : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  haveI : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨E, heff, hE⟩ := exists_effective_snc_boundary_roundup
    (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) d hd ξ hinj hcoh hsnc hsupp
    (fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hcoh i⟩)
  refine ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, E, heff, hE, ?_⟩
  intro p
  exact snc_roundup_integer_coefficients_iff_canonical_base_prime_bound g hnormY η
    c f d hd D hklt H hH hHη ρ hρ cT ξ hinj hcoh hsnc hsupp (hHsupp PUnit.unit) E hE p

end MixedFujita

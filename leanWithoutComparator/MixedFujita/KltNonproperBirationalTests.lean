/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.HironakaSNCModelExistence

/-!
All-model klt also bounds actual smooth birational tests which are not proper.
Construct a proper SNC model internally and use local birational extensions.
Consequently the crepant pair pulls back to every birational source, including
actual open immersions, without treating its composite test map as proper.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A proper-model klt condition controls every actual smooth birational test. -/
theorem logPairIsKlt_discrepancy_bound_on_birational_test
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (u : CodimensionOnePoint U) :
    -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (u : U) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  exact crepant_snc_actual_test_discrepancy_bound ρ hρ c f d hd D cT ξ hinj hcoh hsnc hsupp
    (fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hcoh i⟩)
    σ hσ cU u

/-- The base-point guard is preserved for smooth birational tests without properness. -/
theorem logPairIsKltOverBasePoint_discrepancy_bound_on_birational_test
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKltOverBasePoint g η c f d D)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (u : CodimensionOnePoint U)
    (hη : η ∈ closure ({(σ ≫ g) (u : U)} : Set Y)) :
    -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (u : U) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  exact crepant_snc_actual_test_discrepancy_bound_overBasePoint ρ hρ g η c f d hd D cT
    ξ hinj hcoh hsnc hsupp
    ((logPairIsKltOverBasePoint_iff_crepant_snc_coefficients
      ρ hρ g η c f d hd D cT ξ hinj hcoh hsnc hsupp).mp hklt) σ hσ cU u hη

variable {Z : Scheme.{u}} [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

/-- Crepant klt ascends along an arbitrary actual birational map, including an open immersion. -/
theorem logPairIsKlt_crepant_pullback_without_properness
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cZ : EtaleChart K Z n) :
    LogPairIsKlt cZ (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D) := by
  intro U _ _ _ _ σ _ _ _ hσ cU u hu
  rw [← logDiscrepancyDivisor_comp j σ hj hσ c f d D cZ cU etaleCharts_cover]
  exact logPairIsKlt_discrepancy_bound_on_birational_test c f d hd D hklt
    (σ ≫ j) (dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ) cU ⟨u, hu⟩

/-- Base-point-filtered klt ascends with the actual pulled rational top form. -/
theorem logPairIsKltOverBasePoint_crepant_pullback_without_properness
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKltOverBasePoint g η c f d D) (cZ : EtaleChart K Z n) :
    LogPairIsKltOverBasePoint (j ≫ g) η cZ (crepantPullbackFormUnit j hj c f cZ) d
      (cartierPullback j D) := by
  intro U _ _ _ _ σ _ _ _ hσ cU u hu hη
  rw [← logDiscrepancyDivisor_comp j σ hj hσ c f d D cZ cU etaleCharts_cover]
  apply logPairIsKltOverBasePoint_discrepancy_bound_on_birational_test g η c f d hd D hklt
    (σ ≫ j) (dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ) cU ⟨u, hu⟩
  simpa only [Category.assoc] using hη

end MixedFujita

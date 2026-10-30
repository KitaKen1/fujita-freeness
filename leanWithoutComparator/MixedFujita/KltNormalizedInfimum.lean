/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltGlobalMinimizer
public import MixedFujita.SNCWeightProfileExistence
public import MixedFujita.GlobalMinimizerHyperplane

/-!
The positive lower bound for the normalized infimum and global attainment from an infimum gap.
These interfaces let the general klt estimates feed the existing point-centre limit argument.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The normalized infimum is uniformly bounded below by a positive constant for large degrees. -/
theorem klt_ample_normalizedInfimum_ge (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤), ∀ {t : ℝ}, 0 < t → t ≤ b →
        κ ≤ sncWeightInfimum cY fY d D₀ (j • A) x N t j / N := by
  obtain ⟨κ, hκ, hκ1, hev⟩ :=
    klt_ample_minimizationFunctional_bound hn cY fY d hd D₀ A hklt hA hb
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hev] with j hj
  intro x N hN B₀ t ht htb
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr]
  apply le_sncWeightInfimum cY fY d D₀ (j • A) x N t j
    ⟨N, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • A) x B₀ t j⟩
  intro B p hp
  have h := (hj x hN B p hp ht htb).2
  unfold minimizationFunctional at h
  exact (le_div_iff₀ hNr).mp h

/-- An infimum gap gives an actual global minimizer with the same gap, uniformly in t and x.
No point-centre property is assumed here. -/
theorem klt_ample_global_minimizer_of_infimum_gap (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤), ∀ {t δ : ℝ},
        0 < t → t ≤ b → 0 < δ → RealizationSetsZariskiClosed cY fY d D₀ (j • A) x →
        sncWeightInfimum cY fY d D₀ (j • A) x N t j ≤ (N : ℝ) * (1 - δ) →
        ∃ B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
            (∀ B' : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
              ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
                (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
                  ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) := by
  obtain ⟨κ, -, -, hev⟩ := klt_ample_sncWeightInfimum_attained hn cY fY d hd D₀ A hklt hA hb
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  filter_upwards [hev] with j hj
  intro x N hN B₀ t δ ht htb hδ hclosed hgap
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hinf : sncWeightInfimum cY fY d D₀ (j • A) x N t j < N :=
    hgap.trans_lt (by nlinarith)
  obtain ⟨B, p, hp, heq, -, -⟩ := hj x hN ht htb hclosed
    ⟨N, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • A) x B₀ t j⟩ hinf
  exact ⟨B, p, hp, fun B' p' hp' =>
    heq.trans_le (sncWeightInfimum_le cY fY d D₀ (j • A) x t j B' hp'), heq.le.trans hgap⟩

end MixedFujita

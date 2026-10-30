/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltWeightDiscrepancyInterval
public import MixedFujita.BasisAttainment
public import MixedFujita.SNCWeightInfimum

/-!
Global attainment for a projective klt pair and an arbitrary ample Cartier divisor.
The bounds of section 3.1 discharge the compactness hypotheses of BasisAttainment.
Only closedness of the realization sets and an interior datum remain as hypotheses.
An equivalent infimum formulation explicitly requires a nonempty set of objective values:
the infimum of an empty set must not supply the interior condition.
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

/-- Uniform klt attainment for any ample divisor, conditional on closedness and one interior
profile. The discrepancy bounds are conclusions, rather than additional hypotheses. -/
theorem klt_ample_exists_global_sncWeight_minimizer (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ C : ℕ, 1 ≤ C ∧ ∀ᶠ j : ℕ in atTop,
      ∀ (x : Y) {N : ℕ}, 0 < N → ∀ {t δ : ℝ},
        0 < t → t ≤ b → 0 < δ → δ < 1 →
        RealizationSetsZariskiClosed cY fY d D₀ (j • A) x →
        (∃ B₀ : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∃ p₀ ∈ sncWeightProfiles cY fY d D₀ (j • A) x B₀,
            (∑ i, Real.exp (p₀.1 / t - p₀.2 i / j)) ≤ (N : ℝ) * (1 - δ)) →
        ∃ B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
            (∀ B' : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
              ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
                (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
                  ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (N : ℝ) * (1 - δ) ∧
            -Real.log (1 - δ) / C ≤ p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) ∧
            ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ (C : ℝ) * j * p.1 := by
  obtain ⟨κ, hκ, hκ1, C, hC, hev⟩ :=
    klt_ample_sncWeightProfiles_bounds hn cY fY d hd D₀ A hklt hA hb
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  refine ⟨κ, hκ, hκ1, C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x N hN t δ ht htb hδ hδ1 hclosed hstart
  obtain ⟨B₀, p₀, hp₀, hval₀⟩ := hstart
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hlog : 0 < -Real.log (1 - δ / 2) / C := by
    have h : Real.log (1 - δ / 2) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hCpos
  have hlevel : (N : ℝ) * (1 - δ) < (N : ℝ) * (1 - δ / 2) := by nlinarith
  obtain ⟨B, p, hp, hmin⟩ := exists_basis_sncWeightProfile_minimizer
    cY fY d hd D₀ hklt (j • A) x hN B₀ hclosed ht hjpos hlog
    (L := (N : ℝ) * (1 - δ / 2)) (aHigh := 2 * b * Real.log (1 / κ))
    (Cq := (C : ℝ) * j)
    (fun B p hp hL => hj x hN B p hp ht htb (by linarith) hL)
    ⟨B₀, p₀, hp₀, hval₀.trans_lt hlevel, hval₀.trans_lt (by nlinarith)⟩
  have hpval := (hmin B₀ p₀ hp₀).trans hval₀
  exact ⟨B, p, hp, hmin, hpval, hj x hN B p hp ht htb hδ.le hpval⟩

/-- If the nonempty objective set has infimum below N, closedness implies attainment for all
sufficiently large degrees. The minimizing discrepancy is strictly positive and uniformly bounded
above. No smoothness of the source or prescribed positive gap is assumed. -/
theorem klt_ample_sncWeightInfimum_attained (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop,
      ∀ (x : Y) {N : ℕ}, 0 < N → ∀ {t : ℝ}, 0 < t → t ≤ b →
        RealizationSetsZariskiClosed cY fY d D₀ (j • A) x →
        (sncWeightObjectiveValues cY fY d D₀ (j • A) x N t j).Nonempty →
        sncWeightInfimum cY fY d D₀ (j • A) x N t j < N →
        ∃ B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) =
              sncWeightInfimum cY fY d D₀ (j • A) x N t j ∧
            0 < p.1 ∧ p.1 ≤ 2 * b * Real.log (1 / κ) := by
  obtain ⟨κ, hκ, hκ1, C, hC, hev⟩ :=
    klt_ample_exists_global_sncWeight_minimizer hn cY fY d hd D₀ A hklt hA hb
  refine ⟨κ, hκ, hκ1, ?_⟩
  filter_upwards [hev] with j hj
  intro x N hN t ht htb hclosed hne hinf
  obtain ⟨val, ⟨B₀, p₀, hp₀, rfl⟩, hval⟩ := exists_lt_of_csInf_lt hne hinf
  let S : ℝ := ∑ i, Real.exp (p₀.1 / t - p₀.2 i / j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let δ : ℝ := (1 - S / N) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (sub_pos.mpr ((div_lt_one hNpos).mpr hval))
  have hδ1 : δ < 1 := by
    have h : 0 ≤ S / (N : ℝ) := div_nonneg hS hNpos.le
    dsimp [δ]
    linarith
  have hstart : S ≤ (N : ℝ) * (1 - δ) := by
    dsimp [δ]
    field_simp
    nlinarith [hval]
  obtain ⟨B, p, hp, hmin, -, hlow, hhigh, -⟩ :=
    hj x hN ht htb hδ hδ1 hclosed ⟨B₀, p₀, hp₀, hstart⟩
  refine ⟨B, p, hp, le_antisymm ?_ (sncWeightInfimum_le cY fY d D₀ (j • A) x t j B hp),
    ?_, hhigh⟩
  · exact le_sncWeightInfimum cY fY d D₀ (j • A) x N t j hne hmin
  · have hlog : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
    have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
    exact (div_pos (neg_pos.mpr hlog) hCpos).trans_le hlow

end MixedFujita

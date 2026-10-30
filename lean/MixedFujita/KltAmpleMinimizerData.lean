/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltGlobalMinimizer
public import MixedFujita.SNCWeightProfileExistence
public import MixedFujita.GlobalMinimizerData
public import MixedFujita.KltMinimizerDataPowers

/-!
Reduction of the general ample klt minimizer-data problem to closedness, the interior condition,
and the point-centre property. Uniform estimates, nonemptiness of the objective set and
divisibility of the chosen degree are no longer extra inputs. After attainment at one degree,
the first-order minimizer construction gives data for m = 1; powers of its sections give data
for every m >= 1. This does not prove any of the three remaining geometric hypotheses.
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

/-- For any ample divisor on a projective klt source, closedness, an interior infimum and
point centres of the global minimizers give minimizer data for every divisibility condition.
The starting degree need not itself be divisible by the requested m₀. -/
theorem klt_ample_kltIsolationMinimizerData_of_pointCentre (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
      ∀ {t : ℝ}, 0 < t → t ≤ b → (d : ℝ) * t < 1 →
        RealizationSetsZariskiClosed cY fY d D₀ (j • A) x →
        sncWeightInfimum cY fY d D₀ (j • A) x N t j < N →
        (∀ B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∀ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
            (∀ B' : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
              ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
                (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
                  ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
            SNCWeightProfileHasPointCentre cY fY d D₀ (j • A) x B p) →
        ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  obtain ⟨κ, -, -, hev⟩ :=
    klt_ample_sncWeightInfimum_attained hn cY fY d hd D₀ A hklt hA hb
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x N hN B₀ t ht htb hdt hclosed hinf hpc m₀ hm₀
  have hne : (sncWeightObjectiveValues cY fY d D₀ (j • A) x N t j).Nonempty :=
    ⟨N, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • A) x B₀ t j⟩
  obtain ⟨B, p, hp, heq, -, -⟩ := hj x hN ht htb hclosed hne hinf
  have hmin : ∀ B' : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
      ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
        (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
          ∑ i, Real.exp (p'.1 / t - p'.2 i / j) :=
    fun B' p' hp' => heq.trans_le (sncWeightInfimum_le cY fY d D₀ (j • A) x t j B' hp')
  have hdata := kltIsolationMinimizerData_of_minimal_sncWeightProfile cY fY d hd D₀ hklt
    A 1 x j hj1 (one_dvd j) hN B ht hdt hp (hmin B) (heq.trans_lt hinf) (hpc B p hp hmin)
  exact kltIsolationMinimizerData_of_kltIsolationMinimizerData cY fY d D₀ A x hdata m₀ hm₀

end MixedFujita

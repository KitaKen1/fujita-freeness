/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierLocalEquationLocus
public import MixedFujita.KltChartInteriorProfile
public import MixedFujita.KltAmpleMinimizerData
public import MixedFujita.VeryGeneralClosedPoint
public import MixedFujita.VeryAmpleNumericalBound

/-!
The specialization step of the klt interior condition (section 7).
A very general closed point can be chosen in a constructed boundary-free chart open with
infimum at least that of any prescribed point x. Thus an ordinary-point interior inequality on
that open transfers to x, including singular x. Closedness of rational profile loci and the
ordinary-point numerical inequality are explicit hypotheses. With tuple closedness and point
centres this supplies isolation data, using the attained klt minimum of check-89.
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
  {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- A boundary-free smooth closed point whose objective infimum dominates that of x.
The closed profile loci are hypotheses; the good open and its point are constructed. -/
theorem exists_boundaryFree_closedPoint_sncWeightInfimum_comparison
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {N : ℕ} (hN : 0 < N) (B₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    {j : ℕ} (hj : 0 < j) (t : ℝ)
    (hcl : ∀ α : Fin N → ℚ, IsClosed {y : Y |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y}) (x : Y) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ∈ cY.U ∧ D₀.IsLocalEquationAt y (fY ^ d) ∧
      sncWeightInfimum cY fY d D₀ D x N t j ≤ sncWeightInfimum cY fY d D₀ D y N t j := by
  obtain ⟨V, hV, hVne, -, hVD⟩ := exists_dense_open_localEquation D₀ (fY ^ d) cY.U cY.nonempty
  obtain ⟨Z, hZcl, hZgen, hcomp⟩ := sncWeight_specialization_comparison_of_closed cY fY hd D₀ D
    hklt hN hj t hcl (genericPoint_specializes x)
  obtain ⟨y, hycl, hyV, hyZ⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K)
    (V : Set Y) V.isOpen (by obtain ⟨y⟩ := hVne; exact ⟨y.1, y.2⟩) Z hZcl
    (fun k heq => hZgen k (by rw [heq]; trivial))
  have hne : (sncWeightObjectiveValues cY fY d D₀ D y N t j).Nonempty :=
    ⟨N, sncWeightObjectiveValues_natCast_mem cY fY d D₀ D y B₀ t j⟩
  exact ⟨y, hycl, hV hyV, hVD y hyV, hcomp y hne hyZ⟩

/-- A uniform ordinary-point interior estimate on the boundary-free chart locus transfers to
every prescribed point, including singular points. This is the transfer part of (7). -/
theorem sncWeightInfimum_le_of_boundaryFree_interior (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ D : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {N : ℕ} (hN : 0 < N) (B₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    {j : ℕ} (hj : 0 < j) {t δ : ℝ} (ht : 0 < t)
    (hcl : ∀ α : Fin N → ℚ, IsClosed {y : Y |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y})
    (hstart : ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ cY.U →
      D₀.IsLocalEquationAt y (fY ^ d) →
      ∃ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (lam : ℝ), 0 ≤ lam ∧
        minimizationFunctional j t (lam * n)
          (fun i => lam * ((cartierSectionVanishingOrder D y (B i)).toNat : ℝ)) ≤ 1 - δ)
    (x : Y) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤ (N : ℝ) * (1 - δ) := by
  obtain ⟨y, hycl, hyU, hyD, hcomp⟩ := exists_boundaryFree_closedPoint_sncWeightInfimum_comparison
    cY fY d hd D₀ D hklt hN B₀ hj t hcl x
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) cY.isAffine y hyU hycl
  obtain ⟨B, lam, hlam, hstart⟩ := hstart y hycl hyU hyD
  exact hcomp.trans (sncWeightInfimum_le_of_chart_interior hn cY fY d hd D₀ D hN B y hyU β
    hyD hj ht hlam hstart)

variable [IsLocallyNoetherian Y]

/-- The klt isolation data from ordinary-point (7) on the boundary-free chart locus, closedness
in the point and tuple variables, and point centres of global minimizers. The numerical
ordinary-point inequality and these geometric closedness/centre hypotheses remain explicit. -/
theorem klt_ample_minimizerData_of_boundaryFree_interior (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ j : ℕ in atTop, ∀ (x : Y) {N : ℕ}, 0 < N →
      ∀ _B₀ : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
      ∀ {t δ : ℝ}, 0 < t → t ≤ b → (d : ℝ) * t < 1 → 0 < δ →
        RealizationSetsZariskiClosed cY fY d D₀ (j • A) x →
        (∀ α : Fin N → ℚ, IsClosed {y : Y |
          (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A) N y}) →
        (∀ y : Y, IsClosed ({y} : Set Y) → y ∈ cY.U →
          D₀.IsLocalEquationAt y (fY ^ d) →
          ∃ (B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤)) (lam : ℝ), 0 ≤ lam ∧
            minimizationFunctional j t (lam * n)
              (fun i => lam * ((cartierSectionVanishingOrder (j • A) y (B i)).toNat : ℝ)) ≤
                1 - δ) →
        (∀ B : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
          ∀ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
            (∀ B' : Module.Basis (Fin N) K Γ((j • A).sheaf, ⊤),
              ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
                (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤
                  ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
            SNCWeightProfileHasPointCentre cY fY d D₀ (j • A) x B p) →
        ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  have hev := klt_ample_kltIsolationMinimizerData_of_pointCentre hn cY fY d hd D₀ A hklt hA hb
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x N hN B₀ t δ ht htb hdt hδ hclosed hcl hstart hpc
  have hbound := sncWeightInfimum_le_of_boundaryFree_interior hn cY fY d hd D₀ (j • A) hklt
    hN B₀ hj1 ht hcl hstart x
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinf : sncWeightInfimum cY fY d D₀ (j • A) x N t j < N :=
    hbound.trans_lt (by nlinarith)
  exact hj x hN B₀ ht htb hdt hclosed hinf hpc

end MixedFujita

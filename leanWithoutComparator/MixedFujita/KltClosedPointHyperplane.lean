/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHyperplanePointCentre
public import MixedFujita.ClosedPointProfiles
public import MixedFujita.PointClosureHyperplaneRestriction
public import MixedFujita.KltMinimizerDataShift

/-!
General klt point centres from tuple closedness and closedness only at closed points. This wrapper reuses
the existing degree comparison and the countable bad-locus argument, and constructs the objective
at every point using the zero weight. No smoothness or zero-boundary assumption is used.
The last theorem transfers the resulting profile through a principal shift to an ample divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
  {N n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

set_option quotPrecheck false

local notation "J" => projectiveHyperplaneCartier e g hg hggen
local notation "Nsec" => (fun j : ℕ => Module.finrank K Γ((j • J).sheaf, ⊤))

/-- Tuple and point closedness give a minimal profile with point centre, conditional on the
interior gap and restricted growth. The klt boundary and source are arbitrary. -/
theorem klt_projectiveHyperplane_exists_pointCentre_of_closedPoints
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = n + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • J).sheaf, ⊤), FiniteDimensional K V ∧
          ((s : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • J) η V)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • J) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Nsec j) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ (j • J) (Nsec j) y})
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      sncWeightInfimum cY fY d D₀ (j • J) x (Nsec j) t j ≤ (Nsec j : ℝ) * (1 - δ)) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ j : ℕ, 1 ≤ j ∧ 0 < Nsec j ∧
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
        ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
          (∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) < (Nsec j : ℝ) ∧
          SNCWeightProfileHasPointCentre cY fY d D₀ (j • J) x B p := by
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdimY hn
  have hNpos : ∀ j : ℕ, 0 < Nsec j := by
    intro j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  refine klt_projectiveHyperplane_exists_minimal_pointCentre e g hg hggen he hn cY fY d hd D₀
    hklt x hxc hgx hb s hs hsb ht₀ hδ hδ1
    (fun w _ => exists_nat_topologicalKrullDim_closure_eq hdimY w)
    (projectiveHyperplane_degreeCondition_of_restrictedGrowth e g hg hggen he x s hgrow)
    hclosed hstart ?_
  filter_upwards [hclosedPt, eventually_ge_atTop 1] with j hj hj1
  intro t _ _ w hwx _
  obtain ⟨Z, hZ, hwZ, hcomp⟩ := sncWeight_specialization_comparison_of_closedPoints cY fY hd D₀
    (j • J) hklt (hNpos j) hj1 t hj hxc hwx
  refine ⟨⋂ i, (Z i)ᶜ, closedPointsDenseOver_of_countable Z hZ hwZ, ?_⟩
  intro y hyc hy _
  have := hfin j
  exact hcomp y hyc ⟨_, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • J) y
    (Module.finBasis K _) t j⟩ (Set.mem_iInter.mp hy)

/-- Principal shifts transfer the klt point-centre construction to A. The budget d*l*b ≤ 1
leaves strict room at the parameter t < b, and section powers give every m₀ ≥ 1. -/
theorem klt_projectiveHyperplane_minimizerData_shift_of_closedPoints
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {l : ℕ} (hl : 1 ≤ l) (φ : Y.functionFieldˣ) (hlA : l • A = J + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (hbudget : (d : ℝ) * l * b ≤ 1)
    (s : ℕ) (hs : 1 ≤ s) (hsb : (s : ℝ) * b = n + 1)
    (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • J).sheaf, ⊤), FiniteDimensional K V ∧
          ((s : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • J) η V)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • J) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Nsec j) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ (j • J) (Nsec j) y})
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      sncWeightInfimum cY fY d D₀ (j • J) x (Nsec j) t j ≤ (Nsec j : ℝ) * (1 - δ)) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  obtain ⟨t, -, ht, htb, j, hj, hN, B, p, hp, hmin, hlt, hpc⟩ :=
    klt_projectiveHyperplane_exists_pointCentre_of_closedPoints e g hg hggen he hn cY fY d hd
      D₀ hklt x hxc hgx hb s hs hsb ht₀ hδ hδ1 hgrow hclosed hclosedPt hstart
  have hdl : (0 : ℝ) < (d : ℝ) * l := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < l := by exact_mod_cast hl
    positivity
  have hdt : (d : ℝ) * l * t < 1 :=
    (mul_lt_mul_of_pos_left htb hdl).trans_le hbudget
  have hdata := kltIsolationMinimizerData_of_minimal_sncWeightProfile_shift cY fY d hd D₀ hklt
    J A φ hlA x j hj hN B ht hdt hp hmin hlt hpc
  exact kltIsolationMinimizerData_of_kltIsolationMinimizerData cY fY d D₀ A x hdata

end MixedFujita

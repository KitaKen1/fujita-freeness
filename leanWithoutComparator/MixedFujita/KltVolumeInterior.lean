/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltBoundaryFreeNumericalStart

/-!
The klt interior gap from strict lower growth of section dimensions and closed rational-profile
loci. A single good closed point transfers every rational profile at all sufficiently large
degrees. The transfer is independent of t, so the numerical Taylor start at that point supplies
one positive gap on a fixed t-interval for the specified, possibly singular, point.
Closedness itself remains a hypothesis; the numerical start is proved from dimension growth.
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

omit [CharZero K] in
/-- One boundary-free closed point transfers all rational profiles at every sufficiently large
degree to x. No real t is included in the countable set of conditions. -/
theorem exists_boundaryFree_closedPoint_all_degree_profile_transfer
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ A : CartierDivisor Y)
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y) :
    ∃ y : Y, IsClosed ({y} : Set Y) ∧ y ∈ cY.U ∧ D₀.IsLocalEquationAt y (fY ^ d) ∧
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
          (Module.finrank K Γ((j • A).sheaf, ⊤)) y →
        (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
          (Module.finrank K Γ((j • A).sheaf, ⊤)) x := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcl
  let I := Σ j : ℕ, Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ
  let R : I → Set Y := fun a => {y : Y |
    (fun i => (a.2 i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (a.1 • A)
      (Module.finrank K Γ((a.1 • A).sheaf, ⊤)) y}
  obtain ⟨V, hV, hVne, -, hVD⟩ := exists_dense_open_localEquation D₀ (fY ^ d) cY.U cY.nonempty
  obtain ⟨y, hycl, hyV, hybad⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K)
    (V : Set Y) V.isOpen (by obtain ⟨y⟩ := hVne; exact ⟨y.1, y.2⟩)
    (fun a : {a : I // J ≤ a.1 ∧ R a ≠ Set.univ} => R a.1)
    (fun a => hJ a.1.1 a.2.1 a.1.2) (fun a => a.2.2)
  refine ⟨y, hycl, hV hyV, hVD y hyV, ?_⟩
  filter_upwards [eventually_ge_atTop J] with j hj
  intro α hα
  have hEq : R ⟨j, α⟩ = Set.univ := by
    by_contra h
    exact hybad ⟨⟨j, α⟩, hj, h⟩ hα
  change x ∈ R ⟨j, α⟩
  rw [hEq]
  trivial

variable [IsLocallyNoetherian Y]

/-- A strict dimension lower bound gives the klt infimum gap at every specified point, conditional
only on point-locus closedness. Neither a numerical start nor a Hilbert limit is an extra input. -/
theorem klt_ample_infimum_interior_of_dimension_lower (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤
      (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ))
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹)
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • A).sheaf, ⊤) ∧
      ∀ t, t₀ ≤ t → t ≤ b →
        sncWeightInfimum cY fY d D₀ (j • A) x
          (Module.finrank K Γ((j • A).sheaf, ⊤)) t j ≤
          (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) * (1 - δ) := by
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  obtain ⟨y, hycl, hyU, hyD, htransfer⟩ :=
    exists_boundaryFree_closedPoint_all_degree_profile_transfer cY fY d D₀ A hcl x
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hstart⟩ :=
    klt_boundaryFree_interior_start_of_dimension_lower hn cY fY d hd D₀ A hklt hA
      hc hb hN hvol y hycl hyU hyD
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) cY.isAffine y hyU hycl
  refine ⟨t₀, ht₀, ht₀b, δ, hδ, ?_⟩
  filter_upwards [htransfer, hstart, hN, eventually_ge_atTop 1] with j hjtr hjstart hjN hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hNpos : 0 < Module.finrank K Γ((j • A).sheaf, ⊤) := by
    exact_mod_cast (mul_pos hc (pow_pos hj0 n)).trans_le hjN
  refine ⟨hNpos, ?_⟩
  intro t ht₀t htb
  have ht : 0 < t := ht₀.trans_le ht₀t
  obtain ⟨B, hB⟩ := hjstart t ht₀t htb
  have hne : (sncWeightObjectiveValues cY fY d D₀ (j • A) y
      (Module.finrank K Γ((j • A).sheaf, ⊤)) t j).Nonempty :=
    ⟨_, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • A) y B t j⟩
  have hcomp := sncWeightInfimum_le_of_rational cY fY hd D₀ (j • A) hklt hNpos hj1 t hjtr hne
  exact hcomp.trans (sncWeightInfimum_le_of_chart_interior hn cY fY d hd D₀ (j • A)
    hNpos B y hyU β hyD hj1 ht hζ.le hB)

/-- The klt interior condition (7) from the exact strict-volume input of K-NF, with b = 1/d.
The point-locus closedness is still assumed; no numerical-start hypothesis remains. -/
theorem klt_ample_infimum_interior_of_knf_volume (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ n + ε) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y) :
    ∃ t₀, 0 < t₀ ∧ t₀ < 1 / (d : ℝ) ∧ ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • A).sheaf, ⊤) ∧
      ∀ t, t₀ ≤ t → t ≤ 1 / (d : ℝ) →
        sncWeightInfimum cY fY d D₀ (j • A) x
          (Module.finrank K Γ((j • A).sheaf, ⊤)) t j ≤
          (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) * (1 - δ) := by
  obtain ⟨ε, hε, hvol⟩ := hvol
  let c : ℝ := (((d : ℝ) * (n + 1)) ^ n + ε) / n.factorial
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hc : 0 < c := by dsimp [c]; positivity
  have hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤
      (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) := by
    filter_upwards [hvol] with j hj
    rw [cartierRestrictedDim_genericPoint] at hj
    simpa only [c, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_mul_eq_mul_div] using hj
  have hroot : (d : ℝ) * (n + 1) < (((d : ℝ) * (n + 1)) ^ n + ε) ^ (n : ℝ)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hnpos, Real.rpow_natCast]
    linarith
  have hfact : (n.factorial : ℝ) * c = ((d : ℝ) * (n + 1)) ^ n + ε := by
    dsimp [c]
    field_simp
  have hthreshold : (n : ℝ) / (1 / (d : ℝ)) <
      (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ := by
    rw [hfact]
    calc (n : ℝ) / (1 / (d : ℝ)) = (n : ℝ) * d := by field_simp
      _ = (n : ℝ) / (n + 1) * ((d : ℝ) * (n + 1)) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hroot (div_pos hnpos (by positivity))
  exact klt_ample_infimum_interior_of_dimension_lower hn cY fY d hd D₀ A hklt hA hc
    (by positivity) hN hthreshold hcl x

/-- From the K-NF strict-volume input to isolation data for every m₀. Closedness in the tuple
and point variables and the general klt point-centre property remain explicit hypotheses. -/
theorem klt_ample_minimizerData_of_knf_volume (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ n + ε) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x)
    (hpc : ∀ᶠ j : ℕ in atTop, ∀ {t : ℝ}, 0 < t → t < 1 / (d : ℝ) →
      ∀ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        ∀ p ∈ sncWeightProfiles cY fY d D₀ (j • A) x B,
          (∀ B' : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
            ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • A) x B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
          SNCWeightProfileHasPointCentre cY fY d D₀ (j • A) x B p) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨t₀, ht₀, ht₀b, δ, hδ, hstart⟩ :=
    klt_ample_infimum_interior_of_knf_volume hn cY fY d hd D₀ A hklt hA hvol hcl x
  have hdata := klt_ample_kltIsolationMinimizerData_of_pointCentre hn cY fY d hd D₀ A hklt hA
    (b := 1 / (d : ℝ)) (by positivity)
  have hfin : ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) :=
    cartierIsAmpleProj_finiteDimensional_nsmul (etaleChart_topologicalKrullDim cY) hn hA
  obtain ⟨j, hjdata, hjclosed, hjpc, hjN, hjstart⟩ :=
    (hdata.and (hclosed.and (hpc.and hstart))).exists
  let t : ℝ := (t₀ + 1 / (d : ℝ)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀t : t₀ ≤ t := by dsimp [t]; linarith
  have htb : t < 1 / (d : ℝ) := by dsimp [t]; linarith
  have hdt : (d : ℝ) * t < 1 := by
    have h := (lt_div_iff₀ hdpos).mp htb
    nlinarith
  have hNpos : (0 : ℝ) < Module.finrank K Γ((j • A).sheaf, ⊤) := by exact_mod_cast hjN
  have hinf : sncWeightInfimum cY fY d D₀ (j • A) x
      (Module.finrank K Γ((j • A).sheaf, ⊤)) t j < Module.finrank K Γ((j • A).sheaf, ⊤) :=
    (hjstart t ht₀t htb.le).trans_lt (by nlinarith)
  exact hjdata x hjN (Module.finBasis K Γ((j • A).sheaf, ⊤)) ht htb.le hdt hjclosed hinf
    (hjpc ht htb)

end MixedFujita

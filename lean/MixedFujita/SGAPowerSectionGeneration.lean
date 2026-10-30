/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANaturalGlobalSectionEquivalence
public import MixedFujita.SGAProjectivePowerGlobalGeneration

/-! 非被約源で点毎の正の生成冪から共通生成冪・全正倍数。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Actual module generation and the original SGA nonvanishing section
cover are equivalent in every natural degree on an arbitrary scheme. -/
theorem moduleIsGloballyGenerated_sga_iff_nonvanishing_cover
    {X : Scheme.{u}} (L : X.LineBundle) (n : ℕ) :
    moduleIsGloballyGenerated (L.toModules (n : ℤ)) ↔
      ∀ x : X, ∃ s : L.sections n, x ∈ L.nonvanishingLocus s := by
  constructor
  · intro h x
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [L.iSup_eq_top]; trivial)
    obtain ⟨t, ht⟩ := moduleIsGloballyGenerated_at_frame h x (L.U k) hk (sgaLineBundleOverFrameIso L n k)
    obtain ⟨s, rfl⟩ := (sgaNaturalSectionToModule_bijective L n).surjective t
    refine ⟨s, (L.mem_nonvanishingLocus s).mpr ⟨k, ?_⟩⟩
    unfold moduleOverFrameGlobalCoefficientGerm at ht
    rw [sgaNaturalSectionToModule_frame_coefficient] at ht
    exact (X.mem_basicOpen (s.val k) x hk).mpr ht
  · exact moduleIsGloballyGenerated_sga_of_nonvanishing_cover L n


/-- It is enough to generate at closed points: every point generalizes
a closed point and actual section nonvanishing opens contain generalizations. -/
theorem sga_positive_power_section_cover_of_closed_points
    {X : Scheme.{u}} [CompactSpace X] (L : X.LineBundle)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ n : ℕ, 0 < n ∧ ∃ s : L.sections n, x ∈ L.nonvanishingLocus s) :
    ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : L.sections n, x ∈ L.nonvanishingLocus s := by
  intro x
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure (Set.mem_singleton x)⟩
  obtain ⟨n, hn, s, hs⟩ := h z hzc
  exact ⟨n, hn, s, (specializes_iff_mem_closure.mpr hz).mem_open
    (L.nonvanishingLocus s).isOpen hs⟩


/-- Powers of sections in any natural degree, on the actual possibly
nonreduced scheme. -/
noncomputable def sgaNaturalSectionPow {X : Scheme.{u}} (L : X.LineBundle)
    {n : ℕ} (s : L.sections n) (j : ℕ) : L.sections (n * j) := by
  refine ⟨fun i => s.val i ^ j, ?_⟩
  intro i k
  simpa only [map_pow, mul_pow, pow_mul] using congrArg (fun a => a ^ j) (s.property i k)


/-- Every positive power preserves the actual SGA nonvanishing open. -/
theorem sgaNaturalSectionPow_nonvanishingLocus {X : Scheme.{u}} (L : X.LineBundle)
    {n : ℕ} (s : L.sections n) (j : ℕ) (hj : 0 < j) :
    L.nonvanishingLocus (sgaNaturalSectionPow L s j) = L.nonvanishingLocus s := by
  unfold Scheme.LineBundle.nonvanishingLocus
  apply iSup_congr
  intro i
  exact X.basicOpen_pow (s.val i) hj


/-- Compactness turns point-dependent positive generating powers into
one positive globally generated power. Its exponent is constructed as a
product of the finitely many selected exponents. -/
theorem sga_exists_positive_generated_power_of_power_section_cover
    {X : Scheme.{u}} [CompactSpace X] (L : X.LineBundle)
    (h : ∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s : L.sections n, x ∈ L.nonvanishingLocus s) :
    ∃ q : ℕ, 0 < q ∧ moduleIsGloballyGenerated (L.toModules (q : ℤ)) := by
  classical
  choose n hn s hs using h
  obtain ⟨B, hB⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (L.nonvanishingLocus (s x) : Set X))
    (fun x => (L.nonvanishingLocus (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hs x⟩)
  let q := B.prod n
  have hq : 0 < q := Finset.prod_pos (fun x _ => hn x)
  refine ⟨q, hq, moduleIsGloballyGenerated_sga_of_nonvanishing_cover L q ?_⟩
  intro x
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hB (Set.mem_univ x))
  obtain ⟨j, hj⟩ := Finset.dvd_prod_of_mem n hy
  have hjp : 0 < j := by
    by_contra hnot
    have hj0 : j = 0 := by omega
    rw [hj0, mul_zero] at hj
    exact (Nat.ne_of_gt hq) hj
  have hlocal : ∃ t : L.sections (n y * j), x ∈ L.nonvanishingLocus t := by
    refine ⟨sgaNaturalSectionPow L (s y) j, ?_⟩
    rwa [sgaNaturalSectionPow_nonvanishingLocus L (s y) j hjp]
  have he : n y * j = q := hj.symm
  exact (congrArg (fun t => ∃ s : L.sections t, x ∈ L.nonvanishingLocus s) he).mp hlocal


/-- A generated actual SGA power has generated positive multiples;
all nonvanishing loci are preserved exactly by the section powers. -/
theorem moduleIsGloballyGenerated_sga_positive_multiples
    {X : Scheme.{u}} (L : X.LineBundle) (q : ℕ)
    (h : moduleIsGloballyGenerated (L.toModules (q : ℤ)))
    (j : ℕ) (hj : 0 < j) : moduleIsGloballyGenerated (L.toModules ((q * j : ℕ) : ℤ)) := by
  apply moduleIsGloballyGenerated_sga_of_nonvanishing_cover
  intro x
  obtain ⟨s, hs⟩ := (moduleIsGloballyGenerated_sga_iff_nonvanishing_cover L q).mp h x
  refine ⟨sgaNaturalSectionPow L s j, ?_⟩
  rwa [sgaNaturalSectionPow_nonvanishingLocus L s j hj]

end MixedFujita

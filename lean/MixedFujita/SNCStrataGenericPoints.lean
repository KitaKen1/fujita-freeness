/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartStrataBertini
public import MixedFujita.CartierSectionBertini
public import MixedFujita.ToricExtractionDomination
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
Generic points of the strata of a simple normal crossing family (step 11, section 5.1 of the
manuscript: the centre of a weight and the choice of the closed point).

* Topology. In a quasi-sober T0 space every point y of a closed set C is a specialization of a
  point of C which is maximal for generization inside C (the generic point of an irreducible
  component of C through y). For the members of positive weight of a family of points of a scheme
  this gives the generic point of the component through y of their common stratum.
* Algebra. On an étale chart the coordinate stratum {x_a = 0 : a ∈ S} is flat over the polynomial
  ring in the remaining variables, which is a domain; so every other coordinate x_b is a
  nonzerodivisor on the stratum and lies in no minimal prime of the stratum ideal.
* Geometry. For a simple normal crossing family and a weight on its members, the generic point of
  a component of the stratum of the members of positive weight lies on no member of weight zero:
  the stratum is not contained in any other member. Hence the points of the component lying on
  another member form a proper closed subset, and a general closed point of the centre of the
  weight lies exactly on the members of positive weight.
* The closed point. Over an algebraically closed field, for every open set containing the generic
  point η of the stratum there is a closed point z of the closure of η in that open set with a
  simple normal crossing chart all of whose coordinates vanish at z and whose selected
  coordinates cut out exactly the members of positive weight: the setting of the tangent
  variation of section 5.1, where every crossing coordinate has positive weight.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Topology

/-- In a quasi-sober T0 space, every point of a closed set is a specialization of a point of the
set which is maximal for generization inside the set. -/
theorem exists_maximal_generization_of_mem_isClosed {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {C : Set X} (hC : IsClosed C) {y : X} (hy : y ∈ C) :
    ∃ η ∈ C, η ⤳ y ∧ ∀ η' ∈ C, η' ⤳ η → η' = η := by
  classical
  obtain ⟨t, ht, hyt, hmax⟩ := exists_preirreducible ({(⟨y, hy⟩ : C)} : Set C)
    isPreirreducible_singleton
  have hyt' : (⟨y, hy⟩ : C) ∈ t := hyt rfl
  have hirr : IsIrreducible (Subtype.val '' t : Set X) :=
    IsIrreducible.image (s := t) ⟨⟨_, hyt'⟩, ht⟩ _ continuous_subtype_val.continuousOn
  have hsub : closure (Subtype.val '' t : Set X) ⊆ C :=
    closure_minimal (by
      rintro _ ⟨p, -, rfl⟩
      exact p.property) hC
  have hgen := hirr.isGenericPoint_genericPoint_closure
  have hηmem : hirr.genericPoint ∈ closure (Subtype.val '' t : Set X) := by
    rw [← hgen.def]
    exact subset_closure rfl
  refine ⟨hirr.genericPoint, hsub hηmem, ?_, ?_⟩
  · rw [specializes_iff_mem_closure, hgen.def]
    exact subset_closure ⟨_, hyt', rfl⟩
  · intro η' hη'C hsp
    have hcl : closure (Subtype.val '' t : Set X) ⊆ closure ({η'} : Set X) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hsp))
        isClosed_closure
    have hcl'C : closure ({η'} : Set X) ⊆ C :=
      closure_minimal (Set.singleton_subset_iff.mpr hη'C) hC
    have ht' : IsPreirreducible (Subtype.val ⁻¹' closure ({η'} : Set X) : Set C) := by
      rw [isPreirreducible_iff_isClosed_union_isClosed]
      intro z₁ z₂ hz₁ hz₂ hcov
      obtain ⟨w₁, hw₁, rfl⟩ := isClosed_induced_iff.mp hz₁
      obtain ⟨w₂, hw₂, rfl⟩ := isClosed_induced_iff.mp hz₂
      have hirr' : IsPreirreducible (closure ({η'} : Set X)) := isPreirreducible_singleton.closure
      have hcov' : closure ({η'} : Set X) ⊆ w₁ ∪ w₂ := fun p hp =>
        hcov (show (⟨p, hcl'C hp⟩ : C) ∈ Subtype.val ⁻¹' closure ({η'} : Set X) from hp)
      rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr') w₁ w₂ hw₁ hw₂ hcov' with
        h | h
      · exact Or.inl fun p hp => h hp
      · exact Or.inr fun p hp => h hp
    have htt' : t ⊆ Subtype.val ⁻¹' closure ({η'} : Set X) := fun p hp =>
      hcl (subset_closure ⟨p, hp, rfl⟩)
    have heq := hmax _ ht' htt'
    have hη't : (⟨η', hη'C⟩ : C) ∈ t := by
      rw [← heq]
      exact subset_closure rfl
    have hsp' : hirr.genericPoint ⤳ η' := by
      rw [specializes_iff_mem_closure, hgen.def]
      exact subset_closure ⟨_, hη't, rfl⟩
    exact (hsp.antisymm hsp').eq

/-- The generic point of the component through y of the stratum of the members of positive weight:
a point on all the members of positive weight which specializes to y and has no proper
generization on all of them. -/
theorem exists_stratum_generic_point {X : Scheme} {r : ℕ} (ξ : Fin r → X) (w : Fin r → ℝ)
    (y : X) (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η := by
  have hC : IsClosed {p : X | ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} := by
    have h : {p : X | ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} =
        ⋂ k, ⋂ (_ : w k ≠ 0), closure ({ξ k} : Set X) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [h]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_closure
  obtain ⟨η, hη, hηy, hmax⟩ := exists_maximal_generization_of_mem_isClosed hC
    (show y ∈ {p : X | ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} from hwy)
  exact ⟨η, hη, hηy, fun η' hη' hsp => hmax η' hη' hsp⟩

end Topology

section Chart

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- A coordinate of an étale chart outside S lies in no minimal prime of the ideal of the
coordinate stratum of S: the stratum is flat over the polynomial ring in the remaining variables,
so the coordinate is a nonzerodivisor on it. -/
theorem etaleChart_coordinate_notMem_stratum_minimalPrime (c : EtaleChart K X n)
    (S : Set (Fin n)) {𝔮 : Ideal Γ(X, c.U)}
    (h𝔮 : 𝔮 ∈ (etaleChartStratumIdeal c S).minimalPrimes) {b : Fin n} (hb : b ∉ S) :
    c.coords (MvPolynomial.X b) ∉ 𝔮 := by
  classical
  let P := MvPolynomial (Fin n) K
  let B := Γ(X, c.U)
  let _ : Algebra P B := c.coords.toRingHom.toAlgebra
  have : IsScalarTower K P B := IsScalarTower.of_algebraMap_eq fun k => (c.coords.commutes k).symm
  have hetale : Algebra.Etale P B := etaleChart_coords_etale c
  have hsmooth : Algebra.Smooth P B := ⟨inferInstance, inferInstance⟩
  let J : Ideal P := Ideal.span (MvPolynomial.X (R := K) '' S)
  have hI : etaleChartStratumIdeal c S = J.map (algebraMap P B) := rfl
  have hdom : IsDomain (P ⧸ J) :=
    MulEquiv.isDomain (MvPolynomial {j // j ∉ S} K) (polynomialKillEquiv (K := K) S).toMulEquiv
  -- the variable X_b is not in J
  have hXb : Ideal.Quotient.mk J (MvPolynomial.X b) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro hmem
    have hle : J ≤ RingHom.ker (MvPolynomial.aeval (R := K)
        (fun i : Fin n => if i = b then (1 : K) else 0)).toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      change MvPolynomial.aeval (R := K) (fun i : Fin n => if i = b then (1 : K) else 0)
        (MvPolynomial.X i) = 0
      rw [MvPolynomial.aeval_X, ite_eq_right (fun h : i = b => hb (h ▸ hi))]
    have h1 := hle hmem
    rw [RingHom.mem_ker] at h1
    change MvPolynomial.aeval (R := K) (fun i : Fin n => if i = b then (1 : K) else 0)
      (MvPolynomial.X b) = 0 at h1
    rw [MvPolynomial.aeval_X, ite_eq_left rfl] at h1
    exact one_ne_zero h1
  have hreg : IsSMulRegular (P ⧸ J) (Ideal.Quotient.mk J (MvPolynomial.X b)) :=
    IsLeftRegular.isSMulRegular (mul_right_injective₀ hXb)
  -- the stratum is flat over P ⧸ J
  have hflat : Module.Flat (P ⧸ J) (B ⧸ J.map (algebraMap P B)) :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B J).toLinearEquiv
  have hreg' := IsSMulRegular.of_flat (S := B ⧸ J.map (algebraMap P B)) hreg
  have hnzd : Ideal.Quotient.mk (J.map (algebraMap P B)) (c.coords (MvPolynomial.X b)) ∈
      nonZeroDivisors (B ⧸ J.map (algebraMap P B)) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    apply hreg'
    change algebraMap (P ⧸ J) (B ⧸ J.map (algebraMap P B))
        (Ideal.Quotient.mk J (MvPolynomial.X b)) * x =
      algebraMap (P ⧸ J) (B ⧸ J.map (algebraMap P B))
        (Ideal.Quotient.mk J (MvPolynomial.X b)) * 0
    rw [mul_zero, mul_comm]
    exact hx
  rw [hI, Ideal.minimalPrimes_eq_comap] at h𝔮
  obtain ⟨𝔮', h𝔮', rfl⟩ := h𝔮
  intro hmem
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔮') hmem hnzd

/-- On a simple normal crossing chart, a point of the stratum of the members of positive weight
which has no proper generization in the stratum lies on no member of weight zero. -/
theorem stratum_maximal_point_notMem_closure {r : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X)
    (hη : η ∈ c.U) (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (k' : Fin r) (hk' : w k' = 0) : η ∉ closure ({ξ k'} : Set X) := by
  classical
  intro hηk'
  -- a section lies in the prime of a point of the chart iff its germ is not a unit
  have hdict : ∀ (p : X) (hp : p ∈ c.U) (f : Γ(X, c.U)),
      f ∈ (c.isAffine.primeIdealOf ⟨p, hp⟩).asIdeal ↔ ¬ IsUnit (X.presheaf.germ c.U p hp f) := by
    intro p hp f
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p, hp⟩ : c.U)
    have hloc := c.isAffine.isLocalization_stalk (⟨p, hp⟩ : c.U)
    rw [← not_iff_not, not_not]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk p)
      (c.isAffine.primeIdealOf ⟨p, hp⟩).asIdeal f).symm
  have hmem : ∀ (p : X) (hp : p ∈ c.U) (k : Fin r) (a : Fin n), σc k = some a →
      (p ∈ closure ({ξ k} : Set X) ↔
        c.coords (MvPolynomial.X a) ∈ (c.isAffine.primeIdealOf ⟨p, hp⟩).asIdeal) := by
    intro p hp k a hka
    rw [hdict p hp]
    constructor
    · intro hpk hu
      have h1 : p ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hpk, hp⟩
      rw [hc.2 k, hka, Option.elim_some, Scheme.zeroLocus_singleton] at h1
      exact h1.1 ((X.mem_basicOpen _ p hp).mpr hu)
    · intro hnu
      have h1 : p ∈ closure ({ξ k} : Set X) ∩ c.U := by
        rw [hc.2 k, hka, Option.elim_some, Scheme.zeroLocus_singleton]
        exact ⟨fun hb => hnu ((X.mem_basicOpen _ p hp).mp hb), hp⟩
      exact h1.1
  have hsome : ∀ k, η ∈ closure ({ξ k} : Set X) → ∃ a, σc k = some a := by
    intro k hηk
    cases hσ : σc k with
    | none =>
      exfalso
      have h1 : η ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hηk, hη⟩
      rw [hc.2 k, hσ] at h1
      exact h1
    | some a => exact ⟨a, rfl⟩
  -- the stratum ideal of the coordinates of the members of positive weight
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin n), S = {a | ∃ k, w k ≠ 0 ∧ σc k = some a} := ⟨_, rfl⟩
  have hIle : etaleChartStratumIdeal c S ≤ (c.isAffine.primeIdealOf ⟨η, hη⟩).asIdeal := by
    rw [etaleChartStratumIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    rw [hS] at ha
    obtain ⟨k, hk, hka⟩ := ha
    exact (hmem η hη k a hka).mp (hwη k hk)
  obtain ⟨𝔮₀, h𝔮₀, hle⟩ := Ideal.exists_minimalPrimes_le hIle
  have h𝔮₀prime : 𝔮₀.IsPrime := h𝔮₀.1.1
  -- the point of the chart with prime 𝔮₀
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : X, η₀ = c.isAffine.fromSpec (⟨𝔮₀, h𝔮₀prime⟩ : PrimeSpectrum Γ(X, c.U)) :=
    ⟨_, rfl⟩
  have hη₀U : η₀ ∈ c.U := by
    rw [← SetLike.mem_coe, ← c.isAffine.range_fromSpec, hη₀]
    exact ⟨_, rfl⟩
  have hprime₀ : c.isAffine.primeIdealOf ⟨η₀, hη₀U⟩ =
      (⟨𝔮₀, h𝔮₀prime⟩ : PrimeSpectrum Γ(X, c.U)) := by
    apply c.isAffine.fromSpec.isOpenEmbedding.injective
    rw [c.isAffine.fromSpec_primeIdealOf]
    exact hη₀
  have hspec : η₀ ⤳ η := by
    have h1 : (⟨𝔮₀, h𝔮₀prime⟩ : PrimeSpectrum Γ(X, c.U)) ⤳ c.isAffine.primeIdealOf ⟨η, hη⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map c.isAffine.fromSpec.continuous
    rw [c.isAffine.fromSpec_primeIdealOf] at h2
    rw [hη₀]
    exact h2
  have hη₀mem : ∀ k, w k ≠ 0 → η₀ ∈ closure ({ξ k} : Set X) := by
    intro k hk
    obtain ⟨a, hka⟩ := hsome k (hwη k hk)
    rw [hmem η₀ hη₀U k a hka, hprime₀]
    refine h𝔮₀.1.2 ?_
    rw [etaleChartStratumIdeal_eq_span]
    refine Ideal.subset_span ⟨a, ?_, rfl⟩
    rw [hS]
    exact ⟨k, hk, hka⟩
  -- maximality: the prime of η is minimal over the stratum ideal
  have heq : η₀ = η := hmax η₀ hη₀mem hspec
  obtain ⟨b, hb⟩ := hsome k' hηk'
  have hbS : b ∉ S := by
    rw [hS]
    rintro ⟨k, hk, hkb⟩
    have hkk : k = k' := hc.1 k k' b hkb hb
    exact hk (hkk ▸ hk')
  have hxb : c.coords (MvPolynomial.X b) ∈ 𝔮₀ := by
    have h1 := (hmem η₀ hη₀U k' b hb).mp (heq ▸ hηk')
    rw [hprime₀] at h1
    exact h1
  exact etaleChart_coordinate_notMem_stratum_minimalPrime c S h𝔮₀ hbS hxb

variable (K n) in
/-- The generic point of the component through y of the stratum of the members of positive weight
of a simple normal crossing family: it lies on all the members of positive weight, specializes to
y, has no proper generization in the stratum and lies on no member of weight zero. -/
theorem exists_stratum_generic_point_avoiding {r : ℕ} (ξ : Fin r → X)
    (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      (∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η) ∧
      ∀ k, w k = 0 → η ∉ closure ({ξ k} : Set X) := by
  obtain ⟨η, hη, hηy, hmax⟩ := exists_stratum_generic_point ξ w y hwy
  obtain ⟨c, σc, hηc, hc⟩ := hsnc η
  exact ⟨η, hη, hηy, hmax, fun k hk =>
    stratum_maximal_point_notMem_closure ξ c σc hc w η hηc hη hmax k hk⟩

end Chart

section Centre

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- A general closed point of the centre of a weight on a simple normal crossing family. There is
a point η on all the members of positive weight, specializing to the given point y, such that
every open set containing η contains a closed point z of the closure of η with a simple normal
crossing chart all of whose coordinates vanish at z and whose selected coordinates cut out exactly
the members of positive weight. -/
theorem exists_closedPoint_centered_chart_of_weight {r : ℕ} (ξ : Fin r → X)
    (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      ∀ V : Set X, IsOpen V → η ∈ V →
        ∃ (z : X) (_ : IsClosed ({z} : Set X)) (_ : η ⤳ z) (_ : z ∈ V) (c : EtaleChart K X n)
          (σc : Fin r → Option (Fin n)) (hz : z ∈ c.U), IsSNCChart c ξ σc ∧
          (∀ a, ¬ IsUnit (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a)))) ∧
          ∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0 := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨η, hη, hηy, -, havoid⟩ := exists_stratum_generic_point_avoiding K n ξ hsnc w y hwy
  refine ⟨η, hη, hηy, fun V hV hηV => ?_⟩
  -- the union of the members of weight zero is closed and does not contain η
  have hCclosed : IsClosed (⋃ k ∈ (Finset.univ.filter fun k => w k = 0),
      closure ({ξ k} : Set X)) :=
    isClosed_biUnion_finset fun k _ => isClosed_closure
  have hηC : η ∉ ⋃ k ∈ (Finset.univ.filter fun k => w k = 0), closure ({ξ k} : Set X) := by
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    intro k hk hηk
    exact havoid k hk hηk
  obtain ⟨z, ⟨hzη, hzV, hzC⟩, hzcl⟩ := nonempty_inter_closedPoints
    (Z := closure ({η} : Set X) ∩ (V ∩ (⋃ k ∈ (Finset.univ.filter fun k => w k = 0),
      closure ({ξ k} : Set X))ᶜ))
    ⟨η, subset_closure rfl, hηV, hηC⟩
    (isClosed_closure.isLocallyClosed.inter (hV.inter hCclosed.isOpen_compl).isLocallyClosed)
  have hzcl' : IsClosed ({z} : Set X) := mem_closedPoints_iff.mp hzcl
  have hspz : η ⤳ z := specializes_iff_mem_closure.mpr hzη
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) z hzcl'
  obtain ⟨c, σc, hz, hc, hnu, hsomez, hzsome⟩ := exists_centered_snc_chart ξ hsnc z β
  refine ⟨z, hzcl', hspz, hzV, c, σc, hz, hc, hnu, fun k => ⟨?_, fun hk => ?_⟩⟩
  · rintro ⟨a, hka⟩ hk0
    apply hzC
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk0, hsomez k a hka⟩
  · exact hzsome k (closure_minimal (Set.singleton_subset_iff.mpr (hη k hk)) isClosed_closure hzη)

end Centre

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCStrataGenericPoints
public import MixedFujita.StratumTangentSaturation
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Derivative

/-!
The restriction to the stratum of a weight in Taylor coordinates (section 5.2 of the manuscript:
the terms without old positive weight do not depend on the fibre variables).

Let η be the generic point of a component of the stratum of the members of positive weight of a
simple normal crossing family, in a chart c, and z a point of the chart in the closure of η with
Taylor coordinates given by the chart. Let S be the set of the coordinates of the members of
positive weight.

* Setting the variables of S to zero is a ring endomorphism of the power series; its kernel
  consists of the series all of whose coefficients at exponents with zero S-part vanish.
* A germ at z whose Taylor expansion lies in this kernel lies in the ideal of the coordinates of
  S, and conversely; hence this ideal of the local ring at z is prime.
* A germ at z whose image in the local ring at η is not a unit lies in the ideal of the
  coordinates of S: the ideal is the prime of η, by the maximality of η.
* In characteristic zero, if the derivative of the image of a germ s in the local ring at η in the
  coordinate b lies in the maximal ideal of η, then the Taylor coefficients of s at exponents with
  zero S-part and nonzero b-part vanish.
* For a morphism π: if all the pullbacks of the germs at π(η) have this property for b, then the
  Taylor expansion at z of the pullback of every germ at π(z), reduced modulo the variables of S,
  does not contain the variable b.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

section PowerSeries

variable {σ : Type*} (K : Type*) [Field K]

/-- The scaling of the variables which kills the variables of S and keeps the others. -/
noncomputable def stratumScale (S : Set σ) : σ → K := fun i => if i ∈ S then 0 else 1

variable {K}

theorem stratumScale_of_mem {S : Set σ} {i : σ} (h : i ∈ S) : stratumScale K S i = 0 :=
  ite_eq_left h

theorem stratumScale_of_notMem {S : Set σ} {i : σ} (h : i ∉ S) : stratumScale K S i = 1 :=
  ite_eq_right h

/-- The coefficients of a series with the variables of S set to zero. -/
theorem coeff_rescale_stratumScale (S : Set σ) (f : MvPowerSeries σ K) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (MvPowerSeries.rescale (stratumScale K S) f) =
      if ∀ i ∈ S, e i = 0 then MvPowerSeries.coeff e f else 0 := by
  rw [MvPowerSeries.coeff_rescale]
  by_cases h : ∀ i ∈ S, e i = 0
  · rw [ite_eq_left h]
    have h1 : (e.prod fun s m => stratumScale K S s ^ m) = 1 := by
      refine Finset.prod_eq_one fun s hs => ?_
      have hsS : s ∉ S := fun hsS => (Finsupp.mem_support_iff.mp hs) (h s hsS)
      change stratumScale K S s ^ e s = 1
      rw [stratumScale_of_notMem hsS, one_pow]
    rw [h1, one_mul]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hiS, hi⟩ := h
    have h0 : (e.prod fun s m => stratumScale K S s ^ m) = 0 := by
      refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi) ?_
      change stratumScale K S i ^ e i = 0
      rw [stratumScale_of_mem hiS]
      exact zero_pow hi
    rw [h0, zero_mul]

/-- The kernel of setting the variables of S to zero. -/
theorem rescale_stratumScale_eq_zero_iff (S : Set σ) (f : MvPowerSeries σ K) :
    MvPowerSeries.rescale (stratumScale K S) f = 0 ↔
      ∀ e : σ →₀ ℕ, (∀ i ∈ S, e i = 0) → MvPowerSeries.coeff e f = 0 := by
  constructor
  · intro h e he
    have h1 := congrArg (MvPowerSeries.coeff e) h
    rw [coeff_rescale_stratumScale, ite_eq_left he, map_zero] at h1
    exact h1
  · intro h
    ext e
    rw [coeff_rescale_stratumScale, map_zero]
    by_cases he : ∀ i ∈ S, e i = 0
    · rw [ite_eq_left he]
      exact h e he
    · rw [ite_eq_right he]

/-- The variables of S are killed. -/
theorem rescale_stratumScale_X {S : Set σ} {i : σ} (hi : i ∈ S) :
    MvPowerSeries.rescale (stratumScale K S) (MvPowerSeries.X i : MvPowerSeries σ K) = 0 := by
  rw [rescale_stratumScale_eq_zero_iff]
  intro e he
  rw [MvPowerSeries.coeff_X, ite_eq_right]
  intro h
  have h1 := he i hi
  rw [h, Finsupp.single_eq_same] at h1
  exact one_ne_zero h1

end PowerSeries

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Specialization

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

/-- The map of local rings of a specialization, as a K-algebra map. -/
noncomputable def stalkSpecializesAlgHom {x y : X} (h : x ⤳ y) :
    X.presheaf.stalk y →ₐ[K] X.presheaf.stalk x where
  toRingHom := (X.presheaf.stalkSpecializes h).hom
  commutes' k := by
    change X.presheaf.stalkSpecializes h (X.presheaf.germ ⊤ y (Opens.mem_top y)
        (Scheme.Modules.baseRingToGlobalSections K X k)) =
      X.presheaf.germ ⊤ x (Opens.mem_top x) (Scheme.Modules.baseRingToGlobalSections K X k)
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _

theorem stalkSpecializesAlgHom_apply {x y : X} (h : x ⤳ y) (a : X.presheaf.stalk y) :
    stalkSpecializesAlgHom (K := K) h a = X.presheaf.stalkSpecializes h a :=
  rfl

/-- The stalk coordinates of a chart are compatible with specialization. -/
theorem stalkSpecializesAlgHom_comp_etaleChartStalkCoords (c : EtaleChart K X n) {x y : X}
    (h : x ⤳ y) (hx : x ∈ c.U) (hy : y ∈ c.U) :
    (stalkSpecializesAlgHom (K := K) h).comp (etaleChartStalkCoords c y hy) =
      etaleChartStalkCoords c x hx := by
  apply AlgHom.ext
  intro p
  change X.presheaf.stalkSpecializes h (X.presheaf.germ c.U y hy (c.coords p)) =
    X.presheaf.germ c.U x hx (c.coords p)
  exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _

/-- Coordinate derivations commute with specialization. -/
theorem stalkSpecializes_etaleCoordinateDerivation (c : EtaleChart K X n) {x y : X} (h : x ⤳ y)
    (hx : x ∈ c.U) (hy : y ∈ c.U) (b : Fin n) (s : X.presheaf.stalk y) :
    X.presheaf.stalkSpecializes h (etaleCoordinateDerivation (etaleChartStalkCoords c y hy)
        (etaleChartStalkCoords_formallyEtale c y hy) b s) =
      etaleCoordinateDerivation (etaleChartStalkCoords c x hx)
        (etaleChartStalkCoords_formallyEtale c x hx) b (X.presheaf.stalkSpecializes h s) := by
  have hcomp := stalkSpecializesAlgHom_comp_etaleChartStalkCoords c h hx hy
  have hfe : ((stalkSpecializesAlgHom (K := K) h).comp
      (etaleChartStalkCoords c y hy)).toRingHom.FormallyEtale := by
    rw [hcomp]
    exact etaleChartStalkCoords_formallyEtale c x hx
  have h1 := etaleCoordinateDerivation_comp (stalkSpecializesAlgHom (K := K) h)
    (etaleChartStalkCoords c y hy) (etaleChartStalkCoords_formallyEtale c y hy) hfe b s
  rw [etaleCoordinateDerivation_congr hcomp hfe (etaleChartStalkCoords_formallyEtale c x hx) b]
    at h1
  exact h1.symm

/-- A section of a chart lies in the prime of a point of the chart if and only if its germ is not
a unit. -/
theorem etaleChart_mem_primeIdealOf_iff (c : EtaleChart K X n) (p : X) (hp : p ∈ c.U)
    (f : Γ(X, c.U)) :
    f ∈ (c.isAffine.primeIdealOf ⟨p, hp⟩).asIdeal ↔ ¬ IsUnit (X.presheaf.germ c.U p hp f) := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p, hp⟩ : c.U)
  have hloc := c.isAffine.isLocalization_stalk (⟨p, hp⟩ : c.U)
  rw [← not_iff_not, not_not]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk p)
    (c.isAffine.primeIdealOf ⟨p, hp⟩).asIdeal f).symm

/-- On a simple normal crossing chart, a point of the chart lies on a member with a coordinate if
and only if the germ of the coordinate is not a unit. -/
theorem isSNCChart_mem_closure_iff {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σc : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σc) (p : X) (hp : p ∈ c.U) {k : Fin r}
    {a : Fin n} (hka : σc k = some a) :
    p ∈ closure ({ξ k} : Set X) ↔
      ¬ IsUnit (X.presheaf.germ c.U p hp (c.coords (MvPolynomial.X a))) := by
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

/-- On a simple normal crossing chart, a member through a point of the chart has a coordinate. -/
theorem isSNCChart_exists_some_of_mem_closure {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σc : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σc) (p : X) (hp : p ∈ c.U) {k : Fin r}
    (hpk : p ∈ closure ({ξ k} : Set X)) : ∃ a, σc k = some a := by
  cases hσ : σc k with
  | none =>
    exfalso
    have h1 : p ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hpk, hp⟩
    rw [hc.2 k, hσ] at h1
    exact h1
  | some a => exact ⟨a, rfl⟩

end Specialization

section Stalk

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]

/-- A germ whose Taylor expansion vanishes after setting the variables of S to zero lies in the
ideal of the coordinates of S. -/
theorem stalk_mem_span_coords_of_rescale_eq_zero (c : EtaleChart K X n) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (S : Set (Fin n)) (a : X.presheaf.stalk z)
    (ha : MvPowerSeries.rescale (stratumScale K S) (stalkTaylorExpansion z ez a) = 0) :
    a ∈ Ideal.span ((fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) '' S) := by
  obtain ⟨w, hw⟩ : ∃ w : Fin n → ℕ, ∀ i, w i = if i ∈ S then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hk : ((1 : ℕ) : ℕ∞) ≤ (stalkTaylorExpansion z ez a).weightedOrder w := by
    refine MvPowerSeries.nat_le_weightedOrder w fun e he => ?_
    refine (rescale_stratumScale_eq_zero_iff S _).mp ha e fun i hi => ?_
    have hwi : w i ≠ 0 := by
      rw [hw i, ite_eq_left hi]
      exact one_ne_zero
    have h1 := Finsupp.le_weight w hwi e
    omega
  have hmem := mem_monomialWeightIdeal_of_le_weightedOrder (stalkTaylorExpansion z ez)
    (fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) hez
    (fun r d h => (completionCoordinates_mem_maximalIdeal_pow_iff ez.toRingEquiv r d).mp h)
    w a 1 hk
  refine (Ideal.span_le.mpr ?_ :
    monomialWeightIdeal (fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) w 1 ≤ _) hmem
  rintro _ ⟨α, hα, rfl⟩
  obtain ⟨i, hiS, hi⟩ : ∃ i ∈ S, α i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hw0 : Finsupp.weight w α = 0 := by
      rw [Finsupp.weight_apply]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hiS : i ∉ S := fun hiS => (Finsupp.mem_support_iff.mp hi) (hcon i hiS)
      change α i • w i = 0
      rw [hw i, ite_eq_right hiS, smul_zero]
    omega
  exact Ideal.mem_of_dvd _
    ((dvd_pow_self _ hi).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    (Ideal.subset_span ⟨i, hiS, rfl⟩)

omit [IsLocallyNoetherian X] in
/-- The Taylor expansions of the germs of the ideal of the coordinates of S vanish after setting
the variables of S to zero. -/
theorem rescale_stalkTaylor_eq_zero_of_mem_span (c : EtaleChart K X n) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (S : Set (Fin n)) (a : X.presheaf.stalk z)
    (ha : a ∈ Ideal.span ((fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) '' S)) :
    MvPowerSeries.rescale (stratumScale K S) (stalkTaylorExpansion z ez a) = 0 := by
  have hle : Ideal.span ((fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) '' S) ≤
      RingHom.ker ((MvPowerSeries.rescale (stratumScale K S)).comp
        (stalkTaylorExpansion z ez).toRingHom) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change MvPowerSeries.rescale (stratumScale K S) (stalkTaylorExpansion z ez
      (etaleChartStalkCoords c z hz (MvPolynomial.X i))) = 0
    rw [hez i]
    exact rescale_stratumScale_X hi
  exact RingHom.mem_ker.mp (hle ha)

/-- The ideal of the coordinates of S in the local ring at a point with Taylor coordinates is
prime. -/
theorem stalk_span_coords_isPrime (c : EtaleChart K X n) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (S : Set (Fin n)) :
    (Ideal.span ((fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) '' S)).IsPrime := by
  have h : Ideal.span ((fun i => etaleChartStalkCoords c z hz (MvPolynomial.X i)) '' S) =
      RingHom.ker ((MvPowerSeries.rescale (stratumScale K S)).comp
        (stalkTaylorExpansion z ez).toRingHom) :=
    le_antisymm
      (fun a ha => RingHom.mem_ker.mpr (rescale_stalkTaylor_eq_zero_of_mem_span c z hz ez hez S a ha))
      (fun a ha => stalk_mem_span_coords_of_rescale_eq_zero c z hz ez hez S a
        (RingHom.mem_ker.mp ha))
  rw [h]
  exact RingHom.ker_isPrime _

/-- The prime of the generic point of the stratum in the local ring at a point of its closure. Let
η be a point of a simple normal crossing chart on all the members of positive weight, with no
proper generization on all of them, and z a point of the chart in the closure of η with Taylor
coordinates. A germ at z whose image in the local ring at η is not a unit lies in the ideal of the
coordinates of the members of positive weight. -/
theorem stalk_mem_span_coords_of_stalkSpecializes_mem {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (t : X.presheaf.stalk z)
    (ht : X.presheaf.stalkSpecializes hηz t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η)) :
    t ∈ Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) ''
      {a | ∃ k, w k ≠ 0 ∧ σc k = some a}) := by
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin n), S = {a | ∃ k, w k ≠ 0 ∧ σc k = some a} := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨𝔓, h𝔓⟩ : ∃ 𝔓 : Ideal (X.presheaf.stalk z), 𝔓 =
      Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) '' S) := ⟨_, rfl⟩
  rw [← h𝔓]
  have h𝔓prime : 𝔓.IsPrime := by
    rw [h𝔓]
    exact stalk_span_coords_isPrime c z hz ez hez S
  -- the coordinates of S are not units at η
  have hSη : ∀ a ∈ S, ¬ IsUnit (X.presheaf.germ c.U η hη (c.coords (MvPolynomial.X a))) := by
    intro a ha
    rw [hS] at ha
    obtain ⟨k, hk, hka⟩ := ha
    exact (isSNCChart_mem_closure_iff hc η hη hka).mp (hwη k hk)
  -- the image of 𝔓 in the local ring at η lies in the maximal ideal
  have h𝔓η : ∀ a ∈ 𝔓, X.presheaf.stalkSpecializes hηz a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
    have hle : 𝔓 ≤ (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
        (X.presheaf.stalkSpecializes hηz).hom := by
      rw [h𝔓, Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change X.presheaf.stalkSpecializes hηz
        (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a))) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk η)
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff]
      exact hSη a ha
    exact fun a ha => hle ha
  -- the contraction of 𝔓 to the chart
  obtain ⟨𝔮, h𝔮⟩ : ∃ 𝔮 : Ideal Γ(X, c.U), 𝔮 = 𝔓.comap (X.presheaf.germ c.U z hz).hom :=
    ⟨_, rfl⟩
  have h𝔮prime : 𝔮.IsPrime := by
    rw [h𝔮]
    exact Ideal.comap_isPrime _ 𝔓
  have h𝔮mem : ∀ f : Γ(X, c.U), f ∈ 𝔮 ↔ X.presheaf.germ c.U z hz f ∈ 𝔓 := by
    intro f
    rw [h𝔮]
    rfl
  have hle : 𝔮 ≤ (c.isAffine.primeIdealOf ⟨η, hη⟩).asIdeal := by
    intro f hf
    rw [etaleChart_mem_primeIdealOf_iff c η hη]
    have h1 := h𝔓η _ ((h𝔮mem f).mp hf)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h1
    exact h1
  -- the point of the chart with prime 𝔮
  obtain ⟨ζ, hζ⟩ : ∃ ζ : X, ζ = c.isAffine.fromSpec (⟨𝔮, h𝔮prime⟩ : PrimeSpectrum Γ(X, c.U)) :=
    ⟨_, rfl⟩
  have hζU : ζ ∈ c.U := by
    rw [← SetLike.mem_coe, ← c.isAffine.range_fromSpec, hζ]
    exact ⟨_, rfl⟩
  have hprimeζ : c.isAffine.primeIdealOf ⟨ζ, hζU⟩ =
      (⟨𝔮, h𝔮prime⟩ : PrimeSpectrum Γ(X, c.U)) := by
    apply c.isAffine.fromSpec.isOpenEmbedding.injective
    rw [c.isAffine.fromSpec_primeIdealOf]
    exact hζ
  have hspec : ζ ⤳ η := by
    have h1 : (⟨𝔮, h𝔮prime⟩ : PrimeSpectrum Γ(X, c.U)) ⤳ c.isAffine.primeIdealOf ⟨η, hη⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map c.isAffine.fromSpec.continuous
    rw [c.isAffine.fromSpec_primeIdealOf] at h2
    rw [hζ]
    exact h2
  have hζmem : ∀ k, w k ≠ 0 → ζ ∈ closure ({ξ k} : Set X) := by
    intro k hk
    obtain ⟨a, hka⟩ := isSNCChart_exists_some_of_mem_closure hc η hη (hwη k hk)
    rw [isSNCChart_mem_closure_iff hc ζ hζU hka, ← etaleChart_mem_primeIdealOf_iff c ζ hζU,
      hprimeζ]
    change c.coords (MvPolynomial.X a) ∈ 𝔮
    rw [h𝔮mem, h𝔓]
    refine Ideal.subset_span ⟨a, ?_, rfl⟩
    rw [hS]
    exact ⟨k, hk, hka⟩
  have heq : ζ = η := hmax ζ hζmem hspec
  have hprimeη : c.isAffine.primeIdealOf ⟨η, hη⟩ =
      (⟨𝔮, h𝔮prime⟩ : PrimeSpectrum Γ(X, c.U)) := by
    apply c.isAffine.fromSpec.isOpenEmbedding.injective
    rw [c.isAffine.fromSpec_primeIdealOf]
    exact heq.symm.trans hζ
  -- the germ as a fraction of sections of the chart
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨z, hz⟩ : c.U)
  have hloc := c.isAffine.isLocalization_stalk (⟨z, hz⟩ : c.U)
  obtain ⟨⟨f, u⟩, hfu⟩ := IsLocalization.surj (c.isAffine.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl t
  have hfu' : t * X.presheaf.germ c.U z hz (u : Γ(X, c.U)) = X.presheaf.germ c.U z hz f := hfu
  have hu : IsUnit (X.presheaf.germ c.U z hz (u : Γ(X, c.U))) :=
    not_not.mp ((etaleChart_mem_primeIdealOf_iff c z hz (u : Γ(X, c.U))).not.mp
      (Ideal.mem_primeCompl_iff.mp u.2))
  have hfη : f ∈ (c.isAffine.primeIdealOf ⟨η, hη⟩).asIdeal := by
    rw [etaleChart_mem_primeIdealOf_iff c η hη]
    intro hunit
    have h4 := congrArg (fun a => X.presheaf.stalkSpecializes hηz a) hfu'
    simp only [map_mul, TopCat.Presheaf.germ_stalkSpecializes_apply] at h4
    have h5 : X.presheaf.germ c.U η hη f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
      rw [← h4]
      exact Ideal.mul_mem_right _ _ ht
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h5
    exact h5 hunit
  rw [hprimeη] at hfη
  have hf𝔓 : X.presheaf.germ c.U z hz f ∈ 𝔓 := (h𝔮mem f).mp hfη
  obtain ⟨v, hv⟩ := hu
  have ht' : t = X.presheaf.germ c.U z hz f * ((v⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) := by
    rw [← hfu', ← hv, mul_assoc, Units.mul_inv, mul_one]
  rw [ht']
  exact Ideal.mul_mem_right _ _ hf𝔓

/-- The restriction to the stratum does not contain a coordinate whose derivative vanishes on the
stratum. In characteristic zero, in the situation of the previous statement, let s be a germ at z
such that the derivative in the coordinate b of its image in the local ring at η lies in the
maximal ideal. Then the Taylor coefficients of s at the exponents with zero part in the
coordinates of the members of positive weight and nonzero b-part vanish. -/
theorem stalkTaylor_coeff_eq_zero_of_derivative_mem [CharZero K] {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (b : Fin n) (s : X.presheaf.stalk z)
    (hs : etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b (X.presheaf.stalkSpecializes hηz s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk η))
    (e : Fin n →₀ ℕ) (he : ∀ a, (∃ k, w k ≠ 0 ∧ σc k = some a) → e a = 0) (heb : e b ≠ 0) :
    MvPowerSeries.coeff e (stalkTaylorExpansion z ez s) = 0 := by
  -- the derivative of s lies in the ideal of the coordinates of S
  have hmem := stalk_mem_span_coords_of_stalkSpecializes_mem ξ c σc hc w η hη hwη hmax z hz hηz
    ez hez (etaleCoordinateDerivation (etaleChartStalkCoords c z hz)
      (etaleChartStalkCoords_formallyEtale c z hz) b s)
    (by
      rw [stalkSpecializes_etaleCoordinateDerivation c hηz hη hz b s]
      exact hs)
  have hres := rescale_stalkTaylor_eq_zero_of_mem_span c z hz ez hez _ _ hmem
  rw [etaleCoordinateDerivation_taylor (stalkTaylorExpansion z ez) (etaleChartStalkCoords c z hz)
    (etaleChartStalkCoords_formallyEtale c z hz) hez b s] at hres
  -- the exponent e - e_b
  have hle : Finsupp.single b 1 ≤ e :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr heb)
  have he' : e - Finsupp.single b 1 + Finsupp.single b 1 = e := tsub_add_cancel_of_le hle
  have h0 := (rescale_stratumScale_eq_zero_iff _ _).mp hres (e - Finsupp.single b 1)
    (fun a ha => by
      rw [Finsupp.tsub_apply, he a ha, Nat.zero_sub])
  rw [MvPowerSeries.coeff_pderiv, he'] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact h1
  · exact absurd h1 (Nat.cast_add_one_ne_zero _)

end Stalk

section Pullback

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y)

/-- The pullbacks of the germs of the base, restricted to the stratum, do not contain the fibre
coordinates. Let b be a coordinate such that the derivative in b of the pullback of every germ at
π(η) lies in the maximal ideal of η. Then for every germ h at π(z) the Taylor coefficients of the
pullback of h at the exponents with zero part in the coordinates of the members of positive weight
and nonzero b-part vanish. -/
theorem stalkMap_taylor_coeff_eq_zero_of_saturated {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (b : Fin n)
    (hsat : ∀ h' : Y.presheaf.stalk (π η), etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk η))
    (h : Y.presheaf.stalk (π z))
    (e : Fin n →₀ ℕ) (he : ∀ a, (∃ k, w k ≠ 0 ∧ σc k = some a) → e a = 0) (heb : e b ≠ 0) :
    MvPowerSeries.coeff e (stalkTaylorExpansion z ez (π.stalkMap z h)) = 0 := by
  refine stalkTaylor_coeff_eq_zero_of_derivative_mem ξ c σc hc w η hη hwη hmax z hz hηz ez hez b
    (π.stalkMap z h) ?_ e he heb
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply π η z hηz h]
  exact hsat _

end Pullback

end MixedFujita

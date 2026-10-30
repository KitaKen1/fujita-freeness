/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StratumTangentCoordinates

/-!
The central slice of the pullbacks at a general closed point of the centre of a weight
(section 5.2 of the manuscript: the central slice is the restriction to the image W of the centre).

Let η be the generic point of a component of the stratum of the members of positive weight, z a
point of the chart in the closure of η with Taylor coordinates given by the chart, and π a morphism
to Y. The central slice of a germ h at π(z) consists of the Taylor coefficients of the pullback of
h at the exponents with zero part in the coordinates of the members of positive weight.

* The central slice of h vanishes if and only if h vanishes at π(η), that is, the image of h in
  the local ring at π(η) is not a unit. (This is the germ-level statement; the count of the
  dimension of the central slices of the sections of a divisor is not in this file.)
* A point x' specializing to x such that every germ at x vanishing at x vanishes at x' is x.
* If the central slices of all the germs at π(z) are constant, then π(η) = π(z). In characteristic
  zero this is the case when the pullbacks of all the germs at π(η) have all their derivatives in
  the coordinates outside the family in the maximal ideal of η. Hence, if π(η) is not π(z), there
  is at least one tangent coordinate.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Points

variable {Y : Scheme.{u}}

/-- A section of an affine open lies in the prime of a point of the open if and only if its germ
is not a unit. -/
theorem isAffineOpen_mem_primeIdealOf_iff {U : Y.Opens} (hU : IsAffineOpen U) (p : Y)
    (hp : p ∈ U) (f : Γ(Y, U)) :
    f ∈ (hU.primeIdealOf ⟨p, hp⟩).asIdeal ↔ ¬ IsUnit (Y.presheaf.germ U p hp f) := by
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨p, hp⟩ : U)
  have hloc := hU.isLocalization_stalk (⟨p, hp⟩ : U)
  rw [← not_iff_not, not_not]
  exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk p)
    (hU.primeIdealOf ⟨p, hp⟩).asIdeal f).symm

/-- A point x' specializing to x such that the germs at x vanishing at x vanish at x' is x. -/
theorem eq_of_specializes_of_maximalIdeal_le {x x' : Y} (h : x' ⤳ x)
    (hloc : ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
      Y.presheaf.stalkSpecializes h a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x')) :
    x' = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (⊤ : Y.Opens) from Opens.mem_top x) isOpen_univ
  have hx'U : x' ∈ U := h.mem_open U.isOpen hxU
  have hle : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ≤ (hU.primeIdealOf ⟨x', hx'U⟩).asIdeal := by
    intro f hf
    rw [isAffineOpen_mem_primeIdealOf_iff hU x hxU] at hf
    rw [isAffineOpen_mem_primeIdealOf_iff hU x' hx'U]
    have h1 := hloc (Y.presheaf.germ U x hxU f)
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hf))
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] at h1
    exact h1
  have h1 : hU.primeIdealOf ⟨x, hxU⟩ ⤳ hU.primeIdealOf ⟨x', hx'U⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := h1.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2
  exact (h.antisymm h2).eq

end Points

section Slice

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y)

omit [IsLocallyNoetherian X] in
/-- The germs of the ideal of coordinates that are not units at η vanish at η. -/
theorem stalkSpecializes_mem_maximalIdeal_of_mem_span_coords (c : EtaleChart K X n)
    (S : Set (Fin n)) (η : X) (hη : η ∈ c.U) (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (hS : ∀ a ∈ S, ¬ IsUnit (X.presheaf.germ c.U η hη (c.coords (MvPolynomial.X a))))
    (t : X.presheaf.stalk z)
    (ht : t ∈ Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) '' S)) :
    X.presheaf.stalkSpecializes hηz t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  have hle : Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) '' S) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk η)).comap
        (X.presheaf.stalkSpecializes hηz).hom := by
    rw [Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    change X.presheaf.stalkSpecializes hηz
      (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a))) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk η)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    exact hS a ha
  exact hle ht

/-- The central slice of a germ h at π(z) vanishes if and only if h vanishes at π(η). -/
theorem central_slice_eq_zero_iff {r : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X)
    (hη : η ∈ c.U) (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (h : Y.presheaf.stalk (π z)) :
    (∀ e : Fin n →₀ ℕ, (∀ a, (∃ k, w k ≠ 0 ∧ σc k = some a) → e a = 0) →
        MvPowerSeries.coeff e (stalkTaylorExpansion z ez (π.stalkMap z h)) = 0) ↔
      Y.presheaf.stalkSpecializes (π.base.hom.map_specializes hηz) h ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (π η)) := by
  have hSη : ∀ a ∈ {a | ∃ k, w k ≠ 0 ∧ σc k = some a},
      ¬ IsUnit (X.presheaf.germ c.U η hη (c.coords (MvPolynomial.X a))) := by
    rintro a ⟨k, hk, hka⟩
    exact (isSNCChart_mem_closure_iff hc η hη hka).mp (hwη k hk)
  constructor
  · intro h0
    have hres : MvPowerSeries.rescale (stratumScale K {a | ∃ k, w k ≠ 0 ∧ σc k = some a})
        (stalkTaylorExpansion z ez (π.stalkMap z h)) = 0 :=
      (rescale_stratumScale_eq_zero_iff _ _).mpr h0
    have hmem := stalk_mem_span_coords_of_rescale_eq_zero c z hz ez hez _ _ hres
    have h1 := stalkSpecializes_mem_maximalIdeal_of_mem_span_coords c _ η hη z hz hηz hSη _ hmem
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply π η z hηz h] at h1
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    exact h1 (hu.map (π.stalkMap η).hom)
  · intro hvan e he
    have h1 : X.presheaf.stalkSpecializes hηz (π.stalkMap z h) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply π η z hηz h]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hu =>
        (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hvan))
          ((isUnit_map_iff (π.stalkMap η).hom _).mp hu))
    have hmem := stalk_mem_span_coords_of_stalkSpecializes_mem ξ c σc hc w η hη hwη hmax z hz hηz
      ez hez _ h1
    exact (rescale_stratumScale_eq_zero_iff _ _).mp
      (rescale_stalkTaylor_eq_zero_of_mem_span c z hz ez hez _ _ hmem) e he

/-- If the central slices of all the germs at π(z) are constant, then π(η) = π(z). -/
theorem map_eq_of_central_slice_const {r : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X)
    (hη : η ∈ c.U) (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (hconst : ∀ (h : Y.presheaf.stalk (π z)) (e : Fin n →₀ ℕ),
      (∀ a, (∃ k, w k ≠ 0 ∧ σc k = some a) → e a = 0) → e ≠ 0 →
        MvPowerSeries.coeff e (stalkTaylorExpansion z ez (π.stalkMap z h)) = 0) :
    π η = π z := by
  refine eq_of_specializes_of_maximalIdeal_le (π.base.hom.map_specializes hηz) fun h hh => ?_
  refine (central_slice_eq_zero_iff π ξ c σc hc w η hη hwη hmax z hz hηz ez hez h).mp
    fun e he => ?_
  by_cases he0 : e = 0
  · -- the constant term of the pullback of a germ vanishing at π(z)
    have hm : π.stalkMap z h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hh))
        ((isUnit_map_iff (π.stalkMap z).hom _).mp hu)
    have hord := (completionCoordinates_mem_maximalIdeal_pow_iff ez.toRingEquiv
      (π.stalkMap z h) 1).mpr (by rwa [pow_one])
    rw [he0]
    refine MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le ?_ hord)
    rw [map_zero]
    exact_mod_cast Nat.zero_lt_one
  · exact hconst h e he he0

end Slice

section Tangent

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y)

/-- Without tangent coordinates the image of the centre is a point. If the selected coordinates of
the chart are exactly those of the members of positive weight and, for every germ h at π(η), all
the derivatives of the pullback of h in the coordinates outside the family lie in the maximal ideal
of η, then π(η) = π(z). Hence, if π(η) is not π(z), a chart as in
`exists_closedPoint_tangent_chart_of_weight` has at least one tangent coordinate. -/
theorem map_eq_of_forall_derivative_mem {r : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X)
    (hη : η ∈ c.U) (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (hiff : ∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0)
    (hsat : ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) →
      etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk η)) :
    π η = π z := by
  refine map_eq_of_central_slice_const π ξ c σc hc w η hη hwη hmax z hz hηz ez hez
    fun h e he he0 => ?_
  obtain ⟨b, hb⟩ : ∃ b, e b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact he0 (Finsupp.ext hcon)
  have hbfree : ∀ k, σc k ≠ some b := fun k hkb => hb (he b ⟨k, (hiff k).mp ⟨b, hkb⟩, hkb⟩)
  exact stalkMap_taylor_coeff_eq_zero_of_saturated π ξ c σc hc w η hη hwη hmax z hz hηz ez hez b
    (fun h' => hsat h' b hbfree) h e he hb

end Tangent

end MixedFujita

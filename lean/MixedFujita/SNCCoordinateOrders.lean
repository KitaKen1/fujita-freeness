/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierLocalUnits
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
Coordinate hypersurfaces of an étale chart are reduced. At a DVR stalk their nonunit germs
are uniformizers. The set-theoretic SNC chart condition therefore identifies the order of
each actual coordinate with the indicator of its prescribed codimension-one generic point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A regular ring is reduced, using the domain localizations already supplied by Tau Ceti. -/
theorem regularRing_isReduced {R : Type u} [CommRing R] [IsRegularRing R] : IsReduced R := by
  apply isReduced_ofLocalizationMaximal R
  intro P hP
  have := hP.isPrime
  have : IsRegularLocalRing (Localization.AtPrime P) := (isRegularRing_iff.mp inferInstance) P
  infer_instance

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- An actual étale coordinate on an integral chart is nonzero. -/
theorem etaleChart_coordinate_ne_zero (c : EtaleChart K X n) (a : Fin n) :
    c.coords (MvPolynomial.X a) ≠ 0 := by
  intro h
  have hd := etaleCoordinateDerivation_coordinate c.coords c.formallyEtale a a
  rw [h, map_zero] at hd
  simpa using hd

/-- The coordinate equation as an actual nonzero rational unit. -/
noncomputable def etaleChartCoordinateRationalUnit (c : EtaleChart K X n) (a : Fin n) :
    X.functionFieldˣ :=
  regularEquationRationalUnit X c.U (c.coords (MvPolynomial.X a))
    (etaleChart_coordinate_ne_zero c a)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- A coordinate ideal is radical because the coordinate stratum is smooth and reduced. -/
theorem etaleChart_coordinate_span_isRadical (c : EtaleChart K X n) (a : Fin n) :
    (Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U))).IsRadical := by
  have heq : etaleChartStratumIdeal c ({a} : Set (Fin n)) =
      Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) := by
    rw [etaleChartStratumIdeal_eq_span, Set.image_singleton]
  have : Algebra.Smooth K
      (Γ(X, c.U) ⧸ Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U))) := by
    rw [← heq]
    exact etaleChart_stratum_smooth c {a}
  have := TauCeti.IsRegularRing.of_smooth (R := K)
    (S := Γ(X, c.U) ⧸ Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)))
  have := regularRing_isReduced
    (R := Γ(X, c.U) ⧸ Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)))
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr this

/-- Radicality of the coordinate equation survives passage to an actual stalk. -/
theorem etaleChart_coordinate_germ_span_isRadical (c : EtaleChart K X n) (a : Fin n)
    (x : X) (hx : x ∈ c.U) :
    (Ideal.span ({X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a))} :
      Set (X.presheaf.stalk x))).IsRadical := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := c.isAffine.isLocalization_stalk ⟨x, hx⟩
  have hrad := etaleChart_coordinate_span_isRadical c a
  have hmap : ((Ideal.span ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U))).map
      (algebraMap Γ(X, c.U) (X.presheaf.stalk x))).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    rw [← IsLocalization.map_radical (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      hrad.radical]
  rw [Ideal.map_span, Set.image_singleton] at hmap
  exact hmap

variable [IsLocallyNoetherian X]

/-- At a DVR point, a vanishing étale coordinate has order exactly one. -/
theorem etaleChart_coordinate_ord_one (c : EtaleChart K X n) (a : Fin n)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hu : ¬ IsUnit (X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X a)))) :
    X.ord (etaleChartCoordinateRationalUnit c a : X.functionField) (x : X) = 1 := by
  let g := X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X a))
  have hg : g ≠ 0 := fun h => etaleChart_coordinate_ne_zero c a
    (germ_injective_of_isIntegral X (x : X) hx (h.trans (map_zero _).symm))
  have hirr := dvr_irreducible_of_radical_span g hg hu
    (etaleChart_coordinate_germ_span_isRadical c a (x : X) hx)
  change X.ord (X.germToFunctionField c.U (c.coords (MvPolynomial.X a))) (x : X) = 1
  rw [← X.algebraMap_germ_eq_germToFunctionField hx]
  apply scheme_ord_regular_eq_localAdicOrder_nat x g hg 1
  rw [dvr_localAdicOrder_eq_addVal]
  exact IsDiscreteValuationRing.addVal_uniformizer hirr

/-- The SNC set identity gives the full prime-order indicator for its actual coordinate. -/
theorem isSNCChart_coordinate_ord (c : EtaleChart K X n) {r : ℕ}
    (ξ : Fin r → X) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (i : Fin r) (a : Fin n) (ha : σ i = some a)
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    X.ord (etaleChartCoordinateRationalUnit c a : X.functionField) (x : X) =
      if (x : X) = ξ i then 1 else 0 := by
  have hset := hc.2 i
  rw [ha, Option.elim_some] at hset
  have hzero : (x : X) ∉ X.basicOpen (c.coords (MvPolynomial.X a)) ↔ (x : X) = ξ i := by
    have h := Set.ext_iff.mp hset (x : X)
    rw [Scheme.zeroLocus_singleton] at h
    simpa only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, hx, and_true,
      scheme_codimensionOne_mem_closure_iff_eq (x : X) (ξ i) x.property (hξ i)] using h.symm
  by_cases heq : (x : X) = ξ i
  · rw [ite_eq_left heq]
    apply etaleChart_coordinate_ord_one c a x hx
    exact fun hu => (hzero.mpr heq) ((X.mem_basicOpen _ (x : X) hx).mpr hu)
  · rw [ite_eq_right heq]
    have hu : IsUnit (X.presheaf.germ c.U (x : X) hx (c.coords (MvPolynomial.X a))) :=
      (X.mem_basicOpen _ (x : X) hx).mp (by simpa only [not_not] using hzero.not.mpr heq)
    have h := scheme_ord_stalk_unit (x : X) hu.unit
    simpa only [IsUnit.unit_spec, X.algebraMap_germ_eq_germToFunctionField hx,
      etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val] using h

end MixedFujita

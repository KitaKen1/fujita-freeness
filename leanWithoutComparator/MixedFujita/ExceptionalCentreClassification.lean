/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SpecializationStalkEmbedding
public import MixedFujita.BirationalValuationFibre
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.IdealSheaf.Order.Basic

/-! A one-dimensional exceptional local quotient classifies the centres
of divisors meeting the marked exceptional prime. The actual stalk map
through the intersection either sends the normal equation to a unit or
preserves nonunits at the intersection. Separated birational uniqueness
excludes the exceptional generic centre for every other divisor. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Above a local ideal whose quotient has dimension at most one, a
prime is either the ideal itself or the ambient maximal ideal. -/
theorem prime_eq_or_maximal_of_quotient_dimensionLEOne
    {R : Type*} [CommRing R] [IsLocalRing R] (I q : Ideal R)
    [Ring.DimensionLEOne (R ⧸ I)] [q.IsPrime] (hIq : I ≤ q) :
    q = I ∨ q = IsLocalRing.maximalIdeal R := by
  let Q := q.map (Ideal.Quotient.mk I)
  let : Q.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIq
  by_cases hQ : Q = ⊥
  · left
    apply le_antisymm _ hIq
    have h := (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk I)).mp hQ
    simpa only [Ideal.mk_ker] using h
  · right
    let : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
    have hmax : (Q.comap (Ideal.Quotient.mk I)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    rw [Ideal.comap_map_mk hIq] at hmax
    exact IsLocalRing.eq_maximalIdeal hmax

/-- Evaluation in the base field kills every nonunit of a local algebra. -/
theorem local_algebra_evaluation_nonunit_eq_zero {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] [IsLocalRing R] (ε : R →ₐ[K] K)
    (u : R) (hu : ¬ IsUnit u) : ε u = 0 := by
  let : IsLocalHom ε.toRingHom := IsLocalHom.of_surjective _
    (fun a => ⟨algebraMap K R a, by simp⟩)
  by_contra h
  exact hu (IsLocalHom.map_nonunit (f := ε.toRingHom) u (Ne.isUnit h))

variable {X T : Scheme.{u}}

/-- A local equation for an ideal supported at a generization stays a
nonunit in the generization stalk. -/
theorem ideal_stalk_generator_nonunit_at_generization
    (I : X.IdealSheafData) {b p : X} (h : b ⤳ p) (hb : b ∈ I.support)
    (u : X.presheaf.stalk p) (hI : I.stalkIdeal p = Ideal.span {u}) :
    ¬ IsUnit (X.presheaf.stalkSpecializes h u) := by
  have hu : X.presheaf.stalkSpecializes h u ∈ I.stalkIdeal b := by
    rw [I.stalkIdeal_specializes h, hI]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)
  exact (IsLocalRing.mem_maximalIdeal _).mp
    ((I.mem_support_iff_stalkIdeal_le_maximalIdeal b).mp hb hu)

/-- The centre in a local spectrum of a generization maps to that
generization on the original scheme. -/
theorem fromSpecStalk_comap_specializes_closedPoint {b p : X} (h : b ⤳ p) :
    X.fromSpecStalk p
      (PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
        (IsLocalRing.closedPoint (X.presheaf.stalk b))) = b := by
  have hc := congrArg (fun f : Spec (X.presheaf.stalk b) ⟶ X =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk b)))
      (X.SpecMap_stalkSpecializes_fromSpecStalk h)
  exact hc.trans X.fromSpecStalk_closedPoint

variable {K : Type u} [Field K] [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower

/-- The actual intersection-stalk map has the correct scheme-theoretic centre. -/
theorem modelIntersectionStalkMap_centre (g : T ⟶ X) [g.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) :
    X.fromSpecStalk (g P)
      (PrimeSpectrum.comap (modelIntersectionStalkMap (K := K) g h).toRingHom
        (IsLocalRing.closedPoint (T.presheaf.stalk t))) = g t := by
  have hc : Spec.map (g.stalkMap P ≫ T.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk (g P) =
      T.fromSpecStalk t ≫ g := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hp := congrArg (fun f : Spec (T.presheaf.stalk t) ⟶ X =>
    f (IsLocalRing.closedPoint (T.presheaf.stalk t))) hc
  have hm : (modelIntersectionStalkMap (K := K) g h).toRingHom =
      (g.stalkMap P ≫ T.presheaf.stalkSpecializes h).hom := rfl
  rw [hm]
  simpa only [Scheme.Hom.comp_apply, Spec.map_apply, Scheme.fromSpecStalk_closedPoint] using hp

/-- For another point meeting the marked divisor, the exceptional local
quotient and birational uniqueness force the required normal/tangent
centre alternative. No locality of the map through the intersection is assumed. -/
theorem modelIntersection_normal_unit_or_tangent_nonunit
    (g : T ⟶ X) [IsDominant g] [IsSeparated g] [g.IsOver (Spec (.of K))]
    (hg : Function.Bijective (dominantFunctionFieldMap g).hom)
    {e t P : T} (he : e ⤳ P) (ht : t ⤳ P) (hte : t ≠ e)
    [ValuationRing (X.presheaf.stalk (g e))] (hep : g e ≠ g P)
    (u w : X.presheaf.stalk (g P))
    [Ring.DimensionLEOne (X.presheaf.stalk (g P) ⧸ Ideal.span {u})]
    (hu : ¬ IsUnit (X.presheaf.stalkSpecializes (he.map g.continuous) u))
    (hw : ¬ IsUnit w) :
    IsUnit (modelIntersectionStalkMap (K := K) g ht u) ∨
      ¬ IsUnit (modelIntersectionStalkMap (K := K) g ht w) := by
  let R := X.presheaf.stalk (g P)
  let I : Ideal R := Ideal.span {u}
  let qb : PrimeSpectrum R := PrimeSpectrum.comap
    (X.presheaf.stalkSpecializes (he.map g.continuous)).hom
      (IsLocalRing.closedPoint (X.presheaf.stalk (g e)))
  have hIb : I ≤ qb.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hu
  have hqb : qb.asIdeal = I := by
    rcases prime_eq_or_maximal_of_quotient_dimensionLEOne I qb.asIdeal hIb with h | h
    · exact h
    · have hpoint : qb = IsLocalRing.closedPoint R := PrimeSpectrum.ext h
      have hc := fromSpecStalk_comap_specializes_closedPoint (he.map g.continuous)
      rw [show PrimeSpectrum.comap
        (X.presheaf.stalkSpecializes (he.map g.continuous)).hom
          (IsLocalRing.closedPoint (X.presheaf.stalk (g e))) = qb from rfl,
        hpoint, Scheme.fromSpecStalk_closedPoint] at hc
      exact (hep hc.symm).elim
  by_cases hut : IsUnit (modelIntersectionStalkMap (K := K) g ht u)
  · exact Or.inl hut
  · right
    let q : PrimeSpectrum R := PrimeSpectrum.comap
      (modelIntersectionStalkMap (K := K) g ht).toRingHom
        (IsLocalRing.closedPoint (T.presheaf.stalk t))
    have hIq : I ≤ q.asIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hut
    have hq : q.asIdeal = IsLocalRing.maximalIdeal R := by
      rcases prime_eq_or_maximal_of_quotient_dimensionLEOne I q.asIdeal hIq with h | h
      · have hqq : q = qb := PrimeSpectrum.ext (h.trans hqb.symm)
        have hcentre : g t = g e := by
          calc
            g t = X.fromSpecStalk (g P) q :=
              (modelIntersectionStalkMap_centre (K := K) g ht).symm
            _ = X.fromSpecStalk (g P) qb := congrArg (X.fromSpecStalk (g P)) hqq
            _ = g e := fromSpecStalk_comap_specializes_closedPoint (he.map g.continuous)
        exact (hte (eq_of_birational_over_valuation_stalk g hg (g e) t e hcentre rfl)).elim
      · exact h
    have hwq : w ∈ q.asIdeal := by
      rw [hq]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hw
    exact (IsLocalRing.mem_maximalIdeal _).mp hwq

/-- A rational evaluation supplies the centred tangent nonunit internally. -/
theorem modelIntersection_centered_coordinate_alternative
    (g : T ⟶ X) [IsDominant g] [IsSeparated g] [g.IsOver (Spec (.of K))]
    (hg : Function.Bijective (dominantFunctionFieldMap g).hom)
    {e t P : T} (he : e ⤳ P) (ht : t ⤳ P) (hte : t ≠ e)
    [ValuationRing (X.presheaf.stalk (g e))] (hep : g e ≠ g P)
    (u v : X.presheaf.stalk (g P))
    [Ring.DimensionLEOne (X.presheaf.stalk (g P) ⧸ Ideal.span {u})]
    (hu : ¬ IsUnit (X.presheaf.stalkSpecializes (he.map g.continuous) u))
    (ε : X.presheaf.stalk (g P) →ₐ[K] K) :
    IsUnit (modelIntersectionStalkMap (K := K) g ht u) ∨
      ¬ IsUnit (modelIntersectionStalkMap (K := K) g ht
        (v - algebraMap K (X.presheaf.stalk (g P)) (ε v))) := by
  apply modelIntersection_normal_unit_or_tangent_nonunit g hg he ht hte hep u _ hu
  intro hw
  have hεw := hw.map ε.toRingHom
  change IsUnit (ε (v - algebraMap K (X.presheaf.stalk (g P)) (ε v))) at hεw
  have hz : ε (v - algebraMap K (X.presheaf.stalk (g P)) (ε v)) = 0 := by
    rw [map_sub, ε.commutes, Algebra.algebraMap_self_apply, sub_self]
  rw [hz] at hεw
  exact not_isUnit_zero hεw

/-- On a smooth surface, properness and the closed intersection supply
the distinct image points, smoothness supplies the marked valuation
stalk, and the actual ideal sheaf supplies its nonunit normal equation. -/
theorem smoothSurface_modelIntersection_centered_coordinate_alternative
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))]
    (g : T ⟶ X) [IsDominant g] [IsProper g] [g.IsOver (Spec (.of K))]
    (hg : Function.Bijective (dominantFunctionFieldMap g).hom)
    {e t P : T} (he : e ⤳ P) (ht : t ⤳ P) (hte : t ≠ e)
    (hecod : Order.coheight (g e) = 1) (hP : IsClosed ({P} : Set T))
    (I : X.IdealSheafData) (heI : g e ∈ I.support)
    (u v : X.presheaf.stalk (g P)) (hI : I.stalkIdeal (g P) = Ideal.span {u})
    [Ring.DimensionLEOne (X.presheaf.stalk (g P) ⧸ I.stalkIdeal (g P))]
    (ε : X.presheaf.stalk (g P) →ₐ[K] K) :
    IsUnit (modelIntersectionStalkMap (K := K) g ht u) ∨
      ¬ IsUnit (modelIntersectionStalkMap (K := K) g ht
        (v - algebraMap K (X.presheaf.stalk (g P)) (ε v))) := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth 2 _
  let b : CodimensionOnePoint X := ⟨g e, hecod⟩
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) b
  have hp : IsClosed ({g P} : Set X) := by
    simpa only [Set.image_singleton] using g.isClosedMap _ hP
  have hep : g e ≠ g P := by
    intro h
    have hdim := (TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq
      (X ↘ Spec (.of K)) 2).mp inferInstance |>.2 (g P) hp
    rw [← h, ringKrullDim_stalk_eq_coheight, hecod, WithBot.coe_one] at hdim
    norm_num at hdim
  let : Ring.DimensionLEOne (X.presheaf.stalk (g P) ⧸ Ideal.span {u}) :=
    Ring.DimensionLEOne.of_ringEquiv (Ideal.quotEquivOfEq hI.symm)
  exact modelIntersection_centered_coordinate_alternative g hg he ht hte hep u v
    (ideal_stalk_generator_nonunit_at_generization I (he.map g.continuous) heI u hI) ε

include K in
/-- An intersection of divisor closures on a finite-type scheme over a
field has an actual closed common specialization. -/
theorem exists_closed_common_specialization
    [LocallyOfFiniteType (T ↘ Spec (.of K))] {e t : T}
    (hmeet : (closure ({e} : Set T) ∩ closure ({t} : Set T)).Nonempty) :
    ∃ P : T, IsClosed ({P} : Set T) ∧ e ⤳ P ∧ t ⤳ P := by
  have : JacobsonSpace T := LocallyOfFiniteType.jacobsonSpace (T ↘ Spec (.of K))
  obtain ⟨P, ⟨heP, htP⟩, hP⟩ := nonempty_inter_closedPoints hmeet
    (isClosed_closure.inter isClosed_closure).isLocallyClosed
  exact ⟨P, mem_closedPoints_iff.mp hP,
    specializes_iff_mem_closure.mpr heP, specializes_iff_mem_closure.mpr htP⟩

end MixedFujita

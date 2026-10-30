/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LocalAdicOrder
public import Hironaka.Algebra.RegularSmooth.SmoothAt
public import Mathlib.AlgebraicGeometry.Noetherian
public import Hironaka.Scheme.Snc.HasSncWith
public import Hironaka.Scheme.Smooth.SubschemeStalk
public import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import Mathlib.RingTheory.KrullDimension.Regular

/-! An actual order-one stalk equation gives a regular actual closed-subscheme stalk and its exact one-dimensional Krull dimension drop. Over a perfect field it gives an actual smooth open neighborhood; the quotient/stalk identification is constructed by the existing closed-immersion API. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem subscheme_stalk_regular_of_order_one {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : I.subscheme) [IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z))]
    (a : X.presheaf.stalk (I.subschemeι z))
    (hI : I.stalkIdeal (I.subschemeι z) = Ideal.span {a})
    (ha : localAdicOrder (X.presheaf.stalk (I.subschemeι z)) a = 1) :
    IsRegularLocalRing (I.subscheme.presheaf.stalk z) := by
  obtain ⟨hm, hn⟩ := (localAdicOrder_eq_nat_iff _ 1).mp ha
  have hm' : a ∈ maximalIdeal (X.presheaf.stalk (I.subschemeι z)) := by
    simpa only [pow_one] using hm
  have : IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z) ⧸
      I.stalkIdeal (I.subschemeι z)) := by
    rw [hI]
    exact TauCeti.IsRegularLocalRing.quotient_span_singleton hm' hn
  exact IsRegularLocalRing.of_ringEquiv (I.stalkQuotientEquiv z)

theorem subscheme_stalk_dimension_drop_of_order_one {X : Scheme.{u}}
    (I : X.IdealSheafData) (z : I.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z))]
    (a : X.presheaf.stalk (I.subschemeι z))
    (hI : I.stalkIdeal (I.subschemeι z) = Ideal.span {a})
    (ha : localAdicOrder (X.presheaf.stalk (I.subschemeι z)) a = 1) :
    ringKrullDim (I.subscheme.presheaf.stalk z) + 1 =
      ringKrullDim (X.presheaf.stalk (I.subschemeι z)) := by
  obtain ⟨hm, hn⟩ := (localAdicOrder_eq_nat_iff _ 1).mp ha
  have hm' : a ∈ maximalIdeal (X.presheaf.stalk (I.subschemeι z)) := by
    simpa only [pow_one] using hm
  have ha0 : a ≠ 0 := by intro h; exact hn (h ▸ Ideal.zero_mem _)
  rw [← ringKrullDim_eq_of_ringEquiv (I.stalkQuotientEquiv z), hI]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha0) hm'

theorem subscheme_mem_smoothLocus_of_stalk_order_one
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (I : X.IdealSheafData) (z : I.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z))]
    (a : X.presheaf.stalk (I.subschemeι z))
    (hI : I.stalkIdeal (I.subschemeι z) = Ideal.span {a})
    (ha : localAdicOrder (X.presheaf.stalk (I.subschemeι z)) a = 1) :
    z ∈ (I.subschemeι ≫ f).smoothLocus := by
  apply (Scheme.mem_smoothLocus_iff_isRegularAt _ z).mpr
  exact subscheme_stalk_regular_of_order_one I z a hI ha

theorem subscheme_exists_smooth_open_of_stalk_order_one
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (I : X.IdealSheafData) (z : I.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z))]
    (a : X.presheaf.stalk (I.subschemeι z))
    (hI : I.stalkIdeal (I.subschemeι z) = Ideal.span {a})
    (ha : localAdicOrder (X.presheaf.stalk (I.subschemeι z)) a = 1) :
    ∃ U : I.subscheme.Opens, z ∈ U ∧ Smooth (U.ι ≫ I.subschemeι ≫ f) := by
  let := LocallyOfFiniteType.isLocallyNoetherian f
  exact (Scheme.Hom.mem_smoothLocus_iff_exists_smooth _).mp
    (subscheme_mem_smoothLocus_of_stalk_order_one f I z a hI ha)

end MixedFujita
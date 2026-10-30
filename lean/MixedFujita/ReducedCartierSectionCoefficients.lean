/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionPrimeComponents
public import MixedFujita.CartierDivisorCoefficients
public import MixedFujita.CartierWeilVanishingOrder
public import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Ideal

/-!
A reduced actual Cartier zero scheme has coefficient one at every codimension-one point
of its support with a DVR stalk. Its affine coefficient ideal is radical, and localization
preserves radicality. A nonzero nonunit generating a radical ideal in a DVR is a uniformizer.
This avoids constructing an irreducible global cut or a stalk quotient isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Radicality rules out a repeated uniformizer factor in a DVR. -/
theorem dvr_irreducible_of_radical_span {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (r : R) (hr : r ≠ 0) (hu : ¬ IsUnit r)
    (hred : (Ideal.span ({r} : Set R)).IsRadical) : Irreducible r := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hp : ϖ ^ n ∈ Ideal.span ({r} : Set R) := by
    rw [Ideal.mem_span_singleton]
    refine ⟨(v⁻¹ : Rˣ), ?_⟩
    rw [hv]
    calc
      ϖ ^ n = ϖ ^ n * ((v : R) * (v⁻¹ : Rˣ)) := by simp
      _ = (v : R) * ϖ ^ n * (v⁻¹ : Rˣ) := by ring
  have hd : r ∣ ϖ := Ideal.mem_span_singleton.mp (hred ⟨n, hp⟩)
  exact ((hϖ.dvd_iff.mp hd).resolve_left hu).irreducible hϖ

/-- The affine defining ideals of an actual reduced closed subscheme are radical. -/
theorem idealSheaf_ideal_isRadical_of_reduced_subscheme {X : Scheme.{u}}
    (I : X.IdealSheafData) [IsReduced I.subscheme] (U : X.affineOpens) :
    (I.ideal U).IsRadical := by
  have : IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U))) :=
    isReduced_of_isOpenImmersion (I.subschemeCover.f U)
  exact (Ideal.isRadical_iff_quotient_reduced _).mpr
    ((affine_isReduced_iff _).mp this)

attribute [local instance] cartierBaseOpenAlgebra in
/-- SNC charts supply regular ambient stalks, without a separate smoothness hypothesis. -/
theorem isSNCFamily_stalk_regular {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n r : ℕ} {ξ : Fin r → X} (hξ : IsSNCFamily K n ξ) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨c, σ, hx, hc⟩ := hξ x
  have := etaleChart_smooth c
  have := TauCeti.IsRegularRing.of_smooth (R := K) (S := Γ(X, c.U))
  exact TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_isRegularRing c.isAffine hx

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

include K in
/-- A reduced zero scheme gives a radical principal ideal for the actual local coefficient. -/
theorem cartierSection_localCoefficient_span_isRadical
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    [IsReduced (cartierSectionZeroScheme D s hs)]
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    (Ideal.span ({cartierLocalCoefficient D x f hf s} : Set (X.presheaf.stalk x))).IsRadical := by
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  change IsAffineOpen U at hU
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hEq := CartierDivisor.rationalUnitClass_eq_of_le hUV hV
  let g := cartierGlobalOpenCoefficient (K := K) D U f hEq s
  have hg : (Ideal.span ({g} : Set Γ(X, U))).IsRadical := by
    have : IsReduced (cartierSectionZeroIdeal D s hs).subscheme :=
      inferInstanceAs (IsReduced (cartierSectionZeroScheme D s hs))
    rw [← cartierSectionZeroIdeal_ideal_eq_span (K := K) D s hs ⟨U, hU⟩ f hEq]
    exact idealSheaf_ideal_isRadical_of_reduced_subscheme _ _
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have hmap : ((Ideal.span ({g} : Set Γ(X, U))).map
      (algebraMap Γ(X, U) (X.presheaf.stalk x))).IsRadical := by
    apply Ideal.radical_eq_iff.mp
    rw [← IsLocalization.map_radical (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl,
      hg.radical]
  rw [Ideal.map_span, Set.image_singleton] at hmap
  have hcoeff : algebraMap Γ(X, U) (X.presheaf.stalk x) g =
      cartierLocalCoefficient D x f hf s := by
    change X.presheaf.germ U x hxU g = _
    exact cartierGlobalOpenCoefficient_germ (K := K) D U f hEq x hxU s
  simpa only [hcoeff] using hmap

include K in
/-- A reduced cut has multiplicity one along every codimension-one point of its support. -/
theorem cartierSectionZeroDivisor_coefficient_one_of_reduced [IsLocallyNoetherian X]
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    [IsReduced (cartierSectionZeroScheme D s hs)]
    (x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hx : (x : X) ∈ cartierSectionZeroLocus D s) :
    cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) = 1 := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (x : X)
  have hr : cartierLocalCoefficient D (x : X) f hf s ≠ 0 :=
    (cartierLocalCoefficient_ne_zero_iff D (x : X) f hf s).mpr hs
  have hu : ¬ IsUnit (cartierLocalCoefficient D (x : X) f hf s) := by
    rw [← mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (x : X) f hf]
    exact hx
  have hirr := dvr_irreducible_of_radical_span _ hr hu
    (cartierSection_localCoefficient_span_isRadical (K := K) D s hs (x : X) f hf)
  obtain ⟨r, hr0, hrimage, heq, hrorder⟩ :=
    cartierSectionZeroDivisor_regular_localEquation D (x : X) f hf s hs
  rw [cartierCoefficient_eq_ord heq, ← hrimage]
  apply scheme_ord_regular_eq_localAdicOrder_nat x r hr0 1
  rw [hrorder, cartierSectionVanishingOrder_eq_localCoefficient D (x : X) f hf,
    dvr_localAdicOrder_eq_addVal]
  exact IsDiscreteValuationRing.addVal_uniformizer hirr

end MixedFujita

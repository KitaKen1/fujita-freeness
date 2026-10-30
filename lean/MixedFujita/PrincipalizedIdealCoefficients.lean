/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.DominantCartierPullback
public import Hironaka.Scheme.BlowUp.InverseImage
public import Hironaka.Scheme.BlowUp.Transform.StrictTransform

/-!
Coefficients of a principalized sum of ideal sheaves of effective Cartier divisors (step 7).

If the ideal sheaf of an effective Cartier divisor G is the sum of the ideal sheaves of finitely
many effective Cartier divisors A_i, then at every point the coefficient of G is the minimum of
the coefficients of the A_i: it is at most each of them, and equal to one of them. Indeed on a
common affine neighbourhood with regular equations g and a_i one has (g) = (a_1, …, a_k); thus
a_i = r_i g with r_i regular, and g = Σ c_i a_i gives Σ c_i r_i = 1, so some r_i is invertible at
the point.

The ideal sheaf of the pullback of an effective Cartier divisor along a dominant morphism of
integral schemes is the inverse image of its ideal sheaf. Hence, if the inverse image of a sum of
ideal sheaves of effective Cartier divisors is the ideal sheaf of an effective Cartier divisor G
on the source, the coefficient of G at every point is the minimum of the coefficients of the
pullbacks. This is the form in which a principalization is used to isolate the divisors computing
a minimum.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- If (g) = Σ (a_i) on a nonempty open set of an integral scheme, then at every point of the
open set some a_i is g times a function invertible at the point. -/
theorem exists_mul_eq_isUnit_germ_of_span_eq_iSup {ι : Type*} [Finite ι] (U : X.Opens)
    [Nonempty U] (g : Γ(X, U)) (hg : g ≠ 0) (a : ι → Γ(X, U))
    (hspan : Ideal.span ({g} : Set Γ(X, U)) = ⨆ i, Ideal.span ({a i} : Set Γ(X, U)))
    (x : X) (hxU : x ∈ U) :
    ∃ (i : ι) (r : Γ(X, U)), r * g = a i ∧ IsUnit (X.presheaf.germ U x hxU r) := by
  classical
  have := Fintype.ofFinite ι
  -- every a i is a multiple of g
  have hmul : ∀ i, ∃ r : Γ(X, U), r * g = a i := by
    intro i
    have hmem : a i ∈ Ideal.span ({g} : Set Γ(X, U)) := by
      rw [hspan]
      exact le_iSup (fun i => Ideal.span ({a i} : Set Γ(X, U))) i (Ideal.subset_span rfl)
    exact Ideal.mem_span_singleton'.mp hmem
  choose r hr using hmul
  by_contra hno
  -- otherwise every r i is a non-unit at x
  have hnu : ∀ i, X.presheaf.germ U x hxU (r i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hno ⟨i, r i, hr i, hunit⟩
  -- but a combination of them is one
  have hgmem : g ∈ ⨆ i, Ideal.span ({a i} : Set Γ(X, U)) := by
    rw [← hspan]
    exact Ideal.subset_span rfl
  rw [← Ideal.span_iUnion, Set.iUnion_singleton_eq_range,
    Ideal.mem_span_range_iff_exists_fun] at hgmem
  obtain ⟨c, hc⟩ := hgmem
  have hone : ∑ i, c i * r i = 1 := by
    have h1 : (∑ i, c i * r i) * g = g := by
      rw [Finset.sum_mul]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans hc
      rw [mul_assoc, hr i]
    exact mul_right_cancel₀ hg (h1.trans (one_mul g).symm)
  have hmem1 : X.presheaf.germ U x hxU (∑ i, c i * r i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [map_sum]
    exact Ideal.sum_mem _ fun i _ => by
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (hnu i)
  rw [hone, map_one] at hmem1
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top hmem1

/-- On an open set where G and the A_i have regular equations g and a_i with (g) = Σ (a_i), the
coefficient of G at a point of the open set is at most the coefficient of every A_i and equal to
the coefficient of one of them. -/
theorem cartierCoefficient_le_and_exists_eq_of_span_eq_iSup {ι : Type*} [Finite ι]
    (G : CartierDivisor X) (A : ι → CartierDivisor X) (U : X.Opens) [Nonempty U]
    (g : Γ(X, U)) (hg : g ≠ 0) (a : ι → Γ(X, U)) (ha : ∀ i, a i ≠ 0)
    (hEqG : rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U g hg)) =
      G |_ U)
    (hEqA : ∀ i, rationalUnitClass X U
      (Additive.ofMul (regularEquationRationalUnit X U (a i) (ha i))) = A i |_ U)
    (hspan : Ideal.span ({g} : Set Γ(X, U)) = ⨆ i, Ideal.span ({a i} : Set Γ(X, U)))
    (x : X) (hxU : x ∈ U) :
    (∀ i, cartierCoefficient G x ≤ cartierCoefficient (A i) x) ∧
      ∃ i, cartierCoefficient G x = cartierCoefficient (A i) x := by
  have hinj := X.germToFunctionField_injective U
  have hgF : X.germToFunctionField U g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have hcoefG : cartierCoefficient G x = X.ord (X.germToFunctionField U g) x := by
    rw [cartierCoefficient_eq_ord
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqG hxU),
      regularEquationRationalUnit_val]
  have hcoef : ∀ (i : ι) (r : Γ(X, U)), r * g = a i → cartierCoefficient (A i) x =
      X.ord (X.germToFunctionField U r) x + cartierCoefficient G x := by
    intro i r hr
    have hr0 : r ≠ 0 := fun h0 => ha i (by rw [← hr, h0, zero_mul])
    have hrF : X.germToFunctionField U r ≠ 0 := fun h => hr0 (hinj (by rw [h, map_zero]))
    rw [cartierCoefficient_eq_ord
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hEqA i) hxU),
      regularEquationRationalUnit_val, hcoefG, ← hr, map_mul, Scheme.ord_mul hrF hgF]
  refine ⟨fun i => ?_, ?_⟩
  · have hmem : a i ∈ Ideal.span ({g} : Set Γ(X, U)) := by
      rw [hspan]
      exact le_iSup (fun i => Ideal.span ({a i} : Set Γ(X, U))) i (Ideal.subset_span rfl)
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [hcoef i r hr]
    exact le_add_of_nonneg_left
      (TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg r hxU)
  · obtain ⟨i, r, hr, hunit⟩ := exists_mul_eq_isUnit_germ_of_span_eq_iSup U g hg a hspan x hxU
    refine ⟨i, ?_⟩
    rw [hcoef i r hr, ord_germToFunctionField_eq_zero_of_mem_basicOpen U r x
      ((X.mem_basicOpen r x hxU).mpr hunit), zero_add]

omit [IsLocallyNoetherian X] in
/-- On an open set where G and the A_i have regular equations g and a_i with (g) = Σ (a_i), at
every point of the open set G and one of the A_i have a common local equation: they coincide
near the point. -/
theorem exists_common_isLocalEquationAt_of_span_eq_iSup {ι : Type*} [Finite ι]
    (G : CartierDivisor X) (A : ι → CartierDivisor X) (U : X.Opens) [Nonempty U]
    (g : Γ(X, U)) (hg : g ≠ 0) (a : ι → Γ(X, U)) (ha : ∀ i, a i ≠ 0)
    (hEqG : rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U g hg)) =
      G |_ U)
    (hEqA : ∀ i, rationalUnitClass X U
      (Additive.ofMul (regularEquationRationalUnit X U (a i) (ha i))) = A i |_ U)
    (hspan : Ideal.span ({g} : Set Γ(X, U)) = ⨆ i, Ideal.span ({a i} : Set Γ(X, U)))
    (x : X) (hxU : x ∈ U) :
    ∃ (i : ι) (f : X.functionFieldˣ), G.IsLocalEquationAt x f ∧ (A i).IsLocalEquationAt x f := by
  obtain ⟨i, r, hr, hunit⟩ := exists_mul_eq_isUnit_germ_of_span_eq_iSup U g hg a hspan x hxU
  refine ⟨i, regularEquationRationalUnit X U (a i) (ha i), ?_,
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hEqA i) hxU⟩
  have hxV : x ∈ X.basicOpen r := (X.mem_basicOpen r x hxU).mpr hunit
  have hle : X.basicOpen r ≤ U := X.basicOpen_le r
  have : Nonempty (X.basicOpen r : X.Opens) := ⟨⟨x, hxV⟩⟩
  have hu : IsUnit (X.presheaf.map (homOfLE hle).op r) :=
    X.toRingedSpace.isUnit_res_basicOpen r
  have h1 := isLocalEquationAt_regularUnit_mul
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqG hxU) (X.basicOpen r) hxV
    hu.unit
  have heq : regularUnitToFunctionField X (X.basicOpen r) hu.unit *
      regularEquationRationalUnit X U g hg = regularEquationRationalUnit X U (a i) (ha i) := by
    apply Units.ext
    have h2 : ((regularUnitToFunctionField X (X.basicOpen r) hu.unit : X.functionFieldˣ) :
        X.functionField) =
        X.germToFunctionField (X.basicOpen r) (X.presheaf.map (homOfLE hle).op r) := by
      rw [regularUnitToFunctionField_apply, Units.coe_map, IsUnit.unit_spec]
      rfl
    rw [Units.val_mul, h2, regularEquationRationalUnit_val, regularEquationRationalUnit_val,
      germToFunctionField_restrict X hle r, ← map_mul, hr]
  rw [← heq]
  exact h1

omit [IsLocallyNoetherian X] in
/-- If the ideal sheaf of an effective Cartier divisor G is the sum of the ideal sheaves of
finitely many effective Cartier divisors A_i, then near every point there are regular equations
g and a_i on a common affine open set with (g) = Σ (a_i). -/
theorem exists_affineOpen_span_eq_iSup_of_effectiveCartierIdealSheaf_eq_iSup {ι : Type*}
    [Finite ι] (G : CartierDivisor X) (hG : G.IsEffective) (A : ι → CartierDivisor X)
    (hA : ∀ i, (A i).IsEffective)
    (h : effectiveCartierIdealSheaf G hG = ⨆ i, effectiveCartierIdealSheaf (A i) (hA i))
    (x : X) :
    ∃ (U : X.affineOpens) (_ : x ∈ U.1) (_ : Nonempty U.1) (g : Γ(X, U.1)) (hg : g ≠ 0)
      (a : ι → Γ(X, U.1)) (ha : ∀ i, a i ≠ 0),
      rationalUnitClass X U.1 (Additive.ofMul (regularEquationRationalUnit X U.1 g hg)) =
        G |_ U.1 ∧
      (∀ i, rationalUnitClass X U.1
        (Additive.ofMul (regularEquationRationalUnit X U.1 (a i) (ha i))) = A i |_ U.1) ∧
      Ideal.span ({g} : Set Γ(X, U.1)) = ⨆ i, Ideal.span ({a i} : Set Γ(X, U.1)) := by
  obtain ⟨U, hxU, hne, b, hb, hEq⟩ := exists_affineOpen_regularEquations_of_isEffective
    (fun o : Option ι => o.elim G A)
    (fun o => by
      cases o with
      | none => exact hG
      | some i => exact hA i) x
  have hGU : (effectiveCartierIdealSheaf G hG).ideal U = Ideal.span {b none} :=
    effectiveCartierIdealSheaf_ideal_eq_span G hG U (b none) (hb none) (hEq none)
  have hAU : ∀ i, (effectiveCartierIdealSheaf (A i) (hA i)).ideal U =
      Ideal.span {b (some i)} := fun i =>
    effectiveCartierIdealSheaf_ideal_eq_span (A i) (hA i) U (b (some i)) (hb (some i))
      (hEq (some i))
  have h1 : (effectiveCartierIdealSheaf G hG).ideal U =
      (⨆ i, effectiveCartierIdealSheaf (A i) (hA i)).ideal U := by rw [h]
  rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply] at h1
  have hspan : Ideal.span ({b none} : Set Γ(X, U.1)) =
      ⨆ i, Ideal.span ({b (some i)} : Set Γ(X, U.1)) := by
    rw [← hGU, h1]
    exact iSup_congr hAU
  exact ⟨U, hxU, hne, b none, hb none, fun i => b (some i), fun i => hb (some i), hEq none,
    fun i => hEq (some i), hspan⟩

/-- If the ideal sheaf of an effective Cartier divisor G is the sum of the ideal sheaves of
finitely many effective Cartier divisors, then at every point the coefficient of G is at most the
coefficient of each of them and equal to the coefficient of one of them. -/
theorem cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_iSup {ι : Type*}
    [Finite ι] (G : CartierDivisor X) (hG : G.IsEffective) (A : ι → CartierDivisor X)
    (hA : ∀ i, (A i).IsEffective)
    (h : effectiveCartierIdealSheaf G hG = ⨆ i, effectiveCartierIdealSheaf (A i) (hA i))
    (x : X) :
    (∀ i, cartierCoefficient G x ≤ cartierCoefficient (A i) x) ∧
      ∃ i, cartierCoefficient G x = cartierCoefficient (A i) x := by
  obtain ⟨U, hxU, hne, g, hg, a, ha, hEqG, hEqA, hspan⟩ :=
    exists_affineOpen_span_eq_iSup_of_effectiveCartierIdealSheaf_eq_iSup G hG A hA h x
  exact cartierCoefficient_le_and_exists_eq_of_span_eq_iSup G A U.1 g hg a ha hEqG hEqA hspan x
    hxU

omit [IsLocallyNoetherian X] in
/-- If the ideal sheaf of an effective Cartier divisor G is the sum of the ideal sheaves of
finitely many effective Cartier divisors, then at every point G and one of them have a common
local equation. -/
theorem exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_iSup {ι : Type*}
    [Finite ι] (G : CartierDivisor X) (hG : G.IsEffective) (A : ι → CartierDivisor X)
    (hA : ∀ i, (A i).IsEffective)
    (h : effectiveCartierIdealSheaf G hG = ⨆ i, effectiveCartierIdealSheaf (A i) (hA i))
    (x : X) :
    ∃ (i : ι) (f : X.functionFieldˣ), G.IsLocalEquationAt x f ∧ (A i).IsLocalEquationAt x f := by
  obtain ⟨U, hxU, hne, g, hg, a, ha, hEqG, hEqA, hspan⟩ :=
    exists_affineOpen_span_eq_iSup_of_effectiveCartierIdealSheaf_eq_iSup G hG A hA h x
  exact exists_common_isLocalEquationAt_of_span_eq_iSup G A U.1 g hg a ha hEqG hEqA hspan x hxU

section Pullback

variable {T : Scheme.{u}} [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

omit [IsLocallyNoetherian X] in
/-- Near every point of the source of a dominant morphism, the pullback of an effective Cartier
divisor has as regular equation the pullback of a regular equation of the divisor. -/
theorem exists_affineOpen_regularEquation_cartierPullback (A : CartierDivisor X)
    (hA : A.IsEffective) (t : T) :
    ∃ (U : X.affineOpens) (_ : Nonempty U.1) (a : Γ(X, U.1)) (ha : a ≠ 0)
      (_ : rationalUnitClass X U.1 (Additive.ofMul (regularEquationRationalUnit X U.1 a ha)) =
        A |_ U.1)
      (V : T.affineOpens) (_ : t ∈ V.1) (_ : Nonempty V.1) (e : V.1 ≤ ρ ⁻¹ᵁ U.1)
      (hb : ρ.appLE U.1 V.1 e a ≠ 0),
      rationalUnitClass T V.1 (Additive.ofMul
        (regularEquationRationalUnit T V.1 (ρ.appLE U.1 V.1 e a) hb)) =
          cartierPullback ρ A |_ V.1 := by
  obtain ⟨U, hxU, hne, a, ha, hEq⟩ :=
    exists_affineOpen_regularEquation_of_isEffective A hA (ρ t)
  have hloc := cartierPullback_isLocalEquationAt ρ A t
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxU)
  obtain ⟨V', htV', hV'⟩ := CartierDivisor.isLocalEquationAt_iff.mp hloc
  have htW : t ∈ V' ⊓ ρ ⁻¹ᵁ U.1 := ⟨htV', hxU⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVW⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open htW (V' ⊓ ρ ⁻¹ᵁ U.1).isOpen
  have hneV : Nonempty V := ⟨⟨t, htV⟩⟩
  have hneV' : Nonempty V' := ⟨⟨t, htV'⟩⟩
  have hVW' : V ≤ V' ⊓ ρ ⁻¹ᵁ U.1 := hVW
  have e : V ≤ ρ ⁻¹ᵁ U.1 := hVW'.trans inf_le_right
  have hval : T.germToFunctionField V (ρ.appLE U.1 V e a) =
      (dominantFunctionFieldMap ρ).hom (X.germToFunctionField U.1 a) :=
    (dominantFunctionFieldMap_germ ρ U.1 V e a).symm
  have hunit0 : (dominantFunctionFieldMap ρ).hom (X.germToFunctionField U.1 a) ≠ 0 :=
    (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
      (regularEquationRationalUnit X U.1 a ha)).ne_zero
  have hb : ρ.appLE U.1 V e a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact hunit0 hval.symm
  have hunit : regularEquationRationalUnit T V (ρ.appLE U.1 V e a) hb =
      Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (regularEquationRationalUnit X U.1 a ha) := Units.ext hval
  refine ⟨U, hne, a, ha, hEq, ⟨V, hV⟩, htV, hneV, e, hb, ?_⟩
  change rationalUnitClass T V (Additive.ofMul
    (regularEquationRationalUnit T V (ρ.appLE U.1 V e a) hb)) = cartierPullback ρ A |_ V
  rw [hunit]
  exact CartierDivisor.rationalUnitClass_eq_of_le (hVW'.trans inf_le_left) hV'

omit [IsLocallyNoetherian X] in
/-- The pullback of an effective Cartier divisor along a dominant morphism of integral schemes
is effective. -/
theorem cartierPullback_isEffective (A : CartierDivisor X) (hA : A.IsEffective) :
    (cartierPullback ρ A).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro t
  obtain ⟨U, hne, a, ha, hEq, V, htV, hneV, e, hb, hEqV⟩ :=
    exists_affineOpen_regularEquation_cartierPullback ρ A hA t
  exact ⟨regularEquationRationalUnit T V.1 (ρ.appLE U.1 V.1 e a) hb,
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqV htV,
    regularEquationRationalUnit_mem_stalk_range T V.1 _ hb t htV⟩

omit [IsLocallyNoetherian X] in
/-- The ideal sheaf of the pullback of an effective Cartier divisor along a dominant morphism of
integral schemes is the inverse image of the ideal sheaf of the divisor. -/
theorem effectiveCartierIdealSheaf_cartierPullback (A : CartierDivisor X) (hA : A.IsEffective) :
    effectiveCartierIdealSheaf (cartierPullback ρ A) (cartierPullback_isEffective ρ A hA) =
      (effectiveCartierIdealSheaf A hA).comap ρ := by
  choose U hne a ha hEq V htV hneV e hb hEqV using
    exists_affineOpen_regularEquation_cartierPullback ρ A hA
  have hcover : ⨆ t : T, (V t).1 = ⊤ := by
    apply top_unique
    intro t _
    exact Opens.mem_iSup.mpr ⟨t, htV t⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hcover
  intro t
  rw [effectiveCartierIdealSheaf_ideal_eq_span (cartierPullback ρ A) _ (V t) _ (hb t) (hEqV t),
    Scheme.IdealSheafData.ideal_comap_of_le _ ρ (U t) (V t) (e t),
    effectiveCartierIdealSheaf_ideal_eq_span A hA (U t) (a t) (ha t) (hEq t),
    Ideal.map_span, Set.image_singleton]

omit [IsLocallyNoetherian X] in
/-- If the inverse image along a dominant morphism of the sum of the ideal sheaves of finitely
many effective Cartier divisors A_i is the ideal sheaf of an effective Cartier divisor G on the
source, then at every point the coefficient of G is at most the coefficient of the pullback of
each A_i and equal to the coefficient of the pullback of one of them. -/
theorem cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
    [IsLocallyNoetherian T] {ι : Type*} [Finite ι] (A : ι → CartierDivisor X)
    (hA : ∀ i, (A i).IsEffective) (G : CartierDivisor T) (hG : G.IsEffective)
    (h : effectiveCartierIdealSheaf G hG =
      (⨆ i, effectiveCartierIdealSheaf (A i) (hA i)).comap ρ) (t : T) :
    (∀ i, cartierCoefficient G t ≤ cartierCoefficient (cartierPullback ρ (A i)) t) ∧
      ∃ i, cartierCoefficient G t = cartierCoefficient (cartierPullback ρ (A i)) t := by
  refine cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_iSup G hG
    (fun i => cartierPullback ρ (A i)) (fun i => cartierPullback_isEffective ρ (A i) (hA i))
    ?_ t
  rw [h, Scheme.IdealSheafData.comap_iSup]
  exact iSup_congr fun i => (effectiveCartierIdealSheaf_cartierPullback ρ (A i) (hA i)).symm

omit [IsLocallyNoetherian X] in
/-- If the inverse image along a dominant morphism of the sum of the ideal sheaves of finitely
many effective Cartier divisors A_i is the ideal sheaf of an effective Cartier divisor G on the
source, then at every point G and the pullback of one of the A_i have a common local equation. -/
theorem exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup {ι : Type*}
    [Finite ι] (A : ι → CartierDivisor X) (hA : ∀ i, (A i).IsEffective) (G : CartierDivisor T)
    (hG : G.IsEffective)
    (h : effectiveCartierIdealSheaf G hG =
      (⨆ i, effectiveCartierIdealSheaf (A i) (hA i)).comap ρ) (t : T) :
    ∃ (i : ι) (f : T.functionFieldˣ), G.IsLocalEquationAt t f ∧
      (cartierPullback ρ (A i)).IsLocalEquationAt t f := by
  refine exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_iSup G hG
    (fun i => cartierPullback ρ (A i)) (fun i => cartierPullback_isEffective ρ (A i) (hA i))
    ?_ t
  rw [h, Scheme.IdealSheafData.comap_iSup]
  exact iSup_congr fun i => (effectiveCartierIdealSheaf_cartierPullback ρ (A i) (hA i)).symm

end Pullback

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionLifting
public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.NormalCartierLocalUnits
public import TauCeti.AlgebraicGeometry.Scheme.Regular
public import MixedFujita.SNCBoundaryDiscrepancy
public import MixedFujita.LocalBirationalOrders

/-!
Lifting sections on a normal scheme, in terms of the coefficients of the divisors (step 12,
section 6.3 of the manuscript).

On a normal locally Noetherian integral scheme a rational function g is a section of O(D) over
an open subset W as soon as ord_z(g) + (coefficient of D at z) ≥ 0 at the codimension-one points
z of W (Hartogs). Let E be an effective Cartier divisor whose coefficients vanish at the
codimension-one points outside a closed subset Z, let W be an open neighbourhood of Z and g_W a
nonzero rational function with ord_z(g_W) + D_z ≥ 0 on W, with equality at a codimension-one point
ξ of Z at which E has positive coefficient. If H¹(O(D − E)) = 0, there is a global section g of
O(D) with ord_ξ(g) + D_ξ = 0: a section of O(D) not vanishing along ξ.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- On a normal scheme a rational function whose order at every codimension-one point of W is at
least minus the coefficient of D is a section of O(D) over W. -/
theorem cartier_mem_sections_of_forall_ord
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D : CartierDivisor X)
    (W : X.Opens) [Nonempty W] (g : X.functionField)
    (h : ∀ z : CodimensionOnePoint X, (z : X) ∈ W →
      0 ≤ X.ord g (z : X) + cartierCoefficient D (z : X)) :
    (rationalFunctionsEquiv (X := X) W).symm g ∈ D.sections W := by
  rw [CartierDivisor.mem_sections]
  intro x hx f hf
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  apply mem_range_stalk_of_codimOne hnorm x (V ⊓ W) ⟨hxV, hx⟩
  intro ξ hξ hξ1
  have hfξ : D.IsLocalEquationAt ξ f :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV hξ.1
  let := hnorm ξ
  have : IsDiscreteValuationRing (X.presheaf.stalk ξ) :=
    normal_codimensionOne_stalk_DVR (⟨ξ, hξ1⟩ : CodimensionOnePoint X)
  by_cases hg : g = 0
  · rw [hg, mul_zero]
    exact ⟨0, map_zero _⟩
  · have hord : 0 ≤ X.ord ((f : X.functionField) * g) ξ := by
      rw [X.ord_mul (Units.ne_zero f) hg, ← cartierCoefficient_eq_ord hfξ]
      have h1 := h ⟨ξ, hξ1⟩ hξ.2
      linarith
    obtain ⟨a, ha⟩ := Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg hξ1 hord
    exact ⟨a, ha⟩

/-- Lifting a section not vanishing along a prime divisor: on a normal scheme, if H¹(O(D − E))
vanishes for an effective Cartier divisor E with coefficients zero outside a closed subset Z, a
nonzero rational function g_W with ord + D ≥ 0 on an open neighbourhood W of Z and ord + D = 0 at
a codimension-one point ξ of Z where E has positive coefficient gives a global section g of O(D)
with ord_ξ(g) + D_ξ = 0. -/
theorem exists_global_section_ord_eq_of_vanishing
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (D E : CartierDivisor X)
    (hE : E.IsEffective) (hvan : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf 1))
    (Z : Set X) (hZ : IsClosed Z)
    (hEZ : ∀ z : CodimensionOnePoint X, (z : X) ∉ Z → cartierCoefficient E (z : X) = 0)
    (W : X.Opens) (hZW : Z ⊆ W) (gW : X.functionField) (hgW0 : gW ≠ 0)
    (hgW : ∀ z : CodimensionOnePoint X, (z : X) ∈ W →
      0 ≤ X.ord gW (z : X) + cartierCoefficient D (z : X))
    (ξ : CodimensionOnePoint X) (hξZ : (ξ : X) ∈ Z) (hEξ : 1 ≤ cartierCoefficient E (ξ : X))
    (hgen : X.ord gW (ξ : X) + cartierCoefficient D (ξ : X) = 0) :
    ∃ g : X.functionField, g ≠ 0 ∧ (rationalFunctionsEquiv (X := X) ⊤).symm g ∈ D.sections ⊤ ∧
      X.ord g (ξ : X) + cartierCoefficient D (ξ : X) = 0 := by
  have hξW : (ξ : X) ∈ W := hZW hξZ
  have : Nonempty W := ⟨⟨(ξ : X), hξW⟩⟩
  let := hnorm (ξ : X)
  have hdvr : IsDiscreteValuationRing (X.presheaf.stalk (ξ : X)) :=
    normal_codimensionOne_stalk_DVR ξ
  let V : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have hWV : W ⊔ V = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ Z
    · exact Or.inl (hZW hx)
    · exact Or.inr hx
  -- away from Z the sections of O(D) are sections of O(D − E)
  have hV : D.sections (W ⊓ V) ≤ (D - E).sections (W ⊓ V) := by
    intro s hs
    rw [CartierDivisor.mem_sections]
    intro x hx f hf
    obtain ⟨V', hxV', hV'⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    have : Nonempty V' := ⟨⟨x, hxV'⟩⟩
    have : Nonempty (W ⊓ V : X.Opens) := ⟨⟨x, hx⟩⟩
    apply mem_range_stalk_of_codimOne hnorm x (V' ⊓ (W ⊓ V)) ⟨hxV', hx⟩
    intro ζ hζ hζ1
    have hfζ : (D - E).IsLocalEquationAt ζ f :=
      CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV' hζ.1
    obtain ⟨e, he⟩ := E.exists_isLocalEquationAt ζ
    let := hnorm ζ
    have : IsDiscreteValuationRing (X.presheaf.stalk ζ) :=
      normal_codimensionOne_stalk_DVR (⟨ζ, hζ1⟩ : CodimensionOnePoint X)
    obtain ⟨v, hv⟩ := scheme_ord_zero_exists_stalk_unit (⟨ζ, hζ1⟩ : CodimensionOnePoint X) e
      (by rw [← cartierCoefficient_eq_ord he]; exact hEZ ⟨ζ, hζ1⟩ hζ.2.2)
    have hfe : D.IsLocalEquationAt ζ (f * e) := by
      have h1 := hfζ.mul he
      rwa [sub_add_cancel] at h1
    obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hs) ζ hζ.2 (f * e) hfe
    refine ⟨(v⁻¹ : (X.presheaf.stalk ζ)ˣ) * a, ?_⟩
    rw [map_mul, map_units_inv, hv, ha, Units.val_mul]
    field_simp
  have hgW' : (rationalFunctionsEquiv (X := X) W).symm gW ∈ D.sections W :=
    cartier_mem_sections_of_forall_ord hnorm D W gW hgW
  -- local equations at ξ
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ξ : X)
  obtain ⟨e, he⟩ := E.exists_isLocalEquationAt (ξ : X)
  have heord : 1 ≤ X.ord (e : X.functionField) (ξ : X) := by
    rw [← cartierCoefficient_eq_ord he]
    exact hEξ
  obtain ⟨a, ha⟩ := Scheme.exists_algebraMap_stalk_eq_of_ord_nonneg ξ.property
    (show 0 ≤ X.ord (e : X.functionField) (ξ : X) by omega)
  have hamem : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (ξ : X)) := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    have h0 := scheme_ord_stalk_unit (ξ : X) hunit.unit
    rw [IsUnit.unit_spec, ha] at h0
    omega
  have hfg0 : (f : X.functionField) * gW ≠ 0 := mul_ne_zero (Units.ne_zero f) hgW0
  obtain ⟨u, hu⟩ := scheme_ord_zero_exists_stalk_unit ξ (Units.mk0 _ hfg0) (by
    rw [Units.val_mk0, X.ord_mul (Units.ne_zero f) hgW0, ← cartierCoefficient_eq_ord hf]
    linarith)
  obtain ⟨g, hg, u', hu'⟩ := cartierSections_exists_global_generator D E hE hvan W V hWV hV gW
    hgW' (ξ : X) hξW f e hf he ⟨a, hamem, ha⟩ ⟨u, hu⟩
  have hfg : (f : X.functionField) * g ≠ 0 := by
    rw [← hu']
    exact (u'.isUnit.map _).ne_zero
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg
  refine ⟨g, hg0, hg, ?_⟩
  have h0 := scheme_ord_stalk_unit (ξ : X) u'
  rw [hu', X.ord_mul (Units.ne_zero f) hg0, ← cartierCoefficient_eq_ord hf] at h0
  linarith

section Descent

variable {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian T]

omit [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- A nonzero section of O(D) over W has order at least minus the coefficient of D at the points
of W. -/
theorem cartier_ord_add_coefficient_nonneg_of_mem_sections (D : CartierDivisor T) (W : T.Opens)
    [Nonempty W] (g : T.functionField)
    (hg : (rationalFunctionsEquiv (X := T) W).symm g ∈ D.sections W) (hg0 : g ≠ 0) (z : T)
    (hz : z ∈ W) : 0 ≤ T.ord g z + cartierCoefficient D z := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt z
  have hr := (CartierDivisor.mem_sections.mp hg) z hz f hf
  rw [LinearEquiv.apply_symm_apply] at hr
  have h := scheme_ord_nonneg_of_mem_stalk z _ hr
  rw [T.ord_mul (Units.ne_zero f) hg0, ← cartierCoefficient_eq_ord hf] at h
  linarith

/-- Lifting and descent (section 6.3). Let ρ : T → Y be a proper birational morphism of normal
schemes, P a Cartier divisor of Y, C a Cartier divisor of T and S an effective Cartier divisor of
T with H¹(T, O(ρ*P + C − S)) = 0. Let Z be a closed subset of T mapping to one point x of Y,
outside of which S has coefficient zero, with C ≥ 0 at the codimension-one points of an open
neighbourhood of Z, C ≤ 0 at the codimension-one points of T which are not exceptional, and let ξ
be a codimension-one point of Z at which S has positive coefficient and C coefficient zero. Then P
has a global section generating it at x. -/
theorem exists_section_generating_of_lifting
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ Y) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (P : CartierDivisor Y) (C Sd : CartierDivisor T) (hSd : Sd.IsEffective)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (cartierPullback ρ P + C - Sd).sheaf 1))
    (Z : Set T) (hZ : IsClosed Z)
    (hSdZ : ∀ z : CodimensionOnePoint T, (z : T) ∉ Z → cartierCoefficient Sd (z : T) = 0)
    (W₀ : T.Opens) (hZW₀ : Z ⊆ W₀)
    (hCW₀ : ∀ z : CodimensionOnePoint T, (z : T) ∈ W₀ → 0 ≤ cartierCoefficient C (z : T))
    (hCexc : ∀ z : CodimensionOnePoint T, Order.coheight (ρ (z : T)) = 1 →
      cartierCoefficient C (z : T) ≤ 0)
    (ξ : CodimensionOnePoint T) (hξZ : (ξ : T) ∈ Z) (hSdξ : 1 ≤ cartierCoefficient Sd (ξ : T))
    (hCξ : cartierCoefficient C (ξ : T) = 0) (hZρ : ∀ t ∈ Z, ρ t = ρ (ξ : T)) :
    ∃ (g : Y.functionField) (f : Y.functionFieldˣ) (u : (Y.presheaf.stalk (ρ (ξ : T)))ˣ),
      (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ ∧
      P.IsLocalEquationAt (ρ (ξ : T)) f ∧
      algebraMap (Y.presheaf.stalk (ρ (ξ : T))) Y.functionField u = f * g := by
  obtain ⟨f, hf⟩ := P.exists_isLocalEquationAt (ρ (ξ : T))
  obtain ⟨Y₀, hxY₀, hY₀⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty Y₀ := ⟨⟨ρ (ξ : T), hxY₀⟩⟩
  have hφf0 : (dominantFunctionFieldMap ρ).hom (f : Y.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero f)
  have hZW : Z ⊆ ((ρ ⁻¹ᵁ Y₀) ⊓ W₀ : T.Opens) := fun t ht =>
    ⟨by change ρ t ∈ Y₀; rw [hZρ t ht]; exact hxY₀, hZW₀ ht⟩
  -- the coefficient of ρ*P over Y₀ is the order of the pulled back equation
  have hcoefP : ∀ t : T, ρ t ∈ Y₀ → cartierCoefficient (cartierPullback ρ P) t =
      T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField)) t := fun t ht => by
    rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ P t
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hY₀ ht))]
    rfl
  have hgW : ∀ z : CodimensionOnePoint T, (z : T) ∈ ((ρ ⁻¹ᵁ Y₀) ⊓ W₀ : T.Opens) →
      0 ≤ T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField))⁻¹ (z : T) +
        cartierCoefficient (cartierPullback ρ P + C) (z : T) := by
    intro z hz
    rw [Scheme.ord_inv, cartierCoefficient_add, hcoefP (z : T) hz.1]
    have h1 := hCW₀ z hz.2
    linarith
  have hgen : T.ord ((dominantFunctionFieldMap ρ).hom (f : Y.functionField))⁻¹ (ξ : T) +
      cartierCoefficient (cartierPullback ρ P + C) (ξ : T) = 0 := by
    rw [Scheme.ord_inv, cartierCoefficient_add, hcoefP (ξ : T) hxY₀, hCξ]
    ring
  obtain ⟨gT, hgT0, hgT, hgTξ⟩ := exists_global_section_ord_eq_of_vanishing hnormT
    (cartierPullback ρ P + C) Sd hSd hvan Z hZ hSdZ _ hZW _ (inv_ne_zero hφf0) hgW ξ hξZ hSdξ
    hgen
  obtain ⟨g, rfl⟩ := hρ.2 gT
  have hg0 : g ≠ 0 := fun h => hgT0 (by rw [h, map_zero])
  have hneT : Nonempty (⊤ : T.Opens) := ⟨⟨(ξ : T), trivial⟩⟩
  have hneY : Nonempty (⊤ : Y.Opens) := ⟨⟨ρ (ξ : T), trivial⟩⟩
  -- descent: g is a section of P
  have hgP : (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤ := by
    apply cartier_mem_sections_of_forall_ord hnormY P ⊤ g
    intro y _
    obtain ⟨t, ht, hb⟩ := proper_birational_exists_normal_prime_lift hnormY ρ hρ y
    have hcoh : Order.coheight (ρ (t : T)) = 1 := by rw [ht]; exact y.property
    let := hnormY (ρ (t : T))
    let := hnormT (t : T)
    have : IsDiscreteValuationRing (Y.presheaf.stalk (ρ (t : T))) :=
      normal_codimensionOne_stalk_DVR (⟨ρ (t : T), hcoh⟩ : CodimensionOnePoint Y)
    have : IsDiscreteValuationRing (T.presheaf.stalk (t : T)) := normal_codimensionOne_stalk_DVR t
    have h1 := scheme_ord_pullback_of_stalkMap_bijective ρ t hcoh hb g
    have h2 := cartierCoefficient_pullback_of_stalkMap_bijective ρ t hcoh hb P
    have h3 := cartier_ord_add_coefficient_nonneg_of_mem_sections (cartierPullback ρ P + C) ⊤
      ((dominantFunctionFieldMap ρ).hom g) hgT hgT0 (t : T) trivial
    rw [cartierCoefficient_add] at h3
    have h4 := hCexc t hcoh
    rw [← ht, ← h1, ← h2]
    linarith
  -- generation at the image of ξ
  obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hgP) (ρ (ξ : T)) trivial f hf
  rw [LinearEquiv.apply_symm_apply] at ha
  let := hnormT (ξ : T)
  have : IsDiscreteValuationRing (T.presheaf.stalk (ξ : T)) := normal_codimensionOne_stalk_DVR ξ
  have hpull : (dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g) =
      algebraMap (T.presheaf.stalk (ξ : T)) T.functionField (ρ.stalkMap (ξ : T) a) := by
    rw [← ha, dominantFunctionFieldMap_algebraMap]
  have hne : (dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g) ≠ 0 :=
    (map_ne_zero _).mpr (mul_ne_zero (Units.ne_zero f) hg0)
  have hord0 : T.ord ((dominantFunctionFieldMap ρ).hom ((f : Y.functionField) * g)) (ξ : T) =
      0 := by
    rw [map_mul, T.ord_mul hφf0 hgT0, ← hcoefP (ξ : T) hxY₀]
    rw [cartierCoefficient_add, hCξ] at hgTξ
    linarith
  obtain ⟨v, hv⟩ := scheme_ord_zero_exists_stalk_unit ξ (Units.mk0 _ hne) hord0
  have hva : ρ.stalkMap (ξ : T) a = (v : T.presheaf.stalk (ξ : T)) := by
    apply IsFractionRing.injective (T.presheaf.stalk (ξ : T)) T.functionField
    rw [← hpull, hv]
    rfl
  have hunit : IsUnit a := by
    have hv' : IsUnit (ρ.stalkMap (ξ : T) a) := by rw [hva]; exact v.isUnit
    exact isUnit_of_map_unit (ρ.stalkMap (ξ : T)).hom a hv'
  exact ⟨g, f, hunit.unit, hgP, hf, by rw [IsUnit.unit_spec]; exact ha⟩

end Descent

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DVRSupportPositiveCartierCoefficient
public import MixedFujita.NormalBirationalPrimeLifts

/-!
Recover the actual support of an effective Cartier divisor from a finite family
supporting its prime coefficients. Normal Hartogs gives the reverse inclusion;
neither reducedness of the cut nor local factoriality is required.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Finite prime-coefficient support determines the support of the actual effective ideal. -/
theorem effectiveCartier_support_eq_positive_member_union
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (S : CartierDivisor T) (hS : S.IsEffective) {J : Type*} [Finite J]
    (ξ : J → T)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient S (t : T) = 0) :
    ((effectiveCartierIdealSheaf S hS).support : Set T) =
      ⋃ i ∈ {i | 0 < cartierCoefficient S (ξ i)}, closure ({ξ i} : Set T) := by
  classical
  let : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => by let := hnorm (z : T); exact normal_codimensionOne_stalk_DVR z
  let C : Set T := ⋃ i ∈ {i | 0 < cartierCoefficient S (ξ i)}, closure ({ξ i} : Set T)
  have hclosed : IsClosed C := isClosed_iUnion_of_finite fun i =>
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxC
    let W : T.Opens := ⟨Cᶜ, hclosed.isOpen_compl⟩
    have hxW : x ∈ W := hxC
    have hzero (z : CodimensionOnePoint T) (hz : (z : T) ∈ W) : cartierCoefficient S (z : T) = 0 := by
      by_cases hmem : (z : T) ∈ Set.range ξ
      · obtain ⟨i, hi⟩ := hmem
        have hnon := cartierCoefficient_nonneg_of_isEffective S hS (z : T)
        have hnot : ¬ 0 < cartierCoefficient S (z : T) := by
          intro hpos
          apply hz
          exact Set.mem_iUnion₂.mpr ⟨i, by change 0 < cartierCoefficient S (ξ i); rwa [hi],
            hi ▸ subset_closure (Set.mem_singleton (ξ i))⟩
        omega
      · exact hsupport z hmem
    obtain ⟨U, hxU, hne, a, ha, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective S hS x
    let := hne
    let f := regularEquationRationalUnit T U.1 a ha
    obtain ⟨v, hv⟩ := normal_scheme_ord_zero_exists_stalk_unit hnorm x (U.1 ⊓ W) ⟨hxU, hxW⟩ f (by
      intro z hz
      rw [← cartierCoefficient_eq_ord
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hz.1)]
      exact hzero z hz.2)
    have hgerm : T.presheaf.germ U.1 x hxU a = (v : T.presheaf.stalk x) := by
      apply IsFractionRing.injective (T.presheaf.stalk x) T.functionField
      rw [T.algebraMap_germ_eq_germToFunctionField hxU, hv]
      rfl
    have hbasic : x ∈ T.basicOpen a := (T.mem_basicOpen a x hxU).mpr (hgerm.symm ▸ v.isUnit)
    change x ∈ (effectiveCartierIdealSheaf S hS).support at hx
    rw [(effectiveCartierIdealSheaf S hS).mem_support_iff_of_mem (U := U) hxU,
      effectiveCartierIdealSheaf_ideal_eq_span S hS U a ha hEq, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at hx
    exact hx hbasic
  · intro x hx
    obtain ⟨i, hi, hix⟩ := Set.mem_iUnion₂.mp hx
    have hmem : ξ i ∈ (effectiveCartierIdealSheaf S hS).support := by
      by_contra hnot
      have hz := cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf S hS (ξ i) hnot
      exact (ne_of_gt hi) hz
    exact (specializes_iff_mem_closure.mpr hix).mem_closed
      (effectiveCartierIdealSheaf S hS).support.isClosed hmem

/-- A threshold description of the cut's prime coefficients gives its full topological support. -/
theorem effectiveCartier_support_eq_threshold_member_union
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (hnorm : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (B S : CartierDivisor T) (hS : S.IsEffective) (d : ℕ) (hd : 1 ≤ d)
    {J : Type*} [Finite J] (ξ : J → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hSc : ∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) ↔
      (d : ℤ) ≤ cartierCoefficient B (t : T)) :
    ((effectiveCartierIdealSheaf S hS).support : Set T) =
      ⋃ i ∈ {i | (d : ℤ) ≤ cartierCoefficient B (ξ i)}, closure ({ξ i} : Set T) := by
  have hSsupport (t : CodimensionOnePoint T) (ht : (t : T) ∉ Set.range ξ) :
      cartierCoefficient S (t : T) = 0 := by
    have hnon := cartierCoefficient_nonneg_of_isEffective S hS (t : T)
    have hb := hsupport t ht
    have hc := hSc t
    have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
    omega
  rw [effectiveCartier_support_eq_positive_member_union hnorm S hS ξ hSsupport]
  apply Set.iUnion_congr
  intro i
  simp only [Set.mem_setOf_eq]
  rw [show (0 < cartierCoefficient S (ξ i)) = ((d : ℤ) ≤ cartierCoefficient B (ξ i)) from
    propext (hSc ⟨ξ i, hξ i⟩)]

/-- The actual cut fibre maps onto the support intersected with the model fibre. -/
theorem effectiveCartier_cut_fibre_image {T X : Scheme.{u}} [IsIntegral T]
    (ρ : T ⟶ X) (S : CartierDivisor T) (hS : S.IsEffective) (x : X) :
    (effectiveCartierIdealSheaf S hS).subschemeι ''
      (((effectiveCartierIdealSheaf S hS).subschemeι ≫ ρ) ⁻¹' {x}) =
      ((effectiveCartierIdealSheaf S hS).support : Set T) ∩ ρ ⁻¹' {x} := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Set.mem_range_self s, hs⟩
  · rintro ⟨⟨s, rfl⟩, hs⟩
    exact ⟨s, hs, rfl⟩

/-- Connectedness of the actual possibly nonreduced cut fibre is exactly connectedness
of its support inside the model fibre. -/
theorem effectiveCartier_cut_fibre_preconnected_iff {T X : Scheme.{u}} [IsIntegral T]
    (ρ : T ⟶ X) (S : CartierDivisor T) (hS : S.IsEffective) (x : X) :
    _root_.IsPreconnected (((effectiveCartierIdealSheaf S hS).subschemeι ≫ ρ) ⁻¹' {x}) ↔
      _root_.IsPreconnected (((effectiveCartierIdealSheaf S hS).support : Set T) ∩ ρ ⁻¹' {x}) := by
  rw [← effectiveCartier_cut_fibre_image]
  exact (effectiveCartierIdealSheaf S hS).subschemeι.isClosedEmbedding.isEmbedding.isInducing.isPreconnected_image.symm

end MixedFujita

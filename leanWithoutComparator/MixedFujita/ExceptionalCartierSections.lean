/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.NormalCartierLocalUnits

/-!
Adding an effective exceptional Cartier divisor to a birational pullback does not
add sections, over any nonempty open of a normal target. Exceptionality is the
actual coefficient-zero condition over codimension-one target points; neither
section descent nor the desired rank condition is supplied as a hypothesis.

This is the Hartogs component of the F2 rank calculation. Constructing the
rounded crepant boundary as an effective exceptional Cartier divisor and the
actual direct-image sheaf isomorphism remain separate tasks.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Sections

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- Actual sections on an open pull back to its inverse image. -/
theorem cartierPullback_mem_sections_on_open
    (ρ : T ⟶ X) [IsDominant ρ] (D : CartierDivisor X) (U : X.Opens)
    [Nonempty U] [Nonempty (ρ ⁻¹ᵁ U)] (g : X.functionField)
    (hg : (rationalFunctionsEquiv (X := X) U).symm g ∈ D.sections U) :
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom g) ∈ (cartierPullback ρ D).sections (ρ ⁻¹ᵁ U) := by
  rw [CartierDivisor.mem_sections_iff_exists]
  intro t ht
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
  refine ⟨_, cartierPullback_isLocalEquationAt ρ D t hf, ?_⟩
  obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hg) (ρ t) ht f hf
  refine ⟨ρ.stalkMap t a, ?_⟩
  rw [← dominantFunctionFieldMap_algebraMap, ha]
  simp only [LinearEquiv.apply_symm_apply, Units.coe_map, map_mul]
  rfl

/-- Effectivity gives the inclusion of actual section spaces on every open. -/
theorem mem_sections_add_effective_on_open (D E : CartierDivisor X) (hE : E.IsEffective)
    (U : X.Opens) [Nonempty U] (g : X.functionField)
    (hg : (rationalFunctionsEquiv (X := X) U).symm g ∈ D.sections U) :
    (rationalFunctionsEquiv (X := X) U).symm g ∈ (D + E).sections U := by
  rw [CartierDivisor.mem_sections_iff_exists]
  intro x hx
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨e, he, hreg⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
  refine ⟨f * e, hf.mul he, ?_⟩
  have hr := (CartierDivisor.mem_sections.mp hg) x hx f hf
  rw [LinearEquiv.apply_symm_apply] at hr ⊢
  have hmul := Subring.mul_mem (algebraMap (X.presheaf.stalk x) X.functionField).range hreg hr
  have heq : ((f * e : X.functionFieldˣ) : X.functionField) * g =
      (e : X.functionField) * ((f : X.functionField) * g) := by
    rw [Units.val_mul]
    ring
  rw [heq]
  exact hmul

variable [IsLocallyNoetherian X] [IsLocallyNoetherian T]

/-- Hartogs descends sections after adding an actual exceptional Cartier divisor.
Effectivity is not needed in this direction. -/
theorem mem_sections_of_exceptional_cartierPullback_on_open
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0)
    (D : CartierDivisor X) (U : X.Opens) [Nonempty U] [Nonempty (ρ ⁻¹ᵁ U)]
    (g : X.functionField)
    (hg : (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom g) ∈
        (cartierPullback ρ D + E).sections (ρ ⁻¹ᵁ U)) :
    (rationalFunctionsEquiv (X := X) U).symm g ∈ D.sections U := by
  rw [CartierDivisor.mem_sections]
  intro x hx f hf
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  apply mem_range_stalk_of_codimOne hnorm x (W ⊓ U) ⟨hxW, hx⟩
  intro ξ hξW hξ
  have hfξ : D.IsLocalEquationAt ξ f :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hW hξW.1
  obtain ⟨t, ht, hb⟩ := proper_birational_exists_normal_prime_lift hnorm ρ hρ ⟨ξ, hξ⟩
  have htξ : ρ (t : T) = ξ := ht
  subst htξ
  have htarget : Order.coheight (ρ (t : T)) = 1 := hξ
  have hft : D.IsLocalEquationAt (ρ (t : T)) f := hfξ
  have htu : (t : T) ∈ ρ ⁻¹ᵁ U := hξW.2
  let := hnorm (ρ (t : T))
  let := valuationRing_stalk_of_coheight_eq_one (ρ (t : T)) htarget
  have hdesc : ((f : X.functionField) * g) ∈
      (algebraMap (X.presheaf.stalk (ρ (t : T))) X.functionField).range := by
    apply mem_range_stalk_of_pullback ρ (t : T)
    obtain ⟨e, he⟩ := E.exists_isLocalEquationAt (t : T)
    let := hnormT (t : T)
    let := normal_codimensionOne_stalk_DVR t
    obtain ⟨v, hv⟩ := scheme_ord_zero_exists_stalk_unit t e
      (by rw [← cartierCoefficient_eq_ord he]; exact hE t htarget)
    have hr := (CartierDivisor.mem_sections.mp hg) (t : T) htu _
      ((cartierPullback_isLocalEquationAt ρ D (t : T) hft).mul he)
    rw [LinearEquiv.apply_symm_apply, Units.val_mul, Units.coe_map] at hr
    obtain ⟨a, ha⟩ := hr
    refine ⟨(v⁻¹ : (T.presheaf.stalk (t : T))ˣ) * a, ?_⟩
    rw [map_mul, map_units_inv, hv, ha, map_mul]
    field_simp
    exact mul_comm _ _
  exact hdesc

/-- On every nonempty target open, an effective exceptional divisor adds no sections. -/
theorem mem_sections_effective_exceptional_cartierPullback_iff_on_open
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (E : CartierDivisor T) (hEff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0)
    (D : CartierDivisor X) (U : X.Opens) [Nonempty U] [Nonempty (ρ ⁻¹ᵁ U)]
    (g : X.functionField) :
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom g) ∈
        (cartierPullback ρ D + E).sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := X) U).symm g ∈ D.sections U := by
  constructor
  · exact mem_sections_of_exceptional_cartierPullback_on_open hnorm hnormT ρ hρ E hE D U g
  · intro hg
    exact mem_sections_add_effective_on_open _ E hEff (ρ ⁻¹ᵁ U) _
      (cartierPullback_mem_sections_on_open ρ D U g hg)

end Sections

section Finrank

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]

attribute [local instance] cartierBaseGlobalAlgebra functionFieldBaseAlgebra
  cartierBaseSectionScalarTower functionFieldBaseScalarTower

variable (K) in
/-- Actual global section subspaces agree after adding an effective exceptional divisor. -/
theorem cartierSectionSpace_effective_exceptional_cartierPullback
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (E : CartierDivisor T) (hEff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (D : CartierDivisor X) :
    cartierSectionSpace K (cartierPullback ρ D + E) =
      (cartierSectionSpace K D).map (dominantFunctionFieldAlgHom (K := K) ρ).toLinearMap := by
  have : Nonempty (ρ ⁻¹ᵁ (⊤ : X.Opens)) := ⟨⟨genericPoint T, trivial⟩⟩
  ext r
  constructor
  · intro hr
    obtain ⟨g, rfl⟩ := hρ.2 r
    refine ⟨g, (mem_cartierSectionSpace_iff D g).mpr ?_, rfl⟩
    apply (mem_sections_effective_exceptional_cartierPullback_iff_on_open
      hnorm hnormT ρ hρ E hEff hE D ⊤ g).mp
    exact (mem_cartierSectionSpace_iff _ _).mp hr
  · rintro ⟨g, hg, rfl⟩
    apply (mem_cartierSectionSpace_iff _ _).mpr
    exact (mem_sections_effective_exceptional_cartierPullback_iff_on_open
      hnorm hnormT ρ hρ E hEff hE D ⊤ g).mpr ((mem_cartierSectionSpace_iff D g).mp hg)

variable (K) in
/-- The corresponding h^0 equality uses actual sections, without a finite-dimensional input. -/
theorem finrank_sections_effective_exceptional_cartierPullback
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (E : CartierDivisor T) (hEff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (D : CartierDivisor X) :
    Module.finrank K Γ((cartierPullback ρ D + E).sheaf, ⊤) =
      Module.finrank K Γ(D.sheaf, ⊤) := by
  rw [← finrank_cartierSectionSpace K, ← finrank_cartierSectionSpace K,
    cartierSectionSpace_effective_exceptional_cartierPullback K hnorm hnormT ρ hρ E hEff hE D]
  exact (Submodule.equivMapOfInjective _
    (dominantFunctionFieldAlgHom (K := K) ρ).toRingHom.injective _).finrank_eq.symm

end Finrank

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalHartogs
public import MixedFujita.KltPairs
public import MixedFujita.CartierBigDefinition
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
Sections of pullbacks along proper birational morphisms to a normal variety (step 15). Let X be a
normal locally Noetherian integral scheme. At a codimension-one point ξ the local ring is a
Noetherian integrally closed local domain of dimension one, hence a valuation ring. Let ρ : T → X
be dominant and t a point over ξ. The stalk map at t is local, so a rational function g whose
pullback is regular at t is regular at ξ: otherwise g⁻¹ lies in the maximal ideal at ξ, its
pullback in the maximal ideal at t, and ρ*g · ρ*g⁻¹ = 1. A proper dominant morphism is surjective,
so a rational function g with ρ*g a section of ρ*D is a section of D at the codimension-one points
of X, hence everywhere by Hartogs; sections of D pull back to sections of ρ*D. For a birational ρ
the pullback identifies Γ(X, O(D)) with Γ(T, O(ρ*D)), and h^0(T, q ρ*L) = h^0(X, q L): the
identification used in Lemma 2 for klt pairs, with no valuative criterion and no coherence of
direct images.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section ValuationStalk

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- At a codimension-one point of a normal locally Noetherian integral scheme the local ring is a
valuation ring. -/
theorem valuationRing_stalk_of_coheight_eq_one (ξ : X)
    [IsIntegrallyClosed (X.presheaf.stalk ξ)] (hξ : Order.coheight ξ = 1) :
    ValuationRing (X.presheaf.stalk ξ) := by
  have hdim : ringKrullDim (X.presheaf.stalk ξ) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hξ, WithBot.coe_one]
  have hle : Ring.KrullDimLE 1 (X.presheaf.stalk ξ) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact_mod_cast le_rfl)
  have key : IsIntegrallyClosed (X.presheaf.stalk ξ) ∧ ∀ P : Ideal (X.presheaf.stalk ξ),
      P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
    ⟨inferInstance, fun P hP0 hP =>
      IsLocalRing.eq_maximalIdeal ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp hle) P hP0 hP)⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (X.presheaf.stalk ξ)).out 4 2).mp key

end ValuationStalk

section Domination

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- The function field map is compatible with the stalk maps. -/
theorem dominantFunctionFieldMap_algebraMap (ρ : T ⟶ X) [IsDominant ρ] (t : T)
    (a : X.presheaf.stalk (ρ t)) :
    (dominantFunctionFieldMap ρ).hom (algebraMap (X.presheaf.stalk (ρ t)) X.functionField a) =
      algebraMap (T.presheaf.stalk t) T.functionField (ρ.stalkMap t a) := by
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨ρ t, hV⟩⟩
  have : Nonempty (ρ ⁻¹ᵁ V) := ⟨⟨t, hV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField,
    dominantFunctionFieldMap_germ ρ V (ρ ⁻¹ᵁ V) le_rfl s, Scheme.Hom.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.Hom.appLE_eq_app]

/-- Let t be a point of T over a point of X whose local ring is a valuation ring. A rational
function on X whose pullback is regular at t is regular at ρ(t). -/
theorem mem_range_stalk_of_pullback (ρ : T ⟶ X) [IsDominant ρ] (t : T)
    [ValuationRing (X.presheaf.stalk (ρ t))] (g : X.functionField)
    (hg : (dominantFunctionFieldMap ρ).hom g ∈
      (algebraMap (T.presheaf.stalk t) T.functionField).range) :
    g ∈ (algebraMap (X.presheaf.stalk (ρ t)) X.functionField).range := by
  rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk (ρ t)) g with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, ha⟩
  by_cases hg0 : g = 0
  · exact ⟨0, by rw [map_zero, hg0]⟩
  by_cases hu : IsUnit a
  · refine ⟨((hu.unit⁻¹ : (X.presheaf.stalk (ρ t))ˣ) : X.presheaf.stalk (ρ t)), ?_⟩
    rw [map_units_inv, IsUnit.unit_spec, ha, inv_inv]
  · exfalso
    obtain ⟨b, hb⟩ := hg
    apply hu
    have hmul : b * ρ.stalkMap t a = 1 := by
      apply IsFractionRing.injective (T.presheaf.stalk t) T.functionField
      rw [map_mul, map_one, hb, ← dominantFunctionFieldMap_algebraMap, ha, ← map_mul,
        mul_inv_cancel₀ hg0, map_one]
    exact IsLocalHom.map_nonunit (f := (ρ.stalkMap t).hom) a (IsUnit.of_mul_eq_one_right b hmul)

omit [IsIntegral X] [IsIntegral T] in
/-- A proper dominant morphism is surjective. -/
theorem surjective_of_isProper_of_isDominant (ρ : T ⟶ X) [IsProper ρ] [IsDominant ρ] :
    Function.Surjective ρ := by
  intro x
  have h : x ∈ closure (Set.range ρ) := by
    rw [ρ.denseRange.closure_range]
    trivial
  rwa [ρ.isClosedMap.isClosed_range.closure_eq] at h

end Domination

section Sections

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

/-- Sections pull back to sections. -/
theorem cartierPullback_mem_sections (D : CartierDivisor X) (g : X.functionField)
    (hg : (rationalFunctionsEquiv (X := X) ⊤).symm g ∈ D.sections ⊤) :
    (rationalFunctionsEquiv (X := T) ⊤).symm ((dominantFunctionFieldMap ρ).hom g) ∈
      (cartierPullback ρ D).sections ⊤ := by
  rw [CartierDivisor.mem_sections_iff_exists]
  intro t _
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
  refine ⟨_, cartierPullback_isLocalEquationAt ρ D t hf, ?_⟩
  obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hg) (ρ t) (Opens.mem_top _) f hf
  refine ⟨ρ.stalkMap t a, ?_⟩
  rw [← dominantFunctionFieldMap_algebraMap, ha]
  simp only [LinearEquiv.apply_symm_apply, Units.coe_map, map_mul]
  rfl

variable [IsLocallyNoetherian X]

/-- Sections of ρ*D descend to sections of D, if X is normal and ρ hits every codimension-one
point. -/
theorem mem_sections_of_cartierPullback
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hsurj : ∀ ξ : X, Order.coheight ξ = 1 → ∃ t : T, ρ t = ξ) (D : CartierDivisor X)
    (g : X.functionField)
    (hg : (rationalFunctionsEquiv (X := T) ⊤).symm ((dominantFunctionFieldMap ρ).hom g) ∈
      (cartierPullback ρ D).sections ⊤) :
    (rationalFunctionsEquiv (X := X) ⊤).symm g ∈ D.sections ⊤ := by
  rw [CartierDivisor.mem_sections]
  intro x _ f hf
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  apply mem_range_stalk_of_codimOne hnorm x W hxW
  intro ξ hξW hξ
  have hfξ : D.IsLocalEquationAt ξ f :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hW hξW
  obtain ⟨t, rfl⟩ := hsurj ξ hξ
  have := hnorm (ρ t)
  have := valuationRing_stalk_of_coheight_eq_one (ρ t) hξ
  apply mem_range_stalk_of_pullback ρ t
  have h1 := (CartierDivisor.mem_sections.mp hg) t (Opens.mem_top t) _
    (cartierPullback_isLocalEquationAt ρ D t hfξ)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [map_mul]
  exact h1

end Sections

section Finrank

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra functionFieldBaseAlgebra
  cartierBaseSectionScalarTower

theorem functionFieldBaseScalarTower :
    IsScalarTower K Γ(X, ⊤) X.functionField :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] functionFieldBaseScalarTower

variable (K) in
/-- The global sections of D as a K-subspace of the function field. -/
noncomputable def cartierSectionSpace (D : CartierDivisor X) : Submodule K X.functionField :=
  LinearMap.range ((cartierSectionRational D).restrictScalars K)

theorem mem_cartierSectionSpace_iff (D : CartierDivisor X) (g : X.functionField) :
    g ∈ cartierSectionSpace K D ↔ (rationalFunctionsEquiv (X := X) ⊤).symm g ∈ D.sections ⊤ := by
  constructor
  · rintro ⟨s, rfl⟩
    change (rationalFunctionsEquiv (X := X) ⊤).symm (cartierSectionRational D s) ∈ D.sections ⊤
    rw [cartierSectionRational_apply, LinearEquiv.symm_apply_apply]
    exact D.sheafι_app_mem ⊤ s
  · intro h
    exact ⟨CartierDivisor.sectionMk _ h, cartierSectionRational_sectionMk D g h⟩

variable (K) in
theorem finrank_cartierSectionSpace (D : CartierDivisor X) :
    Module.finrank K (cartierSectionSpace K D) = Module.finrank K Γ(D.sheaf, ⊤) :=
  LinearMap.finrank_range_of_inj (cartierSectionRational_injective D)

variable (K) in
/-- For a proper birational ρ to a normal X, the sections of ρ*D are the pullbacks of the sections
of D. -/
theorem cartierSectionSpace_cartierPullback [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Surjective (dominantFunctionFieldAlgHom (K := K) ρ)) (D : CartierDivisor X) :
    cartierSectionSpace K (cartierPullback ρ D) =
      (cartierSectionSpace K D).map (dominantFunctionFieldAlgHom (K := K) ρ).toLinearMap := by
  ext r
  constructor
  · intro hr
    obtain ⟨g, rfl⟩ := hρ r
    refine ⟨g, (mem_cartierSectionSpace_iff D g).mpr ?_, rfl⟩
    exact mem_sections_of_cartierPullback ρ hnorm
      (fun ξ _ => surjective_of_isProper_of_isDominant ρ ξ) D g
      ((mem_cartierSectionSpace_iff _ _).mp hr)
  · rintro ⟨g, hg, rfl⟩
    exact (mem_cartierSectionSpace_iff _ _).mpr
      (cartierPullback_mem_sections ρ D g ((mem_cartierSectionSpace_iff D g).mp hg))

variable (K) in
/-- h^0(T, ρ*D) = h^0(X, D) for a proper birational ρ to a normal X. -/
theorem finrank_sections_cartierPullback [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Surjective (dominantFunctionFieldAlgHom (K := K) ρ)) (D : CartierDivisor X) :
    Module.finrank K Γ((cartierPullback ρ D).sheaf, ⊤) = Module.finrank K Γ(D.sheaf, ⊤) := by
  rw [← finrank_cartierSectionSpace K, ← finrank_cartierSectionSpace K,
    cartierSectionSpace_cartierPullback K hnorm ρ hρ D]
  exact (Submodule.equivMapOfInjective _
    (dominantFunctionFieldAlgHom (K := K) ρ).toRingHom.injective _).finrank_eq.symm

variable (K) in
/-- h^0(T, q ρ*L) = h^0(X, q L) for a proper birational ρ to a normal X. -/
theorem finrank_sections_nsmul_cartierPullback [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Surjective (dominantFunctionFieldAlgHom (K := K) ρ)) (L : CartierDivisor X)
    (q : ℕ) :
    Module.finrank K Γ((q • cartierPullback ρ L).sheaf, ⊤) =
      Module.finrank K Γ((q • L).sheaf, ⊤) := by
  rw [← cartierPullback_nsmul]
  exact finrank_sections_cartierPullback K hnorm ρ hρ (q • L)

end Finrank

end MixedFujita

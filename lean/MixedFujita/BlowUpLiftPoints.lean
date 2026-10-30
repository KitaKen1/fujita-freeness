/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeLifts
public import MixedFujita.BirationalComposition
public import MixedFujita.HironakaPrincipalizingRound
public import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp

/-!
Divisors of a blow-up on a model dominating it (step 12). Let π : B → X be a separated dominant
morphism of integral schemes which is an isomorphism over an open set containing the generic
point, ρ : T → X a proper birational morphism from an integral scheme and g : T → B a morphism
over X. Then g is dominant, proper and birational, and every point of B whose local ring is a
valuation ring is the image of a point of T at which g is an isomorphism on stalks.

This applies to the blow-up of an ideal sheaf whose support does not contain the generic point,
where g exists as soon as the inverse image of the ideal sheaf on T is invertible, and to the
last stage of a succession of blow-ups with centres over a closed set not containing the generic
point: such a succession is one blow-up, of an ideal sheaf supported in that closed set. Thus a
prime divisor with discrete valuation local ring on a tower of blow-ups appears, with the same
valuation, on every model principalizing that ideal sheaf: this is how the extracted divisor is
kept on the model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Abstract

variable {X T B : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral B]

/-- A morphism g with g ≫ π dominant is dominant, if π is dominant and an isomorphism over an
open set containing the generic point: g sends the generic point to the generic point. -/
theorem lift_isDominant_of_isIso_restrict (π : B ⟶ X) [IsDominant π] (U : X.Opens)
    (hU : genericPoint X ∈ U) (hiso : IsIso (π ∣_ U)) (ρ : T ⟶ X) [IsDominant ρ]
    (g : T ⟶ B) (hg : g ≫ π = ρ) : IsDominant g := by
  have h1 : π (g (genericPoint T)) = genericPoint X := by
    have h := Scheme.Hom.comp_apply g π (genericPoint T)
    rw [hg, dominant_map_genericPoint] at h
    exact h.symm
  have h2 : π (genericPoint B) = genericPoint X := dominant_map_genericPoint π
  have hβ : g (genericPoint T) ∈ π ⁻¹ᵁ U := by
    change π (g (genericPoint T)) ∈ U
    rw [h1]
    exact hU
  have hηB : genericPoint B ∈ π ⁻¹ᵁ U := by
    change π (genericPoint B) ∈ U
    rw [h2]
    exact hU
  have e1 : (π ∣_ U).homeomorph ⟨g (genericPoint T), hβ⟩ = ⟨genericPoint X, hU⟩ :=
    Subtype.ext ((morphismRestrict_base_coe π U ⟨g (genericPoint T), hβ⟩).trans h1)
  have e2 : (π ∣_ U).homeomorph ⟨genericPoint B, hηB⟩ = ⟨genericPoint X, hU⟩ :=
    Subtype.ext ((morphismRestrict_base_coe π U ⟨genericPoint B, hηB⟩).trans h2)
  have heq : g (genericPoint T) = genericPoint B :=
    congrArg Subtype.val ((π ∣_ U).homeomorph.injective (e1.trans e2.symm))
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  have hsub : ({genericPoint B} : Set B) ⊆ Set.range g := by
    rintro y rfl
    exact ⟨genericPoint T, heq⟩
  simpa only [(genericPoint_spec B).def] using closure_mono hsub

/-- A dominant morphism g with g ≫ π birational is birational. -/
theorem lift_functionFieldMap_surjective (π : B ⟶ X) [IsDominant π] (ρ : T ⟶ X) [IsDominant ρ]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (g : T ⟶ B) [IsDominant g]
    (hg : g ≫ π = ρ) : Function.Surjective (dominantFunctionFieldMap g).hom := by
  subst hg
  have hcomp := dominantFunctionFieldMap_comp π g
  have hs : Function.Surjective (dominantFunctionFieldMap π ≫ dominantFunctionFieldMap g).hom := by
    rw [← hcomp]
    exact hρ
  exact Function.Surjective.of_comp hs

/-- Every point of B whose local ring is a valuation ring is the image of a point of a proper
birational model T of X lifting to B, and the lift is an isomorphism on the stalks there. -/
theorem lift_exists_stalkMap_bijective_over (π : B ⟶ X) [IsSeparated π] [IsDominant π]
    (U : X.Opens) (hU : genericPoint X ∈ U) (hiso : IsIso (π ∣_ U)) (ρ : T ⟶ X) [IsProper ρ]
    [IsDominant ρ] (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (g : T ⟶ B)
    (hg : g ≫ π = ρ) (b : B) [ValuationRing (B.presheaf.stalk b)] :
    ∃ t : T, g t = b ∧ Function.Bijective (g.stalkMap t) := by
  have hgdom : IsDominant g := lift_isDominant_of_isIso_restrict π U hU hiso ρ g hg
  have hgsurj : Function.Surjective (dominantFunctionFieldMap g).hom :=
    lift_functionFieldMap_surjective π ρ hρ g hg
  have hgprop : IsProper g := by
    have : IsProper (g ≫ π) := by
      rw [hg]
      infer_instance
    exact IsProper.of_comp g π
  obtain ⟨t, rfl⟩ := surjective_of_isProper_of_isDominant g b
  exact ⟨t, rfl, stalkMap_bijective_of_birational_valuation_stalk g
    ⟨(dominantFunctionFieldMap g).hom.injective, hgsurj⟩ t⟩

end Abstract

section BlowUp

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

/-- A morphism to a blow-up lifting a dominant morphism is dominant, if the support of the centre
does not contain the generic point. -/
theorem blowUp_lift_isDominant (I : X.IdealSheafData) [IsIntegral I.blowUp]
    (hη : genericPoint X ∉ (I.support : Set X)) (ρ : T ⟶ X) [IsDominant ρ]
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ) : IsDominant g := by
  have hπdom : IsDominant I.blowUpπ := blowUp_isDominant_of_genericPoint_notMem_support I hη
  exact lift_isDominant_of_isIso_restrict I.blowUpπ I.support.compl hη
    (Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support I) ρ g hg

/-- Every point of a blow-up whose local ring is a valuation ring is the image of a point of a
proper birational model lifting to the blow-up, and the lift is an isomorphism on the stalks
there. -/
theorem blowUp_lift_exists_stalkMap_bijective_over [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.blowUp] (hη : genericPoint X ∉ (I.support : Set X))
    (ρ : T ⟶ X) [IsProper ρ] [IsDominant ρ]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom)
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ) (b : I.blowUp)
    [ValuationRing (I.blowUp.presheaf.stalk b)] :
    ∃ t : T, g t = b ∧ Function.Bijective (g.stalkMap t) := by
  have hπprop : IsProper I.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π I
  have hπdom : IsDominant I.blowUpπ := blowUp_isDominant_of_genericPoint_notMem_support I hη
  exact lift_exists_stalkMap_bijective_over I.blowUpπ I.support.compl hη
    (Scheme.IdealSheafData.blowUp.isIso_π_restrict_compl_support I) ρ hρ g hg b

/-- The point of the model over a codimension-one point of the blow-up with valuation local ring
has codimension one. -/
theorem blowUp_lift_exists_codimensionOne_over [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.blowUp] (hη : genericPoint X ∉ (I.support : Set X))
    (ρ : T ⟶ X) [IsProper ρ] [IsDominant ρ]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom)
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ) (b : I.blowUp)
    [ValuationRing (I.blowUp.presheaf.stalk b)] (hb : Order.coheight b = 1) :
    ∃ t : T, g t = b ∧ Function.Bijective (g.stalkMap t) ∧ Order.coheight t = 1 := by
  obtain ⟨t, ht, hbij⟩ := blowUp_lift_exists_stalkMap_bijective_over I hη ρ hρ g hg b
  refine ⟨t, ht, hbij, ?_⟩
  rw [coheight_eq_of_stalkMap_bijective g t hbij, ht, hb]

end BlowUp

section Sequence

variable {X T : Scheme.{u}}

/-- A succession of blow-ups of a Noetherian scheme with centres over a closed set is dominated
by every scheme over the base on which the inverse image of one ideal sheaf, supported in that
closed set, is invertible: the succession is the blow-up of that ideal sheaf. -/
theorem blowUpSequence_exists_ideal_lift [IsNoetherian X] (S : Scheme.BlowUpSequence X)
    (Z : Closeds X)
    (hZ : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set X)) :
    ∃ I : X.IdealSheafData, (I.support : Set X) ⊆ (Z : Set X) ∧
      ∀ {T : Scheme.{u}} (ρ : T ⟶ X), (I.comap ρ).IsInvertible →
        ∃ g : T ⟶ S.last, g ≫ S.composite = ρ := by
  obtain ⟨I, hsupp, e, he, -⟩ := exists_blowUp_composite_iso S
  refine ⟨I, ?_, fun {T} ρ hinv => ?_⟩
  · rw [hsupp]
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z, hz, rfl⟩ := hi
    exact hZ i z hz
  · obtain ⟨g₀, hg₀⟩ := (Scheme.IdealSheafData.blowUp.isBlowUp I).exists_lift ρ hinv
    refine ⟨g₀ ≫ e.inv, ?_⟩
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hg₀]

variable [IsIntegral X] [IsIntegral T]

/-- Every point of the last stage of a succession of blow-ups, with centres over a closed set not
containing the generic point, whose local ring is a valuation ring is the image of a point of a
proper birational model lifting to the last stage, and the lift is an isomorphism on the stalks
there. -/
theorem blowUpSequence_lift_exists_stalkMap_bijective_over [IsLocallyNoetherian X]
    (S : Scheme.BlowUpSequence X) [IsIntegral S.last] (Z : Closeds X)
    (hZ : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set X))
    (hZη : genericPoint X ∉ (Z : Set X)) (ρ : T ⟶ X) [IsProper ρ] [IsDominant ρ]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (g : T ⟶ S.last)
    (hg : g ≫ S.composite = ρ) (b : S.last) [ValuationRing (S.last.presheaf.stalk b)] :
    ∃ t : T, g t = b ∧ Function.Bijective (g.stalkMap t) := by
  have hπprop : IsProper S.composite := S.isProper_composite
  have hπdom : IsDominant S.composite := blowUpSequence_isDominant_of_centers_over S Z hZ hZη
  have hiso : IsIso (S.composite ∣_ Z.compl) :=
    Hironaka.Sequence.isIso_composite_restrict_of_centers_disjoint S Z.compl fun i =>
      Set.disjoint_left.mpr fun z hz hzU => hzU (hZ i z hz)
  exact lift_exists_stalkMap_bijective_over S.composite Z.compl hZη hiso ρ hρ g hg b

/-- The point of the model over a codimension-one point of the last stage with valuation local
ring has codimension one. -/
theorem blowUpSequence_lift_exists_codimensionOne_over [IsLocallyNoetherian X]
    (S : Scheme.BlowUpSequence X) [IsIntegral S.last] (Z : Closeds X)
    (hZ : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set X))
    (hZη : genericPoint X ∉ (Z : Set X)) (ρ : T ⟶ X) [IsProper ρ] [IsDominant ρ]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (g : T ⟶ S.last)
    (hg : g ≫ S.composite = ρ) (b : S.last) [ValuationRing (S.last.presheaf.stalk b)]
    (hb : Order.coheight b = 1) :
    ∃ t : T, g t = b ∧ Function.Bijective (g.stalkMap t) ∧ Order.coheight t = 1 := by
  obtain ⟨t, ht, hbij⟩ :=
    blowUpSequence_lift_exists_stalkMap_bijective_over S Z hZ hZη ρ hρ g hg b
  refine ⟨t, ht, hbij, ?_⟩
  rw [coheight_eq_of_stalkMap_bijective g t hbij, ht, hb]

end Sequence

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveCenterGenerators
public import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp

/-!
Blow-ups of projective schemes are projective over the base field. Let X be an integral closed
subscheme of projective space over a field. An integral blow-up of X along any ideal sheaf is a
closed subscheme of a projective space over the same field: the coordinate atlas of X and
compatible generators of the centre give an atlas of ratios on the blow-up. A finite succession
of blow-ups of a Noetherian scheme is one blow-up up to isomorphism, by the pinned resolution
library, so the last stage of such a succession over X, when integral, is also a closed
subscheme of projective space over the field. An integral scheme with a closed immersion into
projective space over the field carries a very ample Cartier divisor, the hyperplane divisor of
a coordinate not vanishing at the generic point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- An integral blow-up of an integral closed subscheme of projective space over a field is a
closed subscheme of a projective space over that field. -/
theorem exists_closedImmersion_blowUp_of_projective [IsLocallyNoetherian X]
    (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
    (I : X.IdealSheafData) [IsIntegral (blowUp I)] :
    ∃ (M : ℕ) (e' : blowUp I ⟶ polynomialProjectiveScheme M K) (_ : IsClosedImmersion e'),
      e' ≫ polynomialProjectiveToBase M K = blowUpπ I ≫ X ↘ Spec (CommRingCat.of K) := by
  have hbase : IsProper (polynomialProjectiveToBase n K) := polynomialProjectiveToBase_isProper n K
  have hprop : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  obtain ⟨d, m, g, hg, hgc⟩ := exists_projective_ideal_atlas_generators e I
  exact ⟨n * m, exists_closedImmersion_blowUp_of_atlas I (projectiveAtlasOpen e)
    (projectiveAtlasRatio e) g (iSup_projectiveAtlasOpen e) (projectiveAtlasRatio_self e)
    (basicOpen_projectiveAtlasRatio_le e) (projectiveAtlasRatio_cocycle e)
    (projectiveAtlasRatio_generate e he) d hg hgc⟩

/-- The last stage of a finite succession of blow-ups of an integral closed subscheme of
projective space over a field, when integral, is a closed subscheme of a projective space over
that field. -/
theorem blowUpSequence_exists_closedImmersion [IsNoetherian X]
    (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
    (S : Scheme.BlowUpSequence X) [IsIntegral S.last] :
    ∃ (M : ℕ) (e' : S.last ⟶ polynomialProjectiveScheme M K) (_ : IsClosedImmersion e'),
      e' ≫ polynomialProjectiveToBase M K = S.composite ≫ X ↘ Spec (CommRingCat.of K) := by
  obtain ⟨J, -, φ, hφ, -⟩ := exists_blowUp_composite_iso S
  have hne : Nonempty (blowUp J) := ⟨φ.hom (Classical.arbitrary S.last)⟩
  have hint : IsIntegral (blowUp J) := isIntegral_of_isOpenImmersion φ.inv
  obtain ⟨M, e', he', hover⟩ := exists_closedImmersion_blowUp_of_projective e he J
  refine ⟨M, φ.hom ≫ e', inferInstance, ?_⟩
  rw [Category.assoc, hover, ← Category.assoc, hφ]

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] in
/-- Inserting an identity in a composite of three morphisms. -/
theorem comp_id_comp_assoc_eq {C : Type*} [Category C] {A B D E : C} (f : A ⟶ B) (g : B ⟶ D)
    (h : D ⟶ E) : (f ≫ g) ≫ h = f ≫ (𝟙 B ≫ g) ≫ h := by
  rw [Category.id_comp, Category.assoc]

/-- The two-step form used for the simple normal crossing model: one blow-up followed by a
succession of blow-ups of the result. -/
theorem blowUpSequence_two_step_exists_closedImmersion [IsNoetherian X]
    (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
    (D₀ : X.IdealSheafData)
    (S₂ : Scheme.BlowUpSequence
      (Scheme.BlowUpSequence.cons X D₀ (Scheme.BlowUpSequence.nil D₀.blowUp)).last)
    [IsIntegral S₂.last] :
    ∃ (M : ℕ) (e' : S₂.last ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
      e' ≫ polynomialProjectiveToBase M K =
        S₂.composite ≫
          (Scheme.BlowUpSequence.cons X D₀ (Scheme.BlowUpSequence.nil D₀.blowUp)).composite ≫
            X ↘ Spec (CommRingCat.of K) := by
  have hint : IsIntegral (Scheme.BlowUpSequence.cons X D₀ S₂).last := ‹IsIntegral S₂.last›
  obtain ⟨M, e', he', hover⟩ :=
    blowUpSequence_exists_closedImmersion e he (Scheme.BlowUpSequence.cons X D₀ S₂)
  refine ⟨M, e', he', hover.trans ?_⟩
  exact comp_id_comp_assoc_eq S₂.composite D₀.blowUpπ (X ↘ Spec (CommRingCat.of K))

/-- The two-step form with the first step given by an equation, as it occurs in the construction
of the simple normal crossing model. -/
theorem blowUpSequence_two_step_exists_closedImmersion_of_eq [IsNoetherian X]
    (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
    (D₀ : X.IdealSheafData) (S₁ : Scheme.BlowUpSequence X)
    (hS₁ : S₁ = Scheme.BlowUpSequence.cons X D₀ (Scheme.BlowUpSequence.nil D₀.blowUp))
    (S₂ : Scheme.BlowUpSequence S₁.last) [IsIntegral S₂.last] :
    ∃ (M : ℕ) (e' : S₂.last ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
      e' ≫ polynomialProjectiveToBase M K =
        S₂.composite ≫ S₁.composite ≫ X ↘ Spec (CommRingCat.of K) := by
  subst hS₁
  exact blowUpSequence_two_step_exists_closedImmersion e he D₀ S₂

/-- An integral scheme with a closed immersion into projective space over a field carries a very
ample Cartier divisor: the hyperplane divisor of a coordinate not vanishing at the generic
point. -/
theorem exists_cartierIsVeryAmpleProj_of_closedImmersion {T : Scheme.{u}} [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))] {M : ℕ} (e : T ⟶ polynomialProjectiveScheme M K)
    [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K)) :
    ∃ J : CartierDivisor T, CartierIsVeryAmpleProj K J := by
  obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart M K (e (genericPoint T))
  have hggen : MvPolynomial.X i ∉ (e (genericPoint T)).asHomogeneousIdeal := hi
  refine ⟨projectiveHyperplaneCartier e (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i)
    hggen, M, e, inferInstance, he, MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i, hggen,
    1, ?_⟩
  rw [principalCartierDivisor_one, add_zero]

end MixedFujita

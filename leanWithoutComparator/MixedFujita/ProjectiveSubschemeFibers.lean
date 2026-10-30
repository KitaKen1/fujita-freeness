/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveBaseChange

/-!
Closed subschemes defined by the homogeneous parameter ideal have actual
fibers over the coefficient Spec: the monomial closed subscheme at zero
and the original closed subscheme at one. Both categorical projections
and the ambient closed immersions are preserved. No flatness of this
closed-subscheme family or lct semicontinuity is asserted.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem projectiveIdealSheafScalarSubscheme_baseChange {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c)
    (I : (polynomialProjectiveScheme n R).IdealSheafData) :
    ∃ (m : (I.comap (polynomialScalarProjectiveMap c hc)).subscheme ⟶ I.subscheme)
      (e : (I.comap (polynomialScalarProjectiveMap c hc)).subscheme ≅
        pullback (I.subschemeι ≫ polynomialProjectiveToBase n R)
          (Spec.map (CommRingCat.ofHom c))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        (I.comap (polynomialScalarProjectiveMap c hc)).subschemeι ≫
          polynomialProjectiveToBase n S ∧
      m ≫ I.subschemeι =
        (I.comap (polynomialScalarProjectiveMap c hc)).subschemeι ≫
          polynomialScalarProjectiveMap c hc := by
  let J := I.comap (polynomialScalarProjectiveMap c hc)
  let m := Scheme.IdealSheafData.subschemeMap J I (polynomialScalarProjectiveMap c hc)
    (I.le_map_comap (polynomialScalarProjectiveMap c hc))
  have h : IsPullback J.subschemeι m (polynomialScalarProjectiveMap c hc) I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [m]) (by simp [J])
  have H := h.flip.paste_vert (polynomialScalarProjectiveMap_isPullback c hc)
  exact ⟨m, H.isoPullback, H.isoPullback_hom_fst, H.isoPullback_hom_snd,
    by simpa only [J] using h.w.symm⟩

theorem homogeneousParameterProjectiveZeroSubscheme_fiber {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    ∃ (m : (homogeneousProjectiveMonomialIdealSheaf I p d
          (homogeneous_support_degree I p f d hf hp)).subscheme ⟶
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subscheme)
      (e : (homogeneousProjectiveMonomialIdealSheaf I p d
          (homogeneous_support_degree I p f d hf hp)).subscheme ≅
        pullback
          ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι ≫
            polynomialProjectiveToBase n (Polynomial K))
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        (homogeneousProjectiveMonomialIdealSheaf I p d
          (homogeneous_support_degree I p f d hf hp)).subschemeι ≫ polynomialProjectiveToBase n K ∧
      m ≫ (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι =
        (homogeneousProjectiveMonomialIdealSheaf I p d
          (homogeneous_support_degree I p f d hf hp)).subschemeι ≫
          polynomialParameterProjectiveEval (0 : K) := by
  rw [← homogeneousParameterProjectiveIdealSheaf_at_zero I w p f d hf hp hw]
  exact projectiveIdealSheafScalarSubscheme_baseChange (Polynomial.evalRingHom (0 : K))
    (fun c => ⟨Polynomial.C c, by simp⟩) _

theorem homogeneousParameterProjectiveOneSubscheme_fiber {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    ∃ (m : (homogeneousProjectiveIdealSheaf I f d hf).subscheme ⟶
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subscheme)
      (e : (homogeneousProjectiveIdealSheaf I f d hf).subscheme ≅
        pullback
          ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι ≫
            polynomialProjectiveToBase n (Polynomial K))
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (1 : K))))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        (homogeneousProjectiveIdealSheaf I f d hf).subschemeι ≫ polynomialProjectiveToBase n K ∧
      m ≫ (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι =
        (homogeneousProjectiveIdealSheaf I f d hf).subschemeι ≫
          polynomialParameterProjectiveEval (1 : K) := by
  rw [← homogeneousParameterProjectiveIdealSheaf_at_one I w p f d hf]
  exact projectiveIdealSheafScalarSubscheme_baseChange (Polynomial.evalRingHom (1 : K))
    (fun c => ⟨Polynomial.C c, by simp⟩) _

end MixedFujita

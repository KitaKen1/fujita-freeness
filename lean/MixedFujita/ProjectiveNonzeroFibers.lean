/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveDiagonalIdealSheaves

/-!
Every nonzero parameter fiber is isomorphic to the original closed subscheme
over the coefficient field. The actual categorical fiber isomorphism
preserves both projections and its ambient immersion, with the inverse
diagonal coordinate transformation. No flatness or lct theorem is asserted.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem subschemeIso_inverse_ambient {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (J : Y.IdealSheafData) (f : X ≅ Y) (e : I.subscheme ≅ J.subscheme)
    (he : e.hom ≫ J.subschemeι = I.subschemeι ≫ f.hom) :
    e.inv ≫ I.subschemeι = J.subschemeι ≫ f.inv := by
  apply (cancel_epi e.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {n : ℕ} {K ι : Type u} [Field K]

theorem homogeneousParameterProjectiveNonzeroSubscheme_iso
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    ∃ e : ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
        (polynomialParameterProjectiveEval t)).subscheme ≅
        (homogeneousProjectiveIdealSheaf I f d hf).subscheme,
      e.hom ≫ (homogeneousProjectiveIdealSheaf I f d hf).subschemeι =
        ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
          (polynomialParameterProjectiveEval t)).subschemeι ≫
            (polynomialDiagonalProjectiveIso w ht).hom := by
  rw [homogeneousParameterProjectiveIdealSheaf_nonzero I w p f d hf ht hw]
  exact idealSheaf_comap_iso_subscheme _ (polynomialDiagonalProjectiveIso w ht)

theorem homogeneousParameterProjectiveNonzeroSubscheme_fiber
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    ∃ (m : (homogeneousProjectiveIdealSheaf I f d hf).subscheme ⟶
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subscheme)
      (e : (homogeneousProjectiveIdealSheaf I f d hf).subscheme ≅
        pullback
          ((homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι ≫
            polynomialProjectiveToBase n (Polynomial K))
          (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t)))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        (homogeneousProjectiveIdealSheaf I f d hf).subschemeι ≫ polynomialProjectiveToBase n K ∧
      m ≫ (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι =
        (homogeneousProjectiveIdealSheaf I f d hf).subschemeι ≫
          (polynomialDiagonalProjectiveIso w ht).inv ≫ polynomialParameterProjectiveEval t := by
  let F := homogeneousParameterProjectiveIdealSheaf I w p f d hf
  let O := homogeneousProjectiveIdealSheaf I f d hf
  let J := F.comap (polynomialParameterProjectiveEval t)
  obtain ⟨mb, eb, hbf, hbs, hbi⟩ :=
    projectiveIdealSheafScalarSubscheme_baseChange (Polynomial.evalRingHom t)
      (fun c => ⟨Polynomial.C c, by simp⟩) F
  change eb.hom ≫ pullback.snd _ _ = J.subschemeι ≫ polynomialProjectiveToBase n K at hbs
  change mb ≫ F.subschemeι = J.subschemeι ≫ polynomialParameterProjectiveEval t at hbi
  obtain ⟨ed, hdi⟩ := homogeneousParameterProjectiveNonzeroSubscheme_iso I w p f d hf ht hw
  have hdinv : ed.inv ≫ J.subschemeι = O.subschemeι ≫ (polynomialDiagonalProjectiveIso w ht).inv :=
    subschemeIso_inverse_ambient J O (polynomialDiagonalProjectiveIso w ht) ed hdi
  refine ⟨ed.inv ≫ mb, ed.symm ≪≫ eb, ?_, ?_, ?_⟩
  · change (ed.inv ≫ eb.hom) ≫ pullback.fst
      (F.subschemeι ≫ polynomialProjectiveToBase n (Polynomial K))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))) = ed.inv ≫ mb
    rw [Category.assoc, hbf]
  · change ed.inv ≫ (eb.hom ≫ pullback.snd _ _) = O.subschemeι ≫ polynomialProjectiveToBase n K
    rw [hbs, ← Category.assoc, hdinv, Category.assoc]
    change O.subschemeι ≫
      (polynomialDiagonalProjectiveMap w (inv_ne_zero ht) ≫ polynomialProjectiveToBase n K) = _
    rw [polynomialDiagonalProjectiveMap_toBase]
  · change (ed.inv ≫ mb) ≫ F.subschemeι = O.subschemeι ≫
      (polynomialDiagonalProjectiveIso w ht).inv ≫ polynomialParameterProjectiveEval t
    rw [Category.assoc, hbi, ← Category.assoc, hdinv, Category.assoc]

end MixedFujita

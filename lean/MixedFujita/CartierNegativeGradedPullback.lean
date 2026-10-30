/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.CartierCutEuler

/-!
Two actual Cartier representations of pulled-back line bundles construct the
representations of O(D-jJ) for every j. Negative sheaves are identified by
cancelling an actual Cartier tensor equivalence, without constructing divisor
pullback as a CartierDivisor object or assuming a representation in each degree.
Isomorphic Cartier sheaves similarly give the negative-twist comparisons used
by finite flags. A pointed flag and its fixed cut class are not constructed.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def cartierSheafTensorInverseIso (D : CartierDivisor X) :
    D.sheaf ⊗ (-D).sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  cartierTensorSheafIso D (-D) ≪≫
    eqToIso (congrArg CartierDivisor.sheaf (add_neg_cancel D)) ≪≫ cartierZeroSheafIso X

noncomputable def cartierNegativeSheafIsoOfIso
    (D E : CartierDivisor X) (e : D.sheaf ≅ E.sheaf) :
    (-D).sheaf ≅ (-E).sheaf :=
  (cartierTwistFunctor D).preimageIso
    (cartierSheafTensorInverseIso D ≪≫
      (tensorIso e (Iso.refl (-E).sheaf) ≪≫ cartierSheafTensorInverseIso E).symm)

noncomputable def cartierSubSheafIsoOfIsos
    (D E A B : CartierDivisor X) (a : D.sheaf ≅ A.sheaf) (b : E.sheaf ≅ B.sheaf) :
    (D - E).sheaf ≅ (A - B).sheaf :=
  (cartierCutTensorSourceIso D E).symm ≪≫
    tensorIso a (cartierNegativeSheafIsoOfIso E B b) ≪≫ cartierCutTensorSourceIso A B

noncomputable def cartierPullbackNegativeIso
    (D : CartierDivisor X) (φ : Y ⟶ X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) :
    (Scheme.Modules.pullback φ).obj (-D).sheaf ≅ (-A).sheaf :=
  (cartierTwistFunctor A).preimageIso
    (tensorIso a.symm (Iso.refl ((Scheme.Modules.pullback φ).obj (-D).sheaf)) ≪≫
      cartierPullbackTensorCancelIso (-D) D φ (add_neg_cancel D) ≪≫
        (cartierSheafTensorInverseIso A).symm)

noncomputable def cartierPullbackSubIso
    (D E : CartierDivisor X) (φ : Y ⟶ X) (A B : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf)
    (b : (Scheme.Modules.pullback φ).obj E.sheaf ≅ B.sheaf) :
    (Scheme.Modules.pullback φ).obj (D - E).sheaf ≅ (A - B).sheaf :=
  (Scheme.Modules.pullback φ).mapIso (cartierCutTensorSourceIso D E).symm ≪≫
    cartierPullbackTensorIso D φ (-E).sheaf ≪≫
      tensorIso a (cartierPullbackNegativeIso E φ B b) ≪≫ cartierCutTensorSourceIso A B

noncomputable def cartierPullbackNegativeGradedIso
    (D J : CartierDivisor X) (φ : Y ⟶ X) (A B : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf)
    (b : (Scheme.Modules.pullback φ).obj J.sheaf ≅ B.sheaf) (j : ℕ) :
    (Scheme.Modules.pullback φ).obj (D - j • J).sheaf ≅ (A - j • B).sheaf :=
  cartierPullbackSubIso D (j • J) φ A (j • B) a (cartierPullbackGradedIso J φ B b j)

noncomputable def cartierNegativeGradedShiftIso
    (A B E : CartierDivisor X) (e : E.sheaf ≅ B.sheaf) (j : ℕ) :
    (A - j • B - E).sheaf ≅ (A - (j + 1) • B).sheaf :=
  cartierSubSheafIsoOfIsos (A - j • B) E (A - j • B) B (Iso.refl _) e ≪≫
    eqToIso (congrArg CartierDivisor.sheaf (by rw [succ_nsmul, sub_add_eq_sub_sub]))

theorem cartierPullback_exists_fixed_all_negative_grades
    (D J : CartierDivisor X) (φ : Y ⟶ X) :
    ∃ A B : CartierDivisor Y, ∀ j : ℕ,
      Nonempty ((Scheme.Modules.pullback φ).obj (D - j • J).sheaf ≅ (A - j • B).sheaf) := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  obtain ⟨B, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor J φ
  exact ⟨A, B, fun j ↦ ⟨cartierPullbackNegativeGradedIso D J φ A B a b j⟩⟩

end MixedFujita

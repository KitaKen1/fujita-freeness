/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierTwistExactness
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
An actual Cartier projection-formula natural isomorphism is constructed for
every scheme morphism to an integral scheme. The target of pullback may be
nonintegral. The pulled-back Cartier sheaf and its pulled-back inverse supply
actual tensor equivalences. The proved canonical pullback tensor comparison
identifies the left adjoints; uniqueness of right adjoints supplies the
projection isomorphism, with its adjunction unit/counit compatibility proved.
For an actual ideal-sheaf subscheme, the twisted pushforward unit is thereby
identified with the pushforward of the actual pulled-back Cartier sheaf.
Closed-immersion cohomology comparison and curve existence are not asserted.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}} [IsIntegral X]

noncomputable def cartierPullbackTwistFunctor (D : CartierDivisor X) (φ : Y ⟶ X) :
    Y.Modules ⥤ Y.Modules := tensorLeft ((Scheme.Modules.pullback φ).obj D.sheaf)

noncomputable def cartierPullbackTensorCancelIso
    (D E : CartierDivisor X) (φ : Y ⟶ X) (h : E + D = 0) :
    (Scheme.Modules.pullback φ).obj E.sheaf ⊗ (Scheme.Modules.pullback φ).obj D.sheaf ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (cartierPullbackTensorIso E φ D.sheaf).symm ≪≫
    (Scheme.Modules.pullback φ).mapIso
      (cartierTensorSheafIso E D ≪≫ eqToIso (congrArg CartierDivisor.sheaf h) ≪≫
        cartierZeroSheafIso X) ≪≫ Scheme.Modules.pullbackObjUnitIso φ

noncomputable def cartierPullbackTwistCancelIso
    (D E : CartierDivisor X) (φ : Y ⟶ X) (h : E + D = 0) :
    cartierPullbackTwistFunctor D φ ⋙ cartierPullbackTwistFunctor E φ ≅ 𝟭 Y.Modules :=
  (tensorLeftTensor ((Scheme.Modules.pullback φ).obj E.sheaf)
    ((Scheme.Modules.pullback φ).obj D.sheaf)).symm ≪≫
    (tensoringLeft Y.Modules).mapIso (cartierPullbackTensorCancelIso D E φ h) ≪≫
      leftUnitorNatIso Y.Modules

noncomputable def cartierPullbackTwistEquivalence (D : CartierDivisor X) (φ : Y ⟶ X) :
    Y.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (cartierPullbackTwistFunctor D φ)
    (cartierPullbackTwistFunctor (-D) φ)
    (cartierPullbackTwistCancelIso D (-D) φ (neg_add_cancel D)).symm
    (cartierPullbackTwistCancelIso (-D) D φ (add_neg_cancel D))

noncomputable def cartierTwistPullbackNatIso (D : CartierDivisor X) (φ : Y ⟶ X) :
    cartierTwistFunctor D ⋙ Scheme.Modules.pullback φ ≅
      Scheme.Modules.pullback φ ⋙ cartierPullbackTwistFunctor D φ :=
  NatIso.ofComponents (fun M ↦ cartierPullbackTensorIso D φ M) fun {M N} f ↦ by
    exact (Functor.OplaxMonoidal.δ_natural_right (Scheme.Modules.pullback φ) D.sheaf f).symm

noncomputable def cartierProjectionFormulaLeftAdjunction
    (D : CartierDivisor X) (φ : Y ⟶ X) :
    cartierTwistFunctor (-D) ⋙ Scheme.Modules.pullback φ ⊣
      Scheme.Modules.pushforward φ ⋙ cartierTwistFunctor D :=
  (cartierTwistEquivalence D).symm.toAdjunction.comp
    (Scheme.Modules.pullbackPushforwardAdjunction φ)

noncomputable def cartierProjectionFormulaRightAdjunction
    (D : CartierDivisor X) (φ : Y ⟶ X) :
    cartierTwistFunctor (-D) ⋙ Scheme.Modules.pullback φ ⊣
      cartierPullbackTwistFunctor D φ ⋙ Scheme.Modules.pushforward φ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction φ).comp
    (cartierPullbackTwistEquivalence D φ).symm.toAdjunction).ofNatIsoLeft
      (cartierTwistPullbackNatIso (-D) φ).symm

noncomputable def cartierProjectionFormulaNatIso (D : CartierDivisor X) (φ : Y ⟶ X) :
    Scheme.Modules.pushforward φ ⋙ cartierTwistFunctor D ≅
      cartierPullbackTwistFunctor D φ ⋙ Scheme.Modules.pushforward φ :=
  (cartierProjectionFormulaLeftAdjunction D φ).rightAdjointUniq
    (cartierProjectionFormulaRightAdjunction D φ)

noncomputable def cartierProjectionFormulaIso
    (D : CartierDivisor X) (φ : Y ⟶ X) (M : Y.Modules) :
    D.sheaf ⊗ (Scheme.Modules.pushforward φ).obj M ≅
      (Scheme.Modules.pushforward φ).obj ((Scheme.Modules.pullback φ).obj D.sheaf ⊗ M) :=
  (cartierProjectionFormulaNatIso D φ).app M

theorem cartierProjectionFormula_unit (D : CartierDivisor X) (φ : Y ⟶ X) (M : X.Modules) :
    (cartierProjectionFormulaLeftAdjunction D φ).unit.app M ≫
      (cartierProjectionFormulaNatIso D φ).hom.app
        (((cartierTwistFunctor (-D)).obj M) |> (Scheme.Modules.pullback φ).obj) =
      (cartierProjectionFormulaRightAdjunction D φ).unit.app M :=
  Adjunction.unit_rightAdjointUniq_hom_app _ _ M

theorem cartierProjectionFormula_counit (D : CartierDivisor X) (φ : Y ⟶ X) (M : Y.Modules) :
    (cartierTwistFunctor (-D) ⋙ Scheme.Modules.pullback φ).map
      ((cartierProjectionFormulaNatIso D φ).hom.app M) ≫
        (cartierProjectionFormulaRightAdjunction D φ).counit.app M =
          (cartierProjectionFormulaLeftAdjunction D φ).counit.app M :=
  Adjunction.rightAdjointUniq_hom_app_counit _ _ M

noncomputable def cartierIdealSubschemeTwistedPushforwardIso
    (D : CartierDivisor X) (I : X.IdealSheafData) :
    D.sheaf ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
      (SheafOfModules.unit I.subscheme.ringCatSheaf) ≅
    (Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj D.sheaf) :=
  cartierProjectionFormulaIso D I.subschemeι (SheafOfModules.unit I.subscheme.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforward I.subschemeι).mapIso
      (rightUnitor ((Scheme.Modules.pullback I.subschemeι).obj D.sheaf))

end MixedFujita

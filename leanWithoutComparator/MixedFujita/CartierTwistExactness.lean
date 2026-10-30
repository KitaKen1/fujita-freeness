/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafModuleFunctor
public import MixedFujita.CartierGradedPullback
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
Tensoring actual module sheaves with the sheaf of an actual Cartier divisor
is an equivalence, with inverse supplied by the negative divisor. This proves
preservation of short exact sequences, including the actual ideal-subscheme
quotient sequence. Euler additivity for the twisted sequence has explicit
finite-cohomology and upper-vanishing inputs. Its quotient is the actual
tensor with a pushforward; projection formula and closed-immersion cohomology
comparison, Koszul exactness and pointed curve existence are not asserted.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def cartierTwistFunctor (D : CartierDivisor X) : X.Modules ⥤ X.Modules :=
  tensorLeft D.sheaf

noncomputable def cartierTwistCancelIso (D E : CartierDivisor X) (h : E + D = 0) :
    cartierTwistFunctor D ⋙ cartierTwistFunctor E ≅ 𝟭 X.Modules :=
  (tensorLeftTensor E.sheaf D.sheaf).symm ≪≫
    (tensoringLeft X.Modules).mapIso
      (cartierTensorSheafIso E D ≪≫ eqToIso (congrArg CartierDivisor.sheaf h) ≪≫
        cartierZeroSheafIso X) ≪≫ leftUnitorNatIso X.Modules

noncomputable def cartierTwistEquivalence (D : CartierDivisor X) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (cartierTwistFunctor D) (cartierTwistFunctor (-D))
    (cartierTwistCancelIso D (-D) (neg_add_cancel D)).symm
    (cartierTwistCancelIso (-D) D (add_neg_cancel D))

instance cartierTwistFunctor_isEquivalence (D : CartierDivisor X) :
    (cartierTwistFunctor D).IsEquivalence :=
  inferInstanceAs (cartierTwistEquivalence D).functor.IsEquivalence

instance cartierTwistFunctor_preservesZeroMorphisms (D : CartierDivisor X) :
    (cartierTwistFunctor D).PreservesZeroMorphisms := by infer_instance

instance cartierTwistFunctor_preservesFiniteLimits (D : CartierDivisor X) :
    PreservesFiniteLimits (cartierTwistFunctor D) := by infer_instance

instance cartierTwistFunctor_preservesFiniteColimits (D : CartierDivisor X) :
    PreservesFiniteColimits (cartierTwistFunctor D) := by infer_instance

theorem cartierTwist_shortExact (D : CartierDivisor X) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) : (S.map (cartierTwistFunctor D)).ShortExact :=
  hS.map_of_exact (cartierTwistFunctor D)

noncomputable def cartierTwistedIdealQuotientSequence
    (D : CartierDivisor X) (I : X.IdealSheafData) : ShortComplex X.Modules :=
  (idealSheafDataModuleQuotientSequence I).map (cartierTwistFunctor D)

theorem cartierTwistedIdealQuotientSequence_shortExact
    (D : CartierDivisor X) (I : X.IdealSheafData) :
    (cartierTwistedIdealQuotientSequence D I).ShortExact :=
  cartierTwist_shortExact D (idealSheafDataModuleQuotientSequence_shortExact I)

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

theorem cartierTwistedIdealQuotient_eulerCharBelow_eq_sub
    (D : CartierDivisor X) (I : X.IdealSheafData) (n : ℕ)
    (hI : ∀ j < n, 0 < j → FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (D.sheaf ⊗ idealSheafDataModule I) j))
    (hO : ∀ j < n, FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (D.sheaf ⊗ SheafOfModules.unit X.ringCatSheaf) j))
    (hvan : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (D.sheaf ⊗ idealSheafDataModule I) n)) :
    Scheme.Modules.eulerCharBelow K X
      (D.sheaf ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) n =
      Scheme.Modules.eulerCharBelow K X (D.sheaf ⊗ SheafOfModules.unit X.ringCatSheaf) n -
        Scheme.Modules.eulerCharBelow K X (D.sheaf ⊗ idealSheafDataModule I) n := by
  have h := Scheme.Modules.eulerCharBelow_eq_add K
    (cartierTwistedIdealQuotientSequence_shortExact D I) n hI hO hvan
  change Scheme.Modules.eulerCharBelow K X
    (D.sheaf ⊗ SheafOfModules.unit X.ringCatSheaf) n =
      Scheme.Modules.eulerCharBelow K X (D.sheaf ⊗ idealSheafDataModule I) n +
        Scheme.Modules.eulerCharBelow K X
          (D.sheaf ⊗ (Scheme.Modules.pushforward I.subschemeι).obj
            (SheafOfModules.unit I.subscheme.ringCatSheaf)) n at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h.symm)

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierIdealSheaf
public import MixedFujita.CartierProjectionFormula

/-!
For an actual effective Cartier divisor E on an integral scheme, the actual
Cartier-twisted quotient sequence is transported to
O(D-E) -> O(D) -> i_* i^* O(D).
The maps, their zero composite and the comparison of short complexes are
constructed, and short exactness is proved. The resulting truncated Euler
difference has finite-cohomology and upper-vanishing inputs on the actual
ambient Cartier sheaves. Cohomology comparison with the cut scheme, pointed
smooth integral cuts and a general-dimensional uniform degree are not claimed.
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

noncomputable def cartierCutTensorSourceIso (D E : CartierDivisor X) :
    D.sheaf ⊗ (-E).sheaf ≅ (D - E).sheaf :=
  cartierTensorSheafIso D (-E) ≪≫
    eqToIso (congrArg CartierDivisor.sheaf (sub_eq_add_neg D E).symm)

noncomputable def cartierCutTwistedQuotient (D E : CartierDivisor X) (hE : E.IsEffective) :
    ShortComplex X.Modules :=
  (effectiveCartierQuotientShortComplex E hE).map (cartierTwistFunctor D)

noncomputable def cartierCutPushforwardIso
    (D E : CartierDivisor X) (hE : E.IsEffective) :
    (cartierCutTwistedQuotient D E hE).X₃ ≅
      (Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj D.sheaf) :=
  cartierIdealSubschemeTwistedPushforwardIso D (effectiveCartierIdealSheaf E hE)

noncomputable def cartierCutShortComplex (D E : CartierDivisor X) (hE : E.IsEffective) :
    ShortComplex X.Modules := by
  let S := cartierCutTwistedQuotient D E hE
  let e₁ := cartierCutTensorSourceIso D E
  let e₂ := rightUnitor D.sheaf
  let e₃ := cartierCutPushforwardIso D E hE
  exact ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero, zero_comp] using
      congrArg (fun q ↦ e₁.inv ≫ q ≫ e₃.hom) S.zero)

noncomputable def cartierCutShortComplexIso
    (D E : CartierDivisor X) (hE : E.IsEffective) :
    cartierCutTwistedQuotient D E hE ≅ cartierCutShortComplex D E hE :=
  ShortComplex.isoMk (cartierCutTensorSourceIso D E) (rightUnitor D.sheaf)
    (cartierCutPushforwardIso D E hE)
    (by simp only [cartierCutShortComplex, Iso.hom_inv_id_assoc])
    (by simp only [cartierCutShortComplex, Iso.hom_inv_id_assoc])

theorem cartierCutShortComplex_shortExact
    (D E : CartierDivisor X) (hE : E.IsEffective) :
    (cartierCutShortComplex D E hE).ShortExact :=
  ShortComplex.shortExact_of_iso (cartierCutShortComplexIso D E hE)
    (cartierTwist_shortExact D (effectiveCartierQuotientShortComplex_shortExact E hE))

theorem cartierCutShortComplex_first_map
    (D E : CartierDivisor X) (hE : E.IsEffective) :
    (cartierCutShortComplex D E hE).f =
      (cartierCutTensorSourceIso D E).inv ≫
        (cartierTwistFunctor D).map (negativeCartierToUnit X E hE) ≫
          (rightUnitor D.sheaf).hom := rfl

theorem cartierCutShortComplex_second_map
    (D E : CartierDivisor X) (hE : E.IsEffective) :
    (cartierCutShortComplex D E hE).g =
      (rightUnitor D.sheaf).inv ≫
        (cartierTwistFunctor D).map
          (schemeUnitToPushforwardUnit (effectiveCartierIdealSheaf E hE).subschemeι) ≫
            (cartierCutPushforwardIso D E hE).hom := rfl

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

theorem cartierCut_eulerCharBelow_eq_sub
    (D E : CartierDivisor X) (hE : E.IsEffective) (n : ℕ)
    (hDE : ∀ j < n, 0 < j → FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (D - E).sheaf j))
    (hD : ∀ j < n, FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology D.sheaf j))
    (hvan : Subsingleton
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (D - E).sheaf n)) :
    Scheme.Modules.eulerCharBelow K X
      ((Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj D.sheaf)) n =
      Scheme.Modules.eulerCharBelow K X D.sheaf n -
        Scheme.Modules.eulerCharBelow K X (D - E).sheaf n := by
  have h := Scheme.Modules.eulerCharBelow_eq_add K
    (cartierCutShortComplex_shortExact D E hE) n hDE hD hvan
  change Scheme.Modules.eulerCharBelow K X D.sheaf n =
    Scheme.Modules.eulerCharBelow K X (D - E).sheaf n +
      Scheme.Modules.eulerCharBelow K X
        ((Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
          ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj D.sheaf)) n at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h.symm)

end MixedFujita

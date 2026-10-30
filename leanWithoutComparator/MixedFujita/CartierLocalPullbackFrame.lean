/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierOpenCoefficient
public import MixedFujita.ModulePullbackRestriction

/-!
An actual Cartier equation on an open gives a trivialization on the actual
open subscheme. Pulling this frame back through the adjunction-compatible
restriction isomorphism gives an actual frame of the actual pulled-back
Cartier module on the preimage open. The local coefficient morphism and
the global pullback unit satisfy a proved commuting square; no such square
is an input. Identifying its component/germ with the intrinsic coefficient
of a chosen target Cartier representation, and deriving the unit relating
the two target frames, are still required before the curve transfer theorem
can drop its supplied coefficient-compatibility hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

noncomputable def cartierOpenRestrictFrameIso (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    D.sheaf.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app D.sheaf).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso (cartierOpenFrameIso D U f hf) ≪≫
      U.sheafOfModulesEquivOverUnit X.ringCatSheaf

noncomputable def cartierPullbackLocalFrameIso (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    ((Scheme.Modules.pullback φ).obj D.sheaf).restrict (φ ⁻¹ᵁ U).ι ≅
      SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf :=
  modulePullbackRestrictionIso φ U D.sheaf ≪≫
    modulePullbackFrameIso (φ ∣_ U) (cartierOpenRestrictFrameIso D U f hf)

theorem cartierPullbackLocalFrameIso_hom (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    (cartierPullbackLocalFrameIso D φ U f hf).hom =
      modulePullbackRestrictedCoefficientHom φ U (cartierOpenRestrictFrameIso D U f hf).hom := rfl

theorem cartierPullbackLocalFrameIso_adjoint (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    (Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app D.sheaf ≫
      (Scheme.Modules.pushforward φ).map
        ((Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι).unit.app
            ((Scheme.Modules.pullback φ).obj D.sheaf) ≫
          (Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι).map
            (cartierPullbackLocalFrameIso D φ U f hf).hom) ≫
      (modulePullbackRestrictionPushforwardIso φ U).hom.app
        (SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf) =
    (Scheme.Modules.restrictAdjunction U.ι).unit.app D.sheaf ≫
      (Scheme.Modules.pushforward U.ι).map (cartierOpenRestrictFrameIso D U f hf).hom ≫
      (Scheme.Modules.pushforward U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit (φ ∣_ U).toRingCatSheafHom) :=
  modulePullbackRestrictedCoefficientHom_adjoint φ U (cartierOpenRestrictFrameIso D U f hf).hom

theorem cartierPullback_exists_equation_frame (D : CartierDivisor X) (φ : Y ⟶ X) (y : Y) :
    ∃ (U : X.Opens) (hy : φ y ∈ U) (f : X.functionFieldˣ),
      haveI : Nonempty U := ⟨⟨φ y, hy⟩⟩
      ∃ _hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U,
        Nonempty (((Scheme.Modules.pullback φ).obj D.sheaf).restrict (φ ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((φ ⁻¹ᵁ U) : Scheme).ringCatSheaf) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  exact ⟨U, hy, f, hU, ⟨cartierPullbackLocalFrameIso D φ U f hU⟩⟩

end MixedFujita

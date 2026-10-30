/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CrepantRoundupDirectImageIso
public import MixedFujita.CanonicalImageIdealNonvanishing

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
variable {B B' : Scheme.{u}} (β : B' ⟶ B) {F : B.Modules} {F' : B'.Modules}

/-- The adjoint of the actual pushforward isomorphism is the genuine base
pullback comparison morphism. No base-change isomorphism is assumed. -/
noncomputable def changedRoundupBaseChangeMap
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') :
    (Scheme.Modules.pullback β).obj F ⟶ F' :=
  ((Scheme.Modules.pullbackPushforwardAdjunction β).homEquiv F F').symm e.hom

theorem changedRoundupBaseChangeMap_unit
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') :
    (Scheme.Modules.pullbackPushforwardAdjunction β).unit.app F ≫
      (Scheme.Modules.pushforward β).map (changedRoundupBaseChangeMap β e) = e.hom :=
  ((Scheme.Modules.pullbackPushforwardAdjunction β).homEquiv F F').apply_symm_apply e.hom

theorem changedRoundupBaseChangeMap_counit
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') :
    changedRoundupBaseChangeMap β e = (Scheme.Modules.pullback β).map e.hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction β).counit.app F' := rfl

theorem changedRoundupBaseChangeMap_ne_zero
    (e : F ≅ (Scheme.Modules.pushforward β).obj F') (hF : ¬ IsZero F) :
    changedRoundupBaseChangeMap β e ≠ 0 := by
  intro hzero
  have h := changedRoundupBaseChangeMap_unit β e
  have hezero : e.hom = 0 := by simpa only [hzero, Functor.map_zero, comp_zero] using h.symm
  apply hF
  rw [IsZero.iff_id_eq_zero]
  rw [← e.hom_inv_id, hezero, zero_comp]

theorem changedRoundupBaseChangeMap_ne_zero_of_effective
    {T : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (hE : E.IsEffective)
    (e : (Scheme.Modules.pushforward q).obj E.sheaf ≅ (Scheme.Modules.pushforward β).obj F') :
    changedRoundupBaseChangeMap β e ≠ 0 :=
  changedRoundupBaseChangeMap_ne_zero β e (effectiveCartier_direct_image_not_isZero q E hE)

end MixedFujita


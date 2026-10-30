/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPulledCoherentTwist
public import MixedFujita.ActualModuleEulerZero
public import MixedFujita.MixedForwardDifferenceLinearity
public import MixedFujita.CartierMixedEulerDifference

/-! 任意の連接層係数の実混合Euler差分と完全列加法性。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual pulled Cartier mixed Euler differences with any coherent-module
coefficient. The proper source may be nonintegral or nonreduced. -/
noncomputable def cartierPulledModuleMixedEulerDifference
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) (M : Y.Modules)
    (D : List (CartierDivisor X)) (E : CartierDivisor X) : ℤ :=
  mixedForwardDifference D (fun F : CartierDivisor X =>
    Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj M)) E


/-- Identity pullback and the unit coefficient recover the original mixed
Cartier Euler characteristic exactly; no numerical-dimension definition changes. -/
theorem cartierPulledModuleMixedEulerDifference_id_unit
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K (𝟙 X)
      (SheafOfModules.unit X.ringCatSheaf) D E = cartierMixedEulerDifference K D E := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (X ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F (𝟙 X)).obj (SheafOfModules.unit X.ringCatSheaf))) =
      fun F : CartierDivisor X => Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf := by
    funext F
    exact moduleEulerChar_congr K
      (tensorIso ((Scheme.Modules.pullbackId X).app F.sheaf)
        (Iso.refl (SheafOfModules.unit X.ringCatSheaf)) ≪≫ rightUnitor F.sheaf)
  unfold cartierPulledModuleMixedEulerDifference cartierMixedEulerDifference
  rw [heq]


/-- Actual mixed Euler differences with coherent coefficients are additive
on short exact sequences, with finiteness and exactness supplied internally. -/
theorem cartierPulledModuleMixedEulerDifference_of_shortExact
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p S.X₂ D E =
      cartierPulledModuleMixedEulerDifference K p S.X₁ D E +
        cartierPulledModuleMixedEulerDifference K p S.X₃ D E := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj S.X₂)) =
      (fun F : CartierDivisor X => Scheme.Modules.eulerChar
        (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj S.X₁)) +
      (fun F : CartierDivisor X => Scheme.Modules.eulerChar
        (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj S.X₃)) := by
    funext F
    let : ((S.map (cartierPullbackTwistFunctor F p)).X₁).IsCoherent := cartierPulledTensor_isCoherent F p S.X₁
    let : ((S.map (cartierPullbackTwistFunctor F p)).X₂).IsCoherent := cartierPulledTensor_isCoherent F p S.X₂
    let : ((S.map (cartierPullbackTwistFunctor F p)).X₃).IsCoherent := cartierPulledTensor_isCoherent F p S.X₃
    exact proper_moduleEulerChar_of_shortExact K (X := Y)
      (S := S.map (cartierPullbackTwistFunctor F p))
      (cartierPulledTensor_shortExact F p hS)
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq, mixedForwardDifference_add_functions]
  rfl


/-- A module whose actual sections all vanish contributes zero to every
mixed Euler difference. This is the zero-support gate for SGA devissage. -/
theorem cartierPulledModuleMixedEulerDifference_zero_sections
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules)
    (hM : ∀ (V : Y.Opens) (s : Γ(M, V)), s = 0)
    (D : List (CartierDivisor X)) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  have hid : 𝟙 M = 0 := Scheme.Modules.hom_ext _ _ fun V => by
    ext s
    exact (hM V _).trans (hM V _).symm
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj M)) =
      fun _ => (0 : ℤ) := by
    funext F
    have hid' : 𝟙 ((cartierPullbackTwistFunctor F p).obj M) = 0 := by
      have h := congrArg (cartierPullbackTwistFunctor F p).map hid
      exact ((cartierPullbackTwistFunctor F p).map_id M).symm.trans
        (h.trans ((cartierPullbackTwistFunctor F p).map_zero M M))
    exact moduleEulerChar_eq_zero_of_id_eq_zero K _ hid'
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq, mixedForwardDifference_zero_function]

end MixedFujita

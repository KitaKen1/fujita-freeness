/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDevissage
public import MixedFujita.ZeroDimensionalCartierFreeness
public import MixedFujita.SGALineBundleCartierRepresentation

/-! 非被約proper零次元源・任意連接係数の全非空混合Euler差分消滅。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On an integral zero-dimensional source every ambient Cartier line bundle
pulls back to the actual unit sheaf, using the proved Cartier/SGA dictionary. -/
noncomputable def zeroDimensional_integral_cartierPulledSheafIsoUnit
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (hdim : topologicalKrullDim Y = 0) (p : Y ⟶ X) (D : CartierDivisor X) :
    (Scheme.Modules.pullback p).obj D.sheaf ≅ SheafOfModules.unit Y.ringCatSheaf := by
  let L := (cartierSGALineBundle D).pullback p
  let H := sgaLineBundleCartierDivisor L
  exact (cartierPulledSheafSGAPowerOneIso D p).symm ≪≫ sgaLineBundleCartierIso L ≪≫
    eqToIso (congrArg CartierDivisor.sheaf (zeroDimensional_cartierDivisor_eq_zero hdim H)) ≪≫
      cartierZeroSheafIso Y


/-- The integral zero-dimensional support case has zero nonempty mixed
Euler differences for every coefficient module, without a finiteness input. -/
theorem zeroDimensional_integral_cartierPulledModuleMixedEulerDifference_vanishes
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y = 0) (p : Y ⟶ X) (M : Y.Modules)
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M (H :: D) E = 0 := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj M)) =
      fun _ => Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) M := by
    funext F
    exact moduleEulerChar_congr K
      (tensorIso (zeroDimensional_integral_cartierPulledSheafIsoUnit hdim p F) (Iso.refl M) ≪≫
        leftUnitor M)
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq, mixedForwardDifference_nonempty_const]


/-- Proper zero-dimensional schemes, including nonreduced or reducible
schemes, have zero nonempty pulled Cartier mixed Euler differences for EVERY
coherent coefficient module. SGA devissage supplies the nilpotent layers. -/
theorem properZeroDimensional_cartierPulledModuleMixedEulerDifference_vanishes
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y = 0) (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M (H :: D) E = 0 := by
  apply cartierPulledModuleMixedEulerDifference_vanish_of_pulled_integral_step K p (H :: D) E ?_ M
  intro Z _ _ _ i _ _ hsmall G hG
  have hle : topologicalKrullDim Z ≤ 0 :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim.le
  have hge : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
    let : Nonempty (IrreducibleCloseds Z) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
    exact Order.krullDim_nonneg
  exact zeroDimensional_integral_cartierPulledModuleMixedEulerDifference_vanishes
    K (le_antisymm hle hge) (i ≫ p) G D H E

end MixedFujita

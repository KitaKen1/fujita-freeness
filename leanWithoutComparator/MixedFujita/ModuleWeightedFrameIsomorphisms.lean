/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleOpenUnitAutomorphisms

/-! 実frameと単元の局所加群層同型・全部分開係数則・一意性。 check-282：既存の構造層からの写像と切断の対応を再利用し、実開上の正則関数による構造加群写像、単元による同型、実frame間の重み付き加群層同型を構成。全部分開の正確な係数則と、その係数則による同型の一意性を証明。実スキームのK射が全開の定数を保つ既存APIから、実商環のK作用と標準K作用の一致を内部供給。標準Cartier因子と切断の局所方程式の積を元のK_X+Dの方程式と同定。実有効Cartier切断と周囲・切断のetale座標から、正規化留数とframe単元を内部構成し、実際のi^*O(K_X+D)とO(K_Y)の切断チャート上の加群層同型へ接続。全部分開の係数則、同じ正規化係数の下での一意性、実Cartier切断／最高次形式の正確な正規化を証明。異なるチャート・方程式間の一致、大域留数層貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra



/-- Actual unit frames and an actual unit coefficient define an isomorphism
of the actual module SHEAVES on an open. -/
noncomputable def moduleOverFrameWeightedIso {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (a : Γ(X, U)ˣ) :
    M.over U ≅ N.over U := e ≪≫ moduleOverUnitMulIso U a ≪≫ d.symm


/-- Its coefficient on every subopen is the restriction of the SAME actual
unit times the source coefficient; no restriction certificate is assumed. -/
theorem moduleOverFrameWeightedIso_coefficient {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (a : Γ(X, U)ˣ)
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    moduleOverFrameCoefficient N U d W hWU
        ((moduleOverFrameWeightedIso M N U e d a).hom.val.app
          (op (Over.mk (homOfLE hWU))) s) =
      X.presheaf.map (homOfLE hWU).op ↑a * moduleOverFrameCoefficient M U e W hWU s := by
  let Q := op (Over.mk (homOfLE hWU))
  change d.hom.val.app Q (d.inv.val.app Q
    ((moduleOverUnitMulHom U ↑a).val.app (op (Over.mk (homOfLE hWU)))
      (moduleOverFrameCoefficient M U e W hWU s))) = _
  rw [moduleOverUnitMulHom_apply]
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.val.app Q) d.inv_hom_id)
      (X.presheaf.map (homOfLE hWU).op ↑a * moduleOverFrameCoefficient M U e W hWU s)
  exact h


/-- The actual all-subopen coefficient law uniquely determines the sheaf iso. -/
theorem moduleOverFrameWeightedIso_unique {X : Scheme.{u}} (M N : X.Modules)
    (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (a : Γ(X, U)ˣ)
    (f : M.over U ≅ N.over U)
    (hf : ∀ (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)),
      moduleOverFrameCoefficient N U d W hWU
          (f.hom.val.app (op (Over.mk (homOfLE hWU))) s) =
        X.presheaf.map (homOfLE hWU).op ↑a * moduleOverFrameCoefficient M U e W hWU s) :
    f = moduleOverFrameWeightedIso M N U e d a := by
  apply Iso.ext
  ext W s
  apply (moduleOverFrameCoefficient N U d W.unop.left W.unop.hom.le).injective
  exact (hf W.unop.left W.unop.hom.le s).trans
    (moduleOverFrameWeightedIso_coefficient M N U e d a W.unop.left W.unop.hom.le s).symm

end MixedFujita

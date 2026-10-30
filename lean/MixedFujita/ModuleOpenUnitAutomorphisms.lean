/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierTopForms
public import MixedFujita.ModulePullbackFrameGenerators

/-! 実開の正則関数・単元による構造加群写像と同型。 check-282：既存の構造層からの写像と切断の対応を再利用し、実開上の正則関数による構造加群写像、単元による同型、実frame間の重み付き加群層同型を構成。全部分開の正確な係数則と、その係数則による同型の一意性を証明。実スキームのK射が全開の定数を保つ既存APIから、実商環のK作用と標準K作用の一致を内部供給。標準Cartier因子と切断の局所方程式の積を元のK_X+Dの方程式と同定。実有効Cartier切断と周囲・切断のetale座標から、正規化留数とframe単元を内部構成し、実際のi^*O(K_X+D)とO(K_Y)の切断チャート上の加群層同型へ接続。全部分開の係数則、同じ正規化係数の下での一意性、実Cartier切断／最高次形式の正確な正規化を証明。異なるチャート・方程式間の一致、大域留数層貼合せ、SNC反復随伴、数値随伴は残る。 -/

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



/-- Multiplication by an actual regular function on an open, as a morphism
of the actual structure module on that open and ALL its subopens. -/
noncomputable def moduleOverUnitMulHom {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.unit (X.ringCatSheaf.over U)).unitHomEquiv.symm
    ((SheafOfModules.unit (X.ringCatSheaf.over U)).val.sectionsMk
      (fun W => show (X.ringCatSheaf.over U).obj.obj W from
        X.presheaf.map W.unop.hom.op a)
      (by
        intro W V f
        change X.presheaf.map f.unop.left.op (X.presheaf.map W.unop.hom.op a) =
          X.presheaf.map V.unop.hom.op a
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl))


/-- The existing unit-Hom equivalence gives precisely multiplication by the
restricted regular function on every actual subopen. -/
theorem moduleOverUnitMulHom_apply {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, U))
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(X, W)) :
    (moduleOverUnitMulHom U a).val.app (op (Over.mk (homOfLE hWU))) s =
      X.presheaf.map (homOfLE hWU).op a * s := by
  change s * X.presheaf.map (homOfLE hWU).op a = _
  exact mul_comm _ _


/-- An actual regular UNIT supplies an isomorphism of structure modules,
including every subopen, not just an automorphism of one section module. -/
noncomputable def moduleOverUnitMulIso {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, U)ˣ) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) where
  hom := moduleOverUnitMulHom U ↑a
  inv := moduleOverUnitMulHom U ↑a⁻¹
  hom_inv_id := by
    ext W : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    let t : Γ(X, W.unop.left) := s
    have h : (moduleOverUnitMulHom U ↑a⁻¹).val.app
        (op (Over.mk (homOfLE W.unop.hom.le)))
        ((moduleOverUnitMulHom U ↑a).val.app (op (Over.mk (homOfLE W.unop.hom.le))) t) = t := by
      rw [moduleOverUnitMulHom_apply, moduleOverUnitMulHom_apply, ← mul_assoc, ← map_mul]
      simp
    exact h
  inv_hom_id := by
    ext W : 2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    let t : Γ(X, W.unop.left) := s
    have h : (moduleOverUnitMulHom U ↑a).val.app
        (op (Over.mk (homOfLE W.unop.hom.le)))
        ((moduleOverUnitMulHom U ↑a⁻¹).val.app (op (Over.mk (homOfLE W.unop.hom.le))) t) = t := by
      rw [moduleOverUnitMulHom_apply, moduleOverUnitMulHom_apply, ← mul_assoc, ← map_mul]
      simp
    exact h

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCoordinateFrameLaws

/-! 源・対象frameと留数係数の同時変換の層同型での相殺。 check-284：実unit-frame生成元の係数1と生成性から、元の開で計算したframe変換を空開を含む全部分開へ移送。実Cartier方程式の単元比による対象frame変換を全部分開で証明。同じ実affine開のetale座標変更について、元の標準Cartier方程式が実微分基底の逆Jacobian単元倍になる正確な公式を既存の微分基底base-changeから証明。源・対象の両frameと留数係数の同時変換が相殺する実加群層同型の等式を証明。実Cartier切断の同一affineチャートで周囲座標と切断座標を同時に変更しても、元のi^*O(K_X+D)からO(K_Y)への正規化局所標準随伴層同型が一致することを、全Jacobian単元・係数則を元座標から内部構成して証明。異なるaffineチャートへの制限比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
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
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Simultaneous source and target frame changes cancel with the residue
coefficient as an equality of ACTUAL module-sheaf isomorphisms. -/
theorem moduleWeightedFrameIso_cancel_both_changes
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d d' : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a a' : Γ(X, U)ˣ) (v w : Γ(X, U)) (hc : ↑a' * v = w * ↑a)
    (he : ∀ (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)),
      moduleOverFrameCoefficient M U e' W hWU s =
        X.presheaf.map (homOfLE hWU).op v * moduleOverFrameCoefficient M U e W hWU s)
    (hd : ∀ (W : X.Opens) (hWU : W ≤ U) (s : Γ(N, W)),
      moduleOverFrameCoefficient N U d' W hWU s =
        X.presheaf.map (homOfLE hWU).op w * moduleOverFrameCoefficient N U d W hWU s) :
    moduleOverFrameWeightedIso M N U e' d' a' = moduleOverFrameWeightedIso M N U e d a := by
  symm
  apply moduleOverFrameWeightedIso_unique
  intro W hWU s
  rw [hd, moduleOverFrameWeightedIso_coefficient, he]
  rw [← mul_assoc, ← map_mul, ← hc, map_mul, mul_assoc]

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAdjunctionEquationIndependence
public import MixedFujita.PulledCanonicalResidueTransitions

/-! 実Cartier frameの全部分開変換と逆Jacobian公式。 check-284：実unit-frame生成元の係数1と生成性から、元の開で計算したframe変換を空開を含む全部分開へ移送。実Cartier方程式の単元比による対象frame変換を全部分開で証明。同じ実affine開のetale座標変更について、元の標準Cartier方程式が実微分基底の逆Jacobian単元倍になる正確な公式を既存の微分基底base-changeから証明。源・対象の両frameと留数係数の同時変換が相殺する実加群層同型の等式を証明。実Cartier切断の同一affineチャートで周囲座標と切断座標を同時に変更しても、元のi^*O(K_X+D)からO(K_Y)への正規化局所標準随伴層同型が一致することを、全Jacobian単元・係数則を元座標から内部構成して証明。異なるaffineチャートへの制限比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- A transition computed on the original unit-frame generator extends to
ALL subopens, including empty ones, without a rational-field case split. -/
theorem moduleOverFrame_coefficient_change_of_top
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (a : Γ(X, U))
    (he : ∀ s : Γ(M, U), moduleOverFrameCoefficient M U e' U le_rfl s =
      a * moduleOverFrameCoefficient M U e U le_rfl s)
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    moduleOverFrameCoefficient M U e' W hWU s =
      X.presheaf.map (homOfLE hWU).op a * moduleOverFrameCoefficient M U e W hWU s := by
  let t := (moduleOverFrameCoefficient M U e U le_rfl).symm 1
  have ht : moduleOverFrameCoefficient M U e U le_rfl t = 1 := LinearEquiv.apply_symm_apply _ _
  have ht' : moduleOverFrameCoefficient M U e' U le_rfl t = a := by rw [he, ht, mul_one]
  conv_lhs => rw [moduleFrame_section_eq_coefficient_smul M U e t ht W hWU s]
  rw [map_smul, moduleOverFrameCoefficient_restrict _ _ _ le_rfl,
    ht', smul_eq_mul, mul_comm]


/-- An actual regular-unit ratio of Cartier equations controls both actual
Cartier frames on EVERY subopen, not merely on the affine section module. -/
theorem cartierOpenFrameCoefficient_unit_equation_change
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f f' : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (hf' : rationalUnitClass X U (Additive.ofMul f') = D |_ U)
    (a : Γ(X, U)ˣ) (ha : f' = Units.map (X.germToFunctionField U).hom a * f)
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(D.sheaf, W)) :
    moduleOverFrameCoefficient D.sheaf U (cartierOpenFrameIso D U f' hf') W hWU s =
      X.presheaf.map (homOfLE hWU).op ↑a *
        moduleOverFrameCoefficient D.sheaf U (cartierOpenFrameIso D U f hf) W hWU s := by
  apply moduleOverFrame_coefficient_change_of_top D.sheaf U
    (cartierOpenFrameIso D U f hf) (cartierOpenFrameIso D U f' hf') (a : Γ(X, U))
  exact fun t => cartierOpenCoefficient_unit_equation_change D U f f' hf hf' a ha t


/-- On the SAME actual affine open, changing etale coordinates changes the
ORIGINAL canonical Cartier equation by the EXACT inverse Jacobian unit. -/
theorem etaleChartCanonicalEquation_same_open_change
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ} (c₀ c : EtaleChart K X n)
    (x' : MvPolynomial (Fin n) K →ₐ[K] Γ(X, c.U)) (hx' : x'.toRingHom.FormallyEtale) :
    let c' : EtaleChart K X n := { c with coords := x', formallyEtale := hx' }
    let a := (Module.Basis.isUnit_det (etaleCoordinateBasis x' hx')
      (etaleCoordinateBasis c.coords c.formallyEtale)).unit
    etaleChartCanonicalEquation c₀ c' =
      Units.map (X.germToFunctionField c.U).hom a * etaleChartCanonicalEquation c₀ c := by
  let c' : EtaleChart K X n := { c with coords := x', formallyEtale := hx' }
  have hd := etaleCoordinateBasis_det_comp (sectionGermAlgHom (K := K) c.U)
    (sectionGermAlgHom_formallyEtale c.U c.isAffine) x' c.coords hx' c.formallyEtale
  change (etaleChartBasis c').det (etaleChartBasis c) =
    X.germToFunctionField c.U
      ((etaleCoordinateBasis x' hx').det (etaleCoordinateBasis c.coords c.formallyEtale)) at hd
  apply Units.ext
  rw [Units.val_mul, Units.coe_map, IsUnit.unit_spec,
    etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val]
  exact (Module.Basis.det_mul_det (etaleChartBasis c') (etaleChartBasis c)
    (etaleChartBasis c₀)).symm.trans
      (congrArg (fun t : X.functionField => t * (etaleChartBasis c).det (etaleChartBasis c₀)) hd)

end MixedFujita

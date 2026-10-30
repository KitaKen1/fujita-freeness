/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PureResidueEquationUniqueness

/-! 実Cartier方程式の単元比・実pullback frameの全部分開変換。 check-283：実商の全射性から微分の全持ち上げを内部供給し、純ambient dg楔積だけで実引き戻し標準加群の線形写像を検出することを証明。純正規化公式による留数の一意性、および任意に独立構成した二留数の方程式変更則を証明。同じ有効Cartier因子の二つの実正則方程式から、実イデアルの一致を通じて実単元を内部抽出。元のCartier係数と実線束pullback frameの全部分開の変換則を証明。実Cartier切断の同一affineチャート・固定座標の下で、二方程式から正規化留数とframe単元をそれぞれ内部構成し、逆向きの係数変化が打ち消し合うことから実局所標準随伴層同型の一致を構成。異なる座標・チャート間の一致、大域留数貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
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


/-- Two actual regular equations of the SAME effective Cartier divisor on
an affine chart differ by an actual unit, derived from its actual ideal. -/
theorem effectiveCartier_affine_equations_unit
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (hD : D.IsEffective)
    (U : X.affineOpens) [Nonempty U.1] (g g' : Γ(X, U.1)) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hEq : rationalUnitClass X U.1
      (Additive.ofMul (regularEquationRationalUnit X U.1 g hg)) = D |_ U.1)
    (hEq' : rationalUnitClass X U.1
      (Additive.ofMul (regularEquationRationalUnit X U.1 g' hg')) = D |_ U.1) :
    ∃ a : Γ(X, U.1)ˣ, g' = ↑a * g := by
  have hi : Ideal.span ({g} : Set Γ(X, U.1)) = Ideal.span {g'} :=
    (effectiveCartierIdealSheaf_ideal_eq_span D hD U g hg hEq).symm.trans
      (effectiveCartierIdealSheaf_ideal_eq_span D hD U g' hg' hEq')
  obtain ⟨a, ha⟩ := Ideal.span_singleton_eq_span_singleton.mp hi
  exact ⟨a, by simpa only [mul_comm] using ha.symm⟩


/-- Actual Cartier coefficients transform by the ACTUAL regular unit ratio
of their local equations, proved in the function field, not assumed. -/
theorem cartierOpenCoefficient_unit_equation_change
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f f' : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (hf' : rationalUnitClass X U (Additive.ofMul f') = D |_ U)
    (a : Γ(X, U)ˣ) (ha : f' = Units.map (X.germToFunctionField U).hom a * f)
    (s : Γ(D.sheaf, U)) :
    cartierOpenCoefficient D U f' hf' U le_rfl s =
      (a : Γ(X, U)) * cartierOpenCoefficient D U f hf U le_rfl s := by
  apply X.germToFunctionField_injective U
  rw [map_mul, cartierOpenCoefficient_image, cartierOpenCoefficient_image, ha, Units.val_mul]
  simp only [Units.coe_map]
  exact mul_assoc _ _ _


/-- A source frame transition is transported through the ACTUAL pullback,
using the pulled original frame generator, then extended to ALL subopens. -/
theorem modulePulledOpenFrame_coefficient_change
    {X Y : Scheme.{u}} (i : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e e' : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (a : Γ(X, U))
    (he : ∀ s : Γ(M, U),
      moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e') U le_rfl s =
        a * moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) U le_rfl s)
    (W : Y.Opens) (hWU : W ≤ i ⁻¹ᵁ U) (s : Γ((Scheme.Modules.pullback i).obj M, W)) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U)
        (modulePulledOpenFrame i M U e') W hWU s =
      Y.presheaf.map (homOfLE hWU).op (i.app U a) *
        moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U)
          (modulePulledOpenFrame i M U e) W hWU s := by
  let t := modulePullbackSections i M U (moduleOpenFrameGenerator M U e)
  have ht : moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U)
      (modulePulledOpenFrame i M U e') (i ⁻¹ᵁ U) le_rfl t = i.app U a := by
    rw [modulePulledOpenFrame, modulePullbackSections_local_frame_coefficient, he,
      moduleOpenFrameGenerator_coefficient, mul_one]
  conv_lhs => rw [modulePullbackFrameGenerator_generates i M U e W hWU s]
  rw [map_smul, moduleOverFrameCoefficient_restrict _ _ _ le_rfl, ht, smul_eq_mul, mul_comm]


/-- The actual pulled-back Cartier frame transforms by the actual pulled
regular unit on every subopen, including the empty open. -/
theorem cartierPullbackFrameCoefficient_unit_equation_change
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (i : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f f' : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (hf' : rationalUnitClass X U (Additive.ofMul f') = D |_ U)
    (a : Γ(X, U)ˣ) (ha : f' = Units.map (X.germToFunctionField U).hom a * f)
    (W : Y.Opens) (hWU : W ≤ i ⁻¹ᵁ U) (s : Γ((Scheme.Modules.pullback i).obj D.sheaf, W)) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj D.sheaf) (i ⁻¹ᵁ U)
        (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D i U f' hf')) W hWU s =
      Y.presheaf.map (homOfLE hWU).op (i.app U ↑a) *
        moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj D.sheaf) (i ⁻¹ᵁ U)
          (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D i U f hf)) W hWU s := by
  apply modulePulledOpenFrame_coefficient_change i D.sheaf U
    (cartierOpenRestrictFrameIso D U f hf) (cartierOpenRestrictFrameIso D U f' hf') (a : Γ(X, U))
  intro t
  dsimp only [cartierOpenRestrictFrameIso]
  rw [moduleRestrictFrameOverIso_roundTrip, moduleRestrictFrameOverIso_roundTrip]
  exact cartierOpenCoefficient_unit_equation_change D U f f' hf hf' a ha t

end MixedFujita

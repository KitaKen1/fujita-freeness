/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierAffineResidue
public import MixedFujita.CurveCanonicalDifferentialLattice
public import MixedFujita.ModuleOpenFrameCoefficients

/-! 最高外積の行列式座標と実像の正則性判定。 check-281：実基底を保つ最高外積写像について、行列式座標の正確な係数式と実像の所属判定を証明。標準Cartier局所方程式＝参照最高次形式の係数を任意次元で同定し、元の標準Cartier因子の実切断と、全実stalkの微分加群から来る正則有理最高次形式の同値を任意の非空開で証明。元のCartier層切断から実有理最高次形式への線形比較を構成し、全非空開の制限自然性・単射性・正則形式の一意逆像を証明。実etale affineチャートでは、元の標準Cartier切断加群と実Kaehler最高外積の線形同型を構成し、元の有理切断と参照形式による正確な正規化を証明。留数を引き戻し標準Cartier線束へ移す部分、大域留数層同型、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
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
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower


/-- Every top exterior vector has its actual determinant coordinate. -/
theorem topExterior_coordinate_smul_wedge
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (b : Module.Basis (Fin n) R M) (w : ⋀[R]^n M) :
    determinantCoordinate b w • exteriorPower.ιMulti R n b = w :=
  (determinantCoordinate b).symm_apply_apply w


/-- A map carrying an actual basis to an actual basis retains its determinant
coordinate, with precisely the actual scalar ring map. -/
theorem exteriorScalarMap_top_coordinate
    {R F M N : Type*} [CommRing R] [CommRing F] [Algebra R F]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower R F N] {n : ℕ}
    (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin n) F N)
    (f : M →ₗ[R] N) (hf : ∀ i, f (b i) = c i) (w : ⋀[R]^n M) :
    exteriorScalarMap R F M N f n w =
      algebraMap R F (determinantCoordinate b w) • exteriorPower.ιMulti F n c := by
  calc
    _ = exteriorScalarMap R F M N f n
        (determinantCoordinate b w • exteriorPower.ιMulti R n b) :=
      congrArg _ (topExterior_coordinate_smul_wedge b w).symm
    _ = _ := by
      rw [map_smul, exteriorScalarMap_wedge]
      have hb : f ∘ b = c := funext hf
      rw [hb, algebraMap_smul]


/-- Membership in the actual image of the top differential lattice is exactly
regularity of its scalar determinant coordinate. No image certificate is input. -/
theorem exteriorScalarMap_top_range_iff
    {R F M N : Type*} [CommRing R] [CommRing F] [Algebra R F]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module F N] [IsScalarTower R F N] {n : ℕ}
    (b : Module.Basis (Fin n) R M) (c : Module.Basis (Fin n) F N)
    (f : M →ₗ[R] N) (hf : ∀ i, f (b i) = c i) (w : ⋀[F]^n N) :
    (∃ v, exteriorScalarMap R F M N f n v = w) ↔
      determinantCoordinate c w ∈ (algebraMap R F).range := by
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨determinantCoordinate b v, ?_⟩
    rw [exteriorScalarMap_top_coordinate b c f hf, map_smul,
      determinantCoordinate_wedge, Module.Basis.det_self, smul_eq_mul, mul_one]
  · rintro ⟨a, ha⟩
    refine ⟨(determinantCoordinate b).symm a, ?_⟩
    rw [exteriorScalarMap_top_coordinate b c f hf,
      LinearEquiv.apply_symm_apply, ha]
    exact topExterior_coordinate_smul_wedge c w

end MixedFujita

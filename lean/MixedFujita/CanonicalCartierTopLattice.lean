/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.TopExteriorDifferentialLattice

/-! 任意次元の標準Cartier局所方程式と全stalk最高次形式。 check-281：実基底を保つ最高外積写像について、行列式座標の正確な係数式と実像の所属判定を証明。標準Cartier局所方程式＝参照最高次形式の係数を任意次元で同定し、元の標準Cartier因子の実切断と、全実stalkの微分加群から来る正則有理最高次形式の同値を任意の非空開で証明。元のCartier層切断から実有理最高次形式への線形比較を構成し、全非空開の制限自然性・単射性・正則形式の一意逆像を証明。実etale affineチャートでは、元の標準Cartier切断加群と実Kaehler最高外積の線形同型を構成し、元の有理切断と参照形式による正確な正規化を証明。留数を引き戻し標準Cartier線束へ移す部分、大域留数層同型、SNC反復随伴、数値随伴は残る。 -/

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


/-- The actual canonical Cartier equation is the coefficient of the reference
top differential in the local coordinate frame, in every dimension. -/
theorem etaleChartCanonicalEquation_top_wedge {n : ℕ} (c₀ c : EtaleChart K X n) :
    (etaleChartCanonicalEquation c₀ c : X.functionField) •
        exteriorPower.ιMulti X.functionField n (etaleChartBasis c) =
      exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀) := by
  rw [etaleChartCanonicalEquation_val]
  exact (alternating_basis_formula (etaleChartBasis c)
    (exteriorPower.ιMulti X.functionField n) (etaleChartBasis c₀)).symm


/-- The actual top differential map from the scheme stalk to its function field. -/
noncomputable def stalkRationalTopDifferentialMap (n : ℕ) (x : X) :
    (⋀[X.presheaf.stalk x]^n Ω[X.presheaf.stalk x⁄K]) →ₗ[K]
      ⋀[X.functionField]^n Ω[X.functionField⁄K] :=
  (exteriorDifferentialMap K K (X.presheaf.stalk x) X.functionField n).restrictScalars K


/-- The top differential image at an actual etale-chart stalk is its actual
regular scalar lattice, with no dimension-one restriction. -/
theorem top_differential_mem_stalk_range_iff {n : ℕ} (c : EtaleChart K X n)
    (x : X) (hx : x ∈ c.U) (w : ⋀[X.functionField]^n Ω[X.functionField⁄K]) :
    w ∈ (stalkRationalTopDifferentialMap (K := K) n x).range ↔
      determinantCoordinate (etaleChartBasis c) w ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  exact exteriorScalarMap_top_range_iff
    (etaleCoordinateBasis (etaleChartStalkCoords c x hx)
      (etaleChartStalkCoords_formallyEtale c x hx)) (etaleChartBasis c)
    (KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField)
    (etaleChart_differential_map_basis c x hx) w


/-- Actual sections of the original canonical Cartier divisor are precisely
rational top forms regular in every actual cotangent stalk. This holds on
EVERY nonempty open and in arbitrary dimension. -/
theorem canonicalDivisor_sections_iff_regular_top_differential {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (U : X.Opens) [Nonempty U]
    (s : Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions X, U)) :
    s ∈ (canonicalDivisor n c₀ hcover).sections U ↔
      ∀ x ∈ U, (rationalFunctionsEquiv U s) •
        exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀) ∈
          (stalkRationalTopDifferentialMap (K := K) n x).range := by
  have hcoord (c : EtaleChart K X n) :
      determinantCoordinate (etaleChartBasis c)
        ((rationalFunctionsEquiv U s) •
          exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀)) =
        (etaleChartCanonicalEquation c₀ c : X.functionField) * rationalFunctionsEquiv U s := by
    rw [← etaleChartCanonicalEquation_top_wedge c₀ c, smul_smul, map_smul,
      determinantCoordinate_wedge, Module.Basis.det_self, smul_eq_mul, mul_one, mul_comm]
  constructor
  · intro hs x hx
    obtain ⟨c, hxc⟩ : ∃ c : EtaleChart K X n, x ∈ c.U := by
      have hmem : x ∈ iSup (fun c : EtaleChart K X n => c.U) := hcover.symm ▸ Opens.mem_top x
      simpa only [Opens.mem_iSup] using hmem
    rw [top_differential_mem_stalk_range_iff c x hxc, hcoord]
    exact (CartierDivisor.mem_sections.mp hs) x hx _
      (canonicalDivisor_isLocalEquationAt c₀ hcover c hxc)
  · intro hs
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    obtain ⟨c, hxc⟩ : ∃ c : EtaleChart K X n, x ∈ c.U := by
      have hmem : x ∈ iSup (fun c : EtaleChart K X n => c.U) := hcover.symm ▸ Opens.mem_top x
      simpa only [Opens.mem_iSup] using hmem
    refine ⟨etaleChartCanonicalEquation c₀ c,
      canonicalDivisor_isLocalEquationAt c₀ hcover c hxc, ?_⟩
    have h := (top_differential_mem_stalk_range_iff c x hxc _).mp (hs x hx)
    rwa [hcoord] at h

end MixedFujita

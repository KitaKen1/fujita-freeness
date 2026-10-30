/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierTopLattice

/-! 全非空開の標準Cartier切断と正則最高次形式の一意対応。 check-281：実基底を保つ最高外積写像について、行列式座標の正確な係数式と実像の所属判定を証明。標準Cartier局所方程式＝参照最高次形式の係数を任意次元で同定し、元の標準Cartier因子の実切断と、全実stalkの微分加群から来る正則有理最高次形式の同値を任意の非空開で証明。元のCartier層切断から実有理最高次形式への線形比較を構成し、全非空開の制限自然性・単射性・正則形式の一意逆像を証明。実etale affineチャートでは、元の標準Cartier切断加群と実Kaehler最高外積の線形同型を構成し、元の有理切断と参照形式による正確な正規化を証明。留数を引き戻し標準Cartier線束へ移す部分、大域留数層同型、SNC反復随伴、数値随伴は残る。 -/

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


/-- The actual base-field actions on every nonempty open and function field
form a scalar tower; no scalar-compatibility hypothesis is needed. -/
theorem canonicalOpenFunctionFieldScalarTower (U : X.Opens) [Nonempty U] :
    IsScalarTower K Γ(X, U) X.functionField :=
  IsScalarTower.of_algebraMap_eq fun a => (sectionGermAlgHom (K := K) U).commutes a |>.symm

attribute [local instance] canonicalOpenFunctionFieldScalarTower


/-- The original canonical Cartier sheaf maps on every nonempty open to the
actual rational top forms by multiplying its coefficient by the reference form. -/
noncomputable def canonicalCartierRationalTopForm {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (U : X.Opens) [Nonempty U] :
    Γ((canonicalDivisor n c₀ hcover).sheaf, U) →ₗ[Γ(X, U)]
      ⋀[X.functionField]^n Ω[X.functionField⁄K] :=
  ((LinearMap.toSpanSingleton X.functionField _
    (exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀))).restrictScalars Γ(X, U)).comp
      ((rationalFunctionsEquiv U).toLinearMap.comp
        ((canonicalDivisor n c₀ hcover).sheafι.val.app (op U)).hom)


/-- The canonical Cartier comparison retains the actual rational section. -/
theorem canonicalCartierRationalTopForm_apply {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (U : X.Opens) [Nonempty U]
    (s : Γ((canonicalDivisor n c₀ hcover).sheaf, U)) :
    canonicalCartierRationalTopForm c₀ hcover U s =
      rationalFunctionsEquiv U
        (Scheme.Modules.Hom.app (canonicalDivisor n c₀ hcover).sheafι U s) •
          exteriorPower.ιMulti X.functionField n (etaleChartBasis c₀) := rfl


/-- The actual comparison commutes with every restriction between nonempty
opens, so the dictionary is compatible on overlaps, not only at global sections. -/
theorem canonicalCartierRationalTopForm_restrict {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    {U V : X.Opens} [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (s : Γ((canonicalDivisor n c₀ hcover).sheaf, U)) :
    canonicalCartierRationalTopForm c₀ hcover V
        ((canonicalDivisor n c₀ hcover).sheaf.presheaf.map (homOfLE hVU).op s) =
      canonicalCartierRationalTopForm c₀ hcover U s := by
  rw [canonicalCartierRationalTopForm_apply, canonicalCartierRationalTopForm_apply]
  have h := ConcreteCategory.congr_hom
    ((canonicalDivisor n c₀ hcover).sheafι.mapPresheaf.naturality (homOfLE hVU).op) s
  change Scheme.Modules.Hom.app (canonicalDivisor n c₀ hcover).sheafι V
      ((canonicalDivisor n c₀ hcover).sheaf.presheaf.map (homOfLE hVU).op s) =
    (rationalFunctions X).presheaf.map (homOfLE hVU).op
      (Scheme.Modules.Hom.app (canonicalDivisor n c₀ hcover).sheafι U s) at h
  rw [h, rationalFunctionsEquiv_map]


/-- This comparison loses no actual Cartier section on any nonempty open. -/
theorem canonicalCartierRationalTopForm_injective {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (canonicalCartierRationalTopForm c₀ hcover U) := by
  intro s t h
  apply (canonicalDivisor n c₀ hcover).sheafι_app_injective U
  apply (rationalFunctionsEquiv U).injective
  have h' := congrArg (determinantCoordinate (etaleChartBasis c₀)) h
  simpa only [canonicalCartierRationalTopForm_apply, map_smul,
    determinantCoordinate_wedge, Module.Basis.det_self, smul_eq_mul, mul_one] using h'


/-- Every rational top form regular in all actual cotangent stalks comes from
one UNIQUE actual canonical Cartier section. This is an all-open, arbitrary-
dimension dictionary, with the original canonical divisor unchanged. -/
theorem canonicalCartierRationalTopForm_range_iff {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (U : X.Opens) [Nonempty U] (w : ⋀[X.functionField]^n Ω[X.functionField⁄K]) :
    (∃! s, canonicalCartierRationalTopForm c₀ hcover U s = w) ↔
      ∀ x ∈ U, w ∈ (stalkRationalTopDifferentialMap (K := K) n x).range := by
  let D := canonicalDivisor n c₀ hcover
  constructor
  · rintro ⟨s, rfl, _⟩
    rw [canonicalCartierRationalTopForm_apply]
    exact (canonicalDivisor_sections_iff_regular_top_differential c₀ hcover U _).mp
      (D.sheafι_app_mem U s)
  · intro hw
    let a := determinantCoordinate (etaleChartBasis c₀) w
    let s := (rationalFunctionsEquiv (X := X) U).symm a
    have hs : s ∈ D.sections U := by
      apply (canonicalDivisor_sections_iff_regular_top_differential c₀ hcover U s).mpr
      rw [LinearEquiv.apply_symm_apply, topExterior_coordinate_smul_wedge]
      exact hw
    have hsf : canonicalCartierRationalTopForm c₀ hcover U (CartierDivisor.sectionMk s hs) = w := by
      rw [canonicalCartierRationalTopForm_apply, CartierDivisor.sheafι_app_sectionMk,
        LinearEquiv.apply_symm_apply]
      exact topExterior_coordinate_smul_wedge (etaleChartBasis c₀) w
    exact ⟨CartierDivisor.sectionMk s hs, hsf, fun t ht =>
      canonicalCartierRationalTopForm_injective c₀ hcover U (ht.trans hsf.symm)⟩


/-- Actual affine-chart differential bases map to the generic coordinate basis. -/
theorem etaleChart_open_differential_map_basis {n : ℕ} (c : EtaleChart K X n) (i : Fin n) :
    KaehlerDifferential.map K K Γ(X, c.U) X.functionField
      (etaleCoordinateBasis c.coords c.formallyEtale i) = etaleChartBasis c i := by
  rw [etaleCoordinateBasis_apply, map_D]
  unfold etaleChartBasis
  rw [etaleCoordinateBasis_apply]
  rfl


/-- The ACTUAL canonical Cartier sections on an etale affine chart are its
actual top Kaehler forms, via the canonical Cartier frame and wedge basis. -/
noncomputable def canonicalCartierAffineFormEquiv {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c : EtaleChart K X n) :
    Γ((canonicalDivisor n c₀ hcover).sheaf, c.U) ≃ₗ[Γ(X, c.U)]
      ⋀[Γ(X, c.U)]^n Ω[Γ(X, c.U)⁄K] :=
  (moduleOverFrameCoefficient _ c.U
    (cartierOpenFrameIso (canonicalDivisor n c₀ hcover) c.U
      (etaleChartCanonicalEquation c₀ c) (canonicalDivisor_restrict c₀ hcover c).symm)
        c.U le_rfl).trans (determinantCoordinate (etaleCoordinateBasis c.coords c.formallyEtale)).symm


/-- The chartwise Cartier/form isomorphism is normalized by the ACTUAL rational
section and reference top form. Thus it agrees with the all-open comparison,
rather than merely giving an unspecified unit between two rank-one modules. -/
theorem canonicalCartierAffineFormEquiv_rational {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c : EtaleChart K X n)
    (s : Γ((canonicalDivisor n c₀ hcover).sheaf, c.U)) :
    exteriorDifferentialMap K K Γ(X, c.U) X.functionField n
        (canonicalCartierAffineFormEquiv c₀ hcover c s) =
      canonicalCartierRationalTopForm c₀ hcover c.U s := by
  let b := etaleCoordinateBasis c.coords c.formallyEtale
  change exteriorScalarMap Γ(X, c.U) X.functionField _ _ _ n _ = _
  rw [exteriorScalarMap_top_coordinate b (etaleChartBasis c)
    (KaehlerDifferential.map K K Γ(X, c.U) X.functionField)
    (etaleChart_open_differential_map_basis c)]
  have hc : determinantCoordinate b (canonicalCartierAffineFormEquiv c₀ hcover c s) =
      cartierOpenCoefficient (canonicalDivisor n c₀ hcover) c.U
        (etaleChartCanonicalEquation c₀ c) (canonicalDivisor_restrict c₀ hcover c).symm
          c.U le_rfl s := by
    change determinantCoordinate b ((determinantCoordinate b).symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [hc, canonicalCartierRationalTopForm_apply]
  have hcoeff := cartierOpenCoefficient_image (canonicalDivisor n c₀ hcover) c.U
    (etaleChartCanonicalEquation c₀ c) (canonicalDivisor_restrict c₀ hcover c).symm
      c.U le_rfl s
  change algebraMap Γ(X, c.U) X.functionField _ = _ at hcoeff
  rw [hcoeff, mul_comm, mul_smul, etaleChartCanonicalEquation_top_wedge]

end MixedFujita

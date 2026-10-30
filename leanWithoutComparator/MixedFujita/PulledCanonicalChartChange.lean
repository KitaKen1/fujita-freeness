/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PulledCanonicalResidueTransitions

/-! 実引き戻し標準加群の制限と外積基底変更自然性。 check-280：実引き戻し標準加群のチャート制限写像を構成し、任意の可換環図式で外積基底変更との自然性を証明。元の正則滑らか主商と実局所化から、両チャートの正規化留数同型を内部構成し、局所化と方程式の単元変更を合わせた制限則を実引き戻し標準加群上へ移送。有効Cartier因子の実閉部分スキームのaffine関数環について、方程式の非零因子性・実閉埋込みの全射性・核=(g)を内部供給。周囲と切断の実etale座標から形式的滑らかさと微分基底を供給し、実Cartier切断の正規化留数・frame単元性へ接続。標準Cartier層との同定・大域留数層同型・数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
open OAI.ReverseLogKodaira.DifferentialBaseChange
namespace MixedFujita

variable {K A B S C : Type*} [CommRing K] [CommRing A] [CommRing B]
  [CommRing S] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K S] [Algebra K C]
  [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
  [IsScalarTower K A B] [IsScalarTower K A S] [IsScalarTower K A C]
  [IsScalarTower K B C] [IsScalarTower K S C]
  [IsScalarTower A B C] [IsScalarTower A S C]


/-- Restriction between the actual pulled-back ambient canonical modules. -/
noncomputable def pulledCanonicalChartChange (n : ℕ) :
    B ⊗[A] (⋀[A]^n Ω[A⁄K]) →ₗ[B] C ⊗[S] (⋀[S]^n Ω[S⁄K]) :=
  (((TensorProduct.mk S C (⋀[S]^n Ω[S⁄K]) (1 : C)).restrictScalars A).comp
    (exteriorDifferentialMap K K A S n)).liftBaseChange B


/-- The restriction has the expected formula on actual pure tensors. -/
theorem pulledCanonicalChartChange_tmul (n : ℕ) (a : B) (w : ⋀[A]^n Ω[A⁄K]) :
    pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) n (a ⊗ₜ[A] w) =
      algebraMap B C a • ((1 : C) ⊗ₜ[S] exteriorDifferentialMap K K A S n w) := by
  simp only [pulledCanonicalChartChange, LinearMap.liftBaseChange_tmul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    IsScalarTower.algebraMap_smul]


/-- Exterior base change commutes with the genuine canonical-module restriction,
for any compatible ring square; no restriction compatibility is assumed. -/
theorem finiteFreeExteriorBaseChangeEquiv_chart_naturality
    {m m' : ℕ} (b : Module.Basis (Fin m) A Ω[A⁄K])
    (b' : Module.Basis (Fin m') S Ω[S⁄K]) (n : ℕ) :
    (exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (K := K) (A := A) (B := B) (S := S) (C := C)) n).comp
        (finiteFreeExteriorBaseChangeEquiv (B := B) b n).toLinearMap =
      ((finiteFreeExteriorBaseChangeEquiv (B := C) b' n).toLinearMap.restrictScalars B).comp
        (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) n) := by
  let L := (exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (K := K) (A := A) (B := B) (S := S) (C := C)) n).comp
    (finiteFreeExteriorBaseChangeEquiv (B := B) b n).toLinearMap
  let R := ((finiteFreeExteriorBaseChangeEquiv (B := C) b' n).toLinearMap.restrictScalars B).comp
    (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) n)
  have h0 : (L.restrictScalars A).comp (TensorProduct.mk A B (⋀[A]^n Ω[A⁄K]) 1) =
      (R.restrictScalars A).comp (TensorProduct.mk A B (⋀[A]^n Ω[A⁄K]) 1) := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span A n Ω[A⁄K])
    rintro _ ⟨v, rfl⟩
    change exteriorScalarMap B C _ _ _ n
        (finiteFreeExteriorBaseChangeEquiv b n ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n v)) =
      finiteFreeExteriorBaseChangeEquiv b' n
        (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) n
          ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n v))
    rw [finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul,
      exteriorScalarMap_wedge, pulledCanonicalChartChange_tmul, map_one, one_smul]
    change _ = finiteFreeExteriorBaseChangeEquiv b' n
      ((1 : C) ⊗ₜ[S] exteriorScalarMap A S _ _ (KaehlerDifferential.map K K A S) n
        (exteriorPower.ιMulti A n v))
    rw [exteriorScalarMap_wedge, finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
    congr 1
    funext i
    simp only [Function.comp_apply, principalQuotientDifferentialChange_tmul, map_one, one_smul]
  change L = R
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext'
  intro a w
  change L (a ⊗ₜ[A] w) = R (a ⊗ₜ[A] w)
  rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, map_smul]
  exact congrArg (fun z => a • z) (LinearMap.congr_fun h0 w)

end MixedFujita

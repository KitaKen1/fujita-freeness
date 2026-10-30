/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothCartierCanonicalAdjunction
public import OAI.AlgebraicGeometry.LogKodaira.BaseChange
public import OAI.AlgebraicGeometry.LogKodaira.RelativeCanonical

/-! 実商環図式の周囲微分写像と可換性。 check-278：可換な実商環図式で制限された周囲微分加群の実写像を構成し、純テンソル式・余法生成元・商微分との可換性を証明。OpenAI由来の外積の係数変更APIと楔積の生成性を再利用し、正規化した局所標準随伴および逆向き留数写像の自然性を証明。実際の局所化では、元の正則主商から局所化後の正則性・全射性・核・微分基底・滑らかさを内部供給し、局所化と方程式の単元変更を同時に許す正規化留数の整合性まで構成。大域の層同型・標準Cartier因子との比較・元lc中心の数値随伴は引き続き残る。 -/

@[expose] public section
set_option autoImplicit false
-- The related lemmas deliberately share one compatible ring-square context.
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
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


/-- The actual map between restricted ambient differential modules for a
commuting square of quotient charts. No compatibility certificate is input. -/
noncomputable def principalQuotientDifferentialChange :
    B ⊗[A] Ω[A⁄K] →ₗ[B] C ⊗[S] Ω[S⁄K] :=
  (((TensorProduct.mk S C Ω[S⁄K] (1 : C)).restrictScalars A).comp
    (KaehlerDifferential.map K K A S)).liftBaseChange B


/-- Pure tensors retain the actual ring maps and Kähler differential map. -/
theorem principalQuotientDifferentialChange_tmul (b : B) (w : Ω[A⁄K]) :
    principalQuotientDifferentialChange (S := S) (C := C) (b ⊗ₜ[A] w) =
      algebraMap B C b • ((1 : C) ⊗ₜ[S] KaehlerDifferential.map K K A S w) := by
  simp only [principalQuotientDifferentialChange, LinearMap.liftBaseChange_tmul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    IsScalarTower.algebraMap_smul]


/-- Actual conormal generators map to the differential of the actual
pulled-back equation in the second quotient chart. -/
theorem principalQuotientDifferentialChange_conormal (g : A) :
    principalQuotientDifferentialChange (B := B) (S := S) (C := C)
        ((1 : B) ⊗ₜ[A] D K A g) =
      (1 : C) ⊗ₜ[S] D K S (algebraMap A S g) := by
  rw [principalQuotientDifferentialChange_tmul, map_D, map_one, one_smul]


/-- The two genuine quotient differential maps commute with the actual
ambient-chart change, for an arbitrary compatible square of rings. -/
theorem principalQuotientDifferentialChange_quotient_square :
    ((mapBaseChange K S C).restrictScalars B).comp
        (principalQuotientDifferentialChange (A := A) (B := B) (S := S)) =
      (KaehlerDifferential.map K K B C).comp (mapBaseChange K A B) := by
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b w =>
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      principalQuotientDifferentialChange_tmul, mapBaseChange_tmul, map_smul]
    rw [OAI.ReverseLogKodaira.RelativeCanonical.differential_map_tower K A S C,
      OAI.ReverseLogKodaira.RelativeCanonical.differential_map_tower K A B C]
    simp only [one_smul, IsScalarTower.algebraMap_smul]

end MixedFujita

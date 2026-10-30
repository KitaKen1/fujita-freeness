/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleWeightedFrameIsomorphisms

/-! 実Cartier切断の正規化局所標準随伴層同型。 check-282：既存の構造層からの写像と切断の対応を再利用し、実開上の正則関数による構造加群写像、単元による同型、実frame間の重み付き加群層同型を構成。全部分開の正確な係数則と、その係数則による同型の一意性を証明。実スキームのK射が全開の定数を保つ既存APIから、実商環のK作用と標準K作用の一致を内部供給。標準Cartier因子と切断の局所方程式の積を元のK_X+Dの方程式と同定。実有効Cartier切断と周囲・切断のetale座標から、正規化留数とframe単元を内部構成し、実際のi^*O(K_X+D)とO(K_Y)の切断チャート上の加群層同型へ接続。全部分開の係数則、同じ正規化係数の下での一意性、実Cartier切断／最高次形式の正確な正規化を証明。異なるチャート・方程式間の一致、大域留数層貼合せ、SNC反復随伴、数値随伴は残る。 -/

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



/-- A genuine morphism over the base field preserves its actual constants on
all opens. The actual quotient algebra and canonical scheme base action agree. -/
theorem schemeApp_base_scalar_tower
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (i : Y ⟶ X) [i.IsOver (Spec (CommRingCat.of K))] (U : X.Opens) :
    let : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
    IsScalarTower K Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := by
  let : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a =>
    (Scheme.Modules.app_baseRingToStructurePresheaf (R := K) i U a).symm


/-- The ACTUAL canonical Cartier divisor plus an effective Cartier divisor
has the product of the canonical and cut equations as its local equation. -/
theorem canonicalPlusCartier_local_equation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c : EtaleChart K X n) (D : CartierDivisor X)
    (g : Γ(X, c.U)) (hg : g ≠ 0)
    (hEq : rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U g hg)) = D |_ c.U) :
    rationalUnitClass X c.U (Additive.ofMul
      (etaleChartCanonicalEquation c₀ c * regularEquationRationalUnit X c.U g hg)) =
        (canonicalDivisor n c₀ hcover + D) |_ c.U := by
  rw [ofMul_mul, map_add, ← canonicalDivisor_restrict c₀ hcover c, hEq]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]


/-- Original geometric Cartier-cut data internally construct a normalized
isomorphism of the ACTUAL sheaves i^*O(K_X+D) and O(K_Y) on the cut chart.
It acts on ALL subopens and is UNIQUE for the internally constructed residue
coefficient. No residue map, frame unit, sheaf iso or gluing law is supplied. -/
theorem smooth_effectiveCartier_local_adjunction_iso
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (hD : D.IsEffective)
    [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf D hD).subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsIntegral (effectiveCartierIdealSheaf D hD).subscheme]
    (r : ℕ) (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cX : EtaleChart K X (1 + r))
    (g : Γ(X, cX.U)) (hg : g ≠ 0)
    (hEq : rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U g hg)) = D |_ cX.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ((effectiveCartierIdealSheaf D hD).subscheme,
        (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale) :
    let I := effectiveCartierIdealSheaf D hD
    let Y := I.subscheme
    let i := I.subschemeι
    let V := i ⁻¹ᵁ cX.U
    let A := Γ(X, cX.U)
    let B := Γ(Y, V)
    let : Algebra A B := (i.app cX.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
    let cY : EtaleChart K Y r :=
      { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
        coords := y, formallyEtale := hy }
    let KX := canonicalDivisor (1 + r) cX₀ hX
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
    let e := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + D) i cX.U
        (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg)
        (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    ∃ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A g) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      ∃! Φ : M.over V ≅ KY.sheaf.over V,
        (∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
          moduleOverFrameCoefficient KY.sheaf V d W hWV
              (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
            Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (∀ s : Γ(M, V),
          canonicalCartierAffineFormEquiv cY₀ hY cY
              (Φ.hom.val.app (op (Over.mk (homOfLE (le_refl V)))) s) =
            moduleOverFrameCoefficient M V e V le_rfl s •
              R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
                (etaleCoordinateBasis cX.coords cX.formallyEtale))) := by
  let I := effectiveCartierIdealSheaf D hD
  let Y := I.subscheme
  let i := I.subschemeι
  let V := i ⁻¹ᵁ cX.U
  let A := Γ(X, cX.U)
  let B := Γ(Y, V)
  let : Algebra A B := (i.app cX.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
  let cY : EtaleChart K Y r :=
    { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
      coords := y, formallyEtale := hy }
  let KX := canonicalDivisor (1 + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
  let e := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg)
      (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  let : Algebra.FormallySmooth K A := formallySmooth_of_etale_coordinates cX.coords cX.formallyEtale
  let : Algebra.FormallySmooth K B := formallySmooth_of_etale_coordinates y hy
  obtain ⟨hreg, hsurj, hker⟩ := effectiveCartier_affine_principal_quotient_data D hD
    ⟨cX.U, cX.isAffine⟩ g hg hEq
  obtain ⟨R, _, hR, a, ha⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := A) (B := B) g hreg hsurj hker r
      (etaleCoordinateBasis cX.coords cX.formallyEtale) (etaleCoordinateBasis y hy)
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  dsimp only
  refine ⟨R, a, hR, ha, Φ, ?_, ?_⟩
  · constructor
    · exact fun W hWV s => moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
    · intro s
      change moduleOverFrameCoefficient KY.sheaf V d V le_rfl
          (Φ.hom.val.app (op (Over.mk (homOfLE (le_refl V)))) s) •
            exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) = _
      rw [moduleOverFrameWeightedIso_coefficient]
      rw [ha, smul_smul]
      apply congrArg (fun t : B => t • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy))
      change Y.presheaf.map (homOfLE (le_refl V)).op ↑a *
          moduleOverFrameCoefficient M V e V le_rfl s =
        moduleOverFrameCoefficient M V e V le_rfl s * ↑a
      have hres : Y.presheaf.map (homOfLE (le_refl V)).op ↑a = (a : B) :=
        Y.presheaf.map_id_apply (op V) (a : B)
      rw [hres, mul_comm]
  · intro Ψ hΨ
    exact moduleOverFrameWeightedIso_unique M KY.sheaf V e d a Ψ hΨ.1

end MixedFujita

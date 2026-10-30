/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.WeightedCoordinateSheafIsomorphisms

/-! 実局所標準随伴層同型の周囲・切断両座標からの独立性。 check-284：実unit-frame生成元の係数1と生成性から、元の開で計算したframe変換を空開を含む全部分開へ移送。実Cartier方程式の単元比による対象frame変換を全部分開で証明。同じ実affine開のetale座標変更について、元の標準Cartier方程式が実微分基底の逆Jacobian単元倍になる正確な公式を既存の微分基底base-changeから証明。源・対象の両frameと留数係数の同時変換が相殺する実加群層同型の等式を証明。実Cartier切断の同一affineチャートで周囲座標と切断座標を同時に変更しても、元のi^*O(K_X+D)からO(K_Y)への正規化局所標準随伴層同型が一致することを、全Jacobian単元・係数則を元座標から内部構成して証明。異なるaffineチャートへの制限比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- Simultaneously changing BOTH ambient and cut coordinates on the SAME
actual affine Cartier chart gives the SAME normalized actual local adjunction
SHEAF iso. All Jacobian units and their source/target frame laws are derived
internally from the original coordinates, not compatibility certificates. -/
theorem smooth_effectiveCartier_local_adjunction_coordinate_independent
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
    (x' : MvPolynomial (Fin (1 + r)) K →ₐ[K] Γ(X, cX.U))
    (hx' : x'.toRingHom.FormallyEtale)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ((effectiveCartierIdealSheaf D hD).subscheme,
        (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale)
    (y' : MvPolynomial (Fin r) K →ₐ[K]
      Γ((effectiveCartierIdealSheaf D hD).subscheme,
        (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U))
    (hy' : y'.toRingHom.FormallyEtale) :
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
    let cX' : EtaleChart K X (1 + r) := { cX with coords := x', formallyEtale := hx' }
    let cY' : EtaleChart K Y r := { cY with coords := y', formallyEtale := hy' }
    let KX := canonicalDivisor (1 + r) cX₀ hX
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
    let e := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + D) i cX.U
        (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg)
        (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq))
    let e' := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + D) i cX.U
        (etaleChartCanonicalEquation cX₀ cX' * regularEquationRationalUnit X cX.U g hg)
        (canonicalPlusCartier_local_equation cX₀ hX cX' D g hg hEq))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    let d' := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY')
      (canonicalDivisor_restrict cY₀ hY cY').symm
    ∃ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
      (a a' : Bˣ) (Φ : M.over V ≅ KY.sheaf.over V),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A g) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis x' hx')) =
          (a' : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y' hy') ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e d a ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e' d' a' ∧
      ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (moduleOverFrameCoefficient KY.sheaf V d' W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a' * moduleOverFrameCoefficient M V e' W hWV s) := by
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
  let cX' : EtaleChart K X (1 + r) := { cX with coords := x', formallyEtale := hx' }
  let cY' : EtaleChart K Y r := { cY with coords := y', formallyEtale := hy' }
  let KX := canonicalDivisor (1 + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
  let e := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg)
      (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq))
  let e' := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U
      (etaleChartCanonicalEquation cX₀ cX' * regularEquationRationalUnit X cX.U g hg)
      (canonicalPlusCartier_local_equation cX₀ hX cX' D g hg hEq))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  let : Algebra.FormallySmooth K A := formallySmooth_of_etale_coordinates cX.coords cX.formallyEtale
  let : Algebra.FormallySmooth K B := formallySmooth_of_etale_coordinates y hy
  let d' := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY')
    (canonicalDivisor_restrict cY₀ hY cY').symm
  let b : Module.Basis (Fin (1 + r)) A Ω[A⁄K] :=
    etaleCoordinateBasis cX.coords cX.formallyEtale
  let b' : Module.Basis (Fin (1 + r)) A Ω[A⁄K] := etaleCoordinateBasis x' hx'
  let c : Module.Basis (Fin r) B Ω[B⁄K] := etaleCoordinateBasis y hy
  let c' : Module.Basis (Fin r) B Ω[B⁄K] := etaleCoordinateBasis y' hy'
  let uX : Aˣ := (Module.Basis.isUnit_det b' b).unit
  let uY : Bˣ := (Module.Basis.isUnit_det c' c).unit
  obtain ⟨hreg, hsurj, hker⟩ := effectiveCartier_affine_principal_quotient_data D hD
    ⟨cX.U, cX.isAffine⟩ g hg hEq
  obtain ⟨R, _, hR, a, ha⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := A) (B := B) g hreg hsurj hker r b c
  obtain ⟨a', haval, ha'⟩ := pulled_canonical_residue_two_frame_transition b b' c c' R.toLinearMap a ha
  have hscalar : (a' : B) * i.app cX.U ↑uX = (uY : B) * (a : B) := by
    have hux : (uX : A) = b'.det b := IsUnit.unit_spec _
    have huy : (uY : B) = c'.det c := IsUnit.unit_spec _
    have hinv : b.det b' * b'.det b = (1 : A) :=
      (Module.Basis.det_mul_det b b' b).trans (Module.Basis.det_self b)
    change (a' : B) * algebraMap A B ↑uX = (uY : B) * (a : B)
    rw [haval, hux, huy]
    calc
      _ = (algebraMap A B (b.det b') * algebraMap A B (b'.det b)) *
          (c'.det c * (a : B)) := by ring
      _ = _ := by rw [← map_mul, hinv, map_one, one_mul]
  have hfx : etaleChartCanonicalEquation cX₀ cX' =
      Units.map (X.germToFunctionField cX.U).hom uX * etaleChartCanonicalEquation cX₀ cX :=
    etaleChartCanonicalEquation_same_open_change cX₀ cX x' hx'
  have hfy : etaleChartCanonicalEquation cY₀ cY' =
      Units.map (Y.germToFunctionField V).hom uY * etaleChartCanonicalEquation cY₀ cY :=
    etaleChartCanonicalEquation_same_open_change cY₀ cY y' hy'
  have hfunit :
      etaleChartCanonicalEquation cX₀ cX' * regularEquationRationalUnit X cX.U g hg =
        Units.map (X.germToFunctionField cX.U).hom uX *
          (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg) := by
    rw [hfx]
    exact mul_assoc _ _ _
  have he : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
      moduleOverFrameCoefficient M V e' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (i.app cX.U ↑uX) *
          moduleOverFrameCoefficient M V e W hWV s := by
    intro W hWV s
    exact cartierPullbackFrameCoefficient_unit_equation_change (KX + D) i cX.U
      _ _ (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq)
      (canonicalPlusCartier_local_equation cX₀ hX cX' D g hg hEq) uX hfunit W hWV s
  have hd : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(KY.sheaf, W)),
      moduleOverFrameCoefficient KY.sheaf V d' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (uY : B) *
          moduleOverFrameCoefficient KY.sheaf V d W hWV s := by
    intro W hWV s
    exact cartierOpenFrameCoefficient_unit_equation_change KY V _ _
      (canonicalDivisor_restrict cY₀ hY cY).symm
      (canonicalDivisor_restrict cY₀ hY cY').symm uY hfy W hWV s
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  have hΦ : moduleOverFrameWeightedIso M KY.sheaf V e' d' a' = Φ :=
    moduleWeightedFrameIso_cancel_both_changes M KY.sheaf V e e' d d' a a'
      (i.app cX.U ↑uX) (uY : B) hscalar he hd
  dsimp only
  refine ⟨R, a, a', Φ, hR, ha, ha', rfl, hΦ.symm, ?_⟩
  intro W hWV s
  constructor
  · exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
  · rw [← hΦ]
    exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e' d' a' W hWV s

end MixedFujita

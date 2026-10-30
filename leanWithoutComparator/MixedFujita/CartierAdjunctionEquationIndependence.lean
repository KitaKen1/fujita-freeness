/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPullbackEquationFrames

/-! 実局所標準随伴層同型の方程式独立性。 check-283：実商の全射性から微分の全持ち上げを内部供給し、純ambient dg楔積だけで実引き戻し標準加群の線形写像を検出することを証明。純正規化公式による留数の一意性、および任意に独立構成した二留数の方程式変更則を証明。同じ有効Cartier因子の二つの実正則方程式から、実イデアルの一致を通じて実単元を内部抽出。元のCartier係数と実線束pullback frameの全部分開の変換則を証明。実Cartier切断の同一affineチャート・固定座標の下で、二方程式から正規化留数とframe単元をそれぞれ内部構成し、逆向きの係数変化が打ち消し合うことから実局所標準随伴層同型の一致を構成。異なる座標・チャート間の一致、大域留数貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- Opposite changes of source frame and residue coefficient cancel in the
ACTUAL sheaf iso. This equality is on every subopen, not just one section ring. -/
theorem moduleWeightedFrameIso_cancel_source_change
    {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (e e' : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (d : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (a a' : Γ(X, U)ˣ) (v : Γ(X, U)) (hc : ↑a' * v = ↑a)
    (he : ∀ (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)),
      moduleOverFrameCoefficient M U e' W hWU s =
        X.presheaf.map (homOfLE hWU).op v * moduleOverFrameCoefficient M U e W hWU s) :
    moduleOverFrameWeightedIso M N U e' d a' = moduleOverFrameWeightedIso M N U e d a := by
  apply moduleOverFrameWeightedIso_unique
  intro W hWU s
  rw [moduleOverFrameWeightedIso_coefficient, he, ← mul_assoc, ← map_mul, hc]


/-- Two ACTUAL regular equations of the same Cartier cut produce the SAME
normalized local Cartier adjunction SHEAF iso. Equation unit, both residues,
both frame units and their cancellation are all constructed internally from
the original geometry; no unit-change or compatibility certificate is input. -/
theorem smooth_effectiveCartier_local_adjunction_equation_independent
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
    (g' : Γ(X, cX.U)) (hg' : g' ≠ 0)
    (hEq' : rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U g' hg')) = D |_ cX.U)
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
    let e' := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + D) i cX.U
        (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g' hg')
        (canonicalPlusCartier_local_equation cX₀ hX cX D g' hg' hEq'))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    ∃ (R R' : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
      (a a' : Bˣ) (Φ : M.over V ≅ KY.sheaf.over V),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A g) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A g') z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a' : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e d a ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e' d a' ∧
      ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
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
  let KX := canonicalDivisor (1 + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
  let e := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg)
      (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq))
  let e' := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g' hg')
      (canonicalPlusCartier_local_equation cX₀ hX cX D g' hg' hEq'))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  let : Algebra.FormallySmooth K A := formallySmooth_of_etale_coordinates cX.coords cX.formallyEtale
  let : Algebra.FormallySmooth K B := formallySmooth_of_etale_coordinates y hy
  obtain ⟨u, hu⟩ := effectiveCartier_affine_equations_unit D hD
    ⟨cX.U, cX.isAffine⟩ g g' hg hg' hEq hEq'
  obtain ⟨hreg, hsurj, hker⟩ := effectiveCartier_affine_principal_quotient_data D hD
    ⟨cX.U, cX.isAffine⟩ g hg hEq
  obtain ⟨hreg', hsurj', hker'⟩ := effectiveCartier_affine_principal_quotient_data D hD
    ⟨cX.U, cX.isAffine⟩ g' hg' hEq'
  obtain ⟨R, _, hR, a, ha⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := A) (B := B) g hreg hsurj hker r
      (etaleCoordinateBasis cX.coords cX.formallyEtale) (etaleCoordinateBasis y hy)
  obtain ⟨R', _, hR', a', ha'⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := A) (B := B) g' hreg' hsurj' hker' r
      (etaleCoordinateBasis cX.coords cX.formallyEtale) (etaleCoordinateBasis y hy)
  have hgzero : algebraMap A B g = 0 := RingHom.mem_ker.mp
    (hker ▸ Ideal.mem_span_singleton_self g)
  have hRunit : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A (↑u * g)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
    intro z
    rw [← hu]
    exact hR' z
  have hres := pure_pulled_residue_equation_change g ↑u hgzero hsurj r
    (etaleCoordinateBasis cX.coords cX.formallyEtale) R R' hR hRunit
  have hscalar : (a' : B) * i.app cX.U ↑u = (a : B) := by
    have h := hres ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
      (etaleCoordinateBasis cX.coords cX.formallyEtale))
    rw [map_smul, ha', ha] at h
    have hh : algebraMap A B ↑u * (a' : B) = (a : B) :=
      topExterior_wedge_smul_cancel (etaleCoordinateBasis y hy)
        (by simpa only [smul_smul] using h)
    change (a' : B) * algebraMap A B ↑u = (a : B)
    rw [mul_comm]
    exact hh
  have hfunit :
      etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g' hg' =
        Units.map (X.germToFunctionField cX.U).hom u *
          (etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg) := by
    apply Units.ext
    simp only [Units.val_mul, regularEquationRationalUnit_val, Units.coe_map]
    rw [hu, map_mul]
    exact mul_left_comm _ _ _
  have he : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
      moduleOverFrameCoefficient M V e' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (i.app cX.U ↑u) *
          moduleOverFrameCoefficient M V e W hWV s := by
    intro W hWV s
    exact cartierPullbackFrameCoefficient_unit_equation_change (KX + D) i cX.U
      _ _ (canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq)
      (canonicalPlusCartier_local_equation cX₀ hX cX D g' hg' hEq') u hfunit W hWV s
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  have hΦ : moduleOverFrameWeightedIso M KY.sheaf V e' d a' = Φ :=
    moduleWeightedFrameIso_cancel_source_change M KY.sheaf V e e' d a a'
      (i.app cX.U ↑u) hscalar he
  dsimp only
  refine ⟨R, R', a, a', Φ, hR, hR', ha, ha', rfl, hΦ.symm, ?_⟩
  intro W hWV s
  constructor
  · exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
  · rw [← hΦ]
    exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e' d a' W hWV s

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveNumericalTrivialityCurves
public import MixedFujita.NumericalTrivialityPullback
public import MixedFujita.KodairaLemmaStatementProof

/-! 特異射影整スキーム上の数値自明非零切断の主因子性。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower


theorem projective_numericallyTrivial_nonzero_section_unit
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    IsUnit (cartierLocalCoefficient D x f hf s) := by
  obtain ⟨H, hH⟩ := hproj
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    obtain ⟨_, _, b, e, _, he, _⟩ := hH
    have := polynomialProjectiveToBase_isProper b K
    rw [← he]
    infer_instance
  obtain ⟨cX⟩ := nonempty_etaleChart_of_charZero (K := K) hdim
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hG, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cX 1 1 0 (fun _ : Fin 0 => 0) hH
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdimT : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  have hDT := cartierIsNumericallyTrivial_pullback_of_nonzero_section ρ D hD s hs
  have hsT := cartierDominantPullbackSection_ne_zero ρ D s hs
  obtain ⟨bT, eT, hclosedT, hbaseT, _⟩ := hJ
  let := hclosedT
  obtain ⟨t, rfl⟩ := surjective_of_isProper_of_isDominant ρ x
  apply (isUnit_map_iff (ρ.stalkMap t).hom _).mp
  rw [← cartierDominantPullbackSection_localCoefficient ρ D s t f hf]
  exact polynomialProjective_numericallyTrivial_nonzero_section_unit eT hbaseT n hdimT hn
    (cartierPullback ρ D) hDT (cartierDominantPullbackSection ρ D s) hsT t _ _


theorem projective_numericallyTrivial_principal_of_nonzero_section
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ :=
  principal_of_section_everywhere_unit D s hs
    (projective_numericallyTrivial_nonzero_section_unit hdim hn hproj D hD s hs)

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteTypeClosedPointEvaluation
public import MixedFujita.ProjectiveNumericallyTrivialSections

/-! 全正次元・特異源での数値自明全倍数切断空間の有限性と次元1上界。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

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

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
  (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
include hdim hn hproj


theorem projective_numericallyTrivial_graded_sections_bound
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D) (j : ℕ) :
    FiniteDimensional K Γ((j • D).sheaf, ⊤) ∧
      Module.finrank K Γ((j • D).sheaf, ⊤) ≤ 1 := by
  obtain ⟨H, hH⟩ := hproj
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    obtain ⟨_, _, b, e, _, he, _⟩ := hH
    have := polynomialProjectiveToBase_isProper b K
    rw [← he]
    infer_instance
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, Set.mem_univ _⟩
  obtain ⟨β⟩ := finiteTypeScheme_closedPoint_has_localEvaluation (K := K) x hx
  obtain ⟨f, hf⟩ := (j • D).exists_isLocalEquationAt x
  let L : Γ((j • D).sheaf, ⊤) →ₗ[K] K := β.toLinearMap.comp
    ((cartierLocalCoefficient (j • D) x f hf).restrictScalars K)
  have hinj : Function.Injective L := by
    intro a b hab
    by_contra hne
    have hu := projective_numericallyTrivial_nonzero_section_unit hdim hn ⟨H, hH⟩
      (j • D) (cartierIsNumericallyTrivial_nsmul hD j) (a - b) (sub_ne_zero.mpr hne) x f hf
    have hz : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact (hu.map β.toRingHom).ne_zero hz

  have hfin := FiniteDimensional.of_injective L hinj
  exact ⟨hfin, by simpa using LinearMap.finrank_le_finrank_of_injective hinj⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointIdealGenerators
public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.SmoothClosedPoints

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierBaseOpenAlgebra cartierBaseLocalAlgebra cartierBaseGlobalAlgebra
variable {K : Type u} [Field K] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {n : ℕ}
noncomputable def projectivePointedChartEquationLinear
    (e : Y ⟶ polynomialProjectiveScheme n K)
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (x : Y) (k : Fin n) :
    polynomialProjectiveVanishingForms 1 (e x) →ₗ[K]
      Γ(Y, projectivePullbackCoordinateOpen e k) where
  toFun := projectivePointedChartEquation e x k
  map_add' f g := by
    change projectivePullbackHomogeneousEquation e k 1 (f.val.val + g.val.val) _ = _
    simp only [← projectivePullbackAffinePolynomialMap_dehomogenize, map_add,
      projectivePointedChartEquation]
  map_smul' a f := by
    change projectivePullbackHomogeneousEquation e k 1 (a • f.val.val) _ =
      a • projectivePullbackHomogeneousEquation e k 1 f.val.val _
    simp only [← projectivePullbackAffinePolynomialMap_dehomogenize,
      MvPolynomial.algebraMap_eq, map_mul, projectiveDehomogenize_C,
      projectivePullbackAffinePolynomialMap_C_eq_algebraMap e he k, Algebra.smul_def]

theorem ideal_span_linearMap_basis {K R M ι : Type*} [Field K] [CommRing R]
    [Algebra K R] [AddCommMonoid M] [Module K M] [Fintype ι]
    (b : Module.Basis ι K M) (φ : M →ₗ[K] R) :
    Ideal.span (Set.range fun i => φ (b i)) = Ideal.span (Set.range φ) := by
  classical
  apply le_antisymm
  · apply Ideal.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨m, rfl⟩
    rw [← b.sum_repr m, map_sum]
    apply Ideal.sum_mem
    intro i _
    rw [map_smul]
    exact (Ideal.span (Set.range fun i => φ (b i))).restrictScalars K |>.smul_mem
      (b.repr m i) (Ideal.subset_span (Set.mem_range_self i))

theorem projectivePointedChartEquation_span
    [IsAlgClosed K] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (k : Fin n) (x : Y) (hx : IsClosed {x}) :
    Ideal.span (Set.range (projectivePointedChartEquation e x k)) =
      (pointClosureIdeal x).ideal ⟨projectivePullbackCoordinateOpen e k,
        projectivePullbackCoordinateOpen_isAffineOpen e k⟩ := by
  by_cases hxk : x ∈ projectivePullbackCoordinateOpen e k
  · exact projectivePointedChartEquation_span_of_mem e he k x hx hxk
      (smoothAffineClosedPointEvaluation (K := K)
        (projectivePullbackCoordinateOpen_isAffineOpen e k) x hxk hx)
  · rw [projectivePointedChartEquation_span_of_notMem e k x hxk,
      pointClosureIdeal_affine_of_notMem x hx _ hxk]

theorem projectivePointedBasis_restricted_span
    [IsAlgClosed K] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (x : Y) (hx : IsClosed {x}) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι K (polynomialProjectiveVanishingForms 1 (e x)))
    (k : Fin n) (U : Y.affineOpens) (hU : U.1 ≤ projectivePullbackCoordinateOpen e k) :
    Ideal.span (Set.range fun i => Y.presheaf.map (homOfLE hU).op
      (projectivePointedChartEquation e x k (b i))) = (pointClosureIdeal x).ideal U := by
  have hb := ideal_span_linearMap_basis b (projectivePointedChartEquationLinear e he x k)
  change Ideal.span (Set.range fun i => projectivePointedChartEquation e x k (b i)) =
      Ideal.span (Set.range (projectivePointedChartEquation e x k)) at hb
  rw [← (pointClosureIdeal x).map_ideal (U := U)
      (V := ⟨projectivePullbackCoordinateOpen e k, projectivePullbackCoordinateOpen_isAffineOpen e k⟩) hU,
    ← projectivePointedChartEquation_span e he k x hx, ← hb, Ideal.map_span, ← Set.range_comp']
  rfl

theorem projectivePointedBasis_restricted_pointed_or_free
    [IsAlgClosed K] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (x : Y) (hx : IsClosed {x}) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι K (polynomialProjectiveVanishingForms 1 (e x)))
    (k : Fin n) (U : Y.affineOpens) (hU : U.1 ≤ projectivePullbackCoordinateOpen e k) :
    Ideal.span (Set.range fun i => Y.presheaf.map (homOfLE hU).op
      (projectivePointedChartEquation e x k (b i))) = ⊤ ∨
    ∃ β : Γ(Y, U.1) →ₐ[K] K, Ideal.span (Set.range fun i =>
      Y.presheaf.map (homOfLE hU).op (projectivePointedChartEquation e x k (b i))) =
      RingHom.ker β.toRingHom := by
  rw [projectivePointedBasis_restricted_span e he x hx b k U hU]
  by_cases hxx : x ∈ U.1
  · exact Or.inr ⟨rationalAffineGermPoint x hxx
        (smoothAffineClosedPointEvaluation (K := K) U.2 x hxx hx),
      pointClosureIdeal_affine_eq_evaluation_kernel x hx U hxx _⟩
  · exact Or.inl (pointClosureIdeal_affine_of_notMem x hx U hxx)

end MixedFujita

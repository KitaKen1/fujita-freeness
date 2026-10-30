/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PointClosureAffineIdeal
public import MixedFujita.PolynomialPointKernelGenerators
public import MixedFujita.ProjectiveChartGenerators
public import MixedFujita.PointedProjectiveFormAvoidance

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierBaseOpenAlgebra cartierBaseLocalAlgebra
  cartierBaseGlobalAlgebra
variable {K : Type u} [Field K] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {n : ℕ}

theorem projectivePullback_pointed_form_evaluation
    (e : Y ⟶ polynomialProjectiveScheme n K) (k : Fin n)
    (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
    (β : Y.presheaf.stalk x →ₐ[K] K)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous 1) :
    f ∈ (e x).asHomogeneousIdeal ↔
      rationalAffineGermPoint x hxk β
        (projectivePullbackHomogeneousEquation e k 1 f hf) = 0 := by
  have hne : rationalAffineGermPoint x hxk β
      (projectivePullbackHomogeneousEquation e k 1 f hf) ≠ 0 ↔
      f ∉ (e x).asHomogeneousIdeal := by
    change β (Y.presheaf.germ _ x hxk
      (projectivePullbackHomogeneousEquation e k 1 f hf)) ≠ 0 ↔ _
    rw [← rationalLocalPoint_isUnit_iff β, ← Y.mem_basicOpen _ x hxk,
      projectivePullbackHomogeneousEquation_basicOpen e k 1 f hf Nat.zero_lt_one]
    exact and_iff_right hxk
  simpa only [not_not] using (not_congr hne).symm

noncomputable def projectivePointedChartEquation
    (e : Y ⟶ polynomialProjectiveScheme n K) (x : Y) (k : Fin n)
    (f : polynomialProjectiveVanishingForms 1 (e x)) :
    Γ(Y, projectivePullbackCoordinateOpen e k) :=
  projectivePullbackHomogeneousEquation e k 1 f.val.val f.val.property

theorem projectivePointedChartEquation_span_of_mem
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (k : Fin n) (x : Y) (hx : IsClosed {x})
    (hxk : x ∈ projectivePullbackCoordinateOpen e k)
    (β : Y.presheaf.stalk x →ₐ[K] K) :
    Ideal.span (Set.range (projectivePointedChartEquation e x k)) =
      (pointClosureIdeal x).ideal ⟨projectivePullbackCoordinateOpen e k,
        projectivePullbackCoordinateOpen_isAffineOpen e k⟩ := by
  let φ : MvPolynomial {j : Fin n // j ≠ k} K →ₐ[K]
      Γ(Y, projectivePullbackCoordinateOpen e k) := {
    __ := projectivePullbackAffinePolynomialMap e k
    commutes' := projectivePullbackAffinePolynomialMap_C_eq_algebraMap e he k }
  let α := rationalAffineGermPoint x hxk β
  rw [pointClosureIdeal_affine_eq_evaluation_kernel x hx _ hxk β]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact (projectivePullback_pointed_form_evaluation e k x hxk β f.val.val
      f.val.property).mp f.property
  · rw [polynomial_surjection_point_kernel_generators φ
      (projectivePullbackAffinePolynomialMap_surjective e k) α, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    let f := MvPolynomial.X i.val - MvPolynomial.C (α (φ (MvPolynomial.X i))) * MvPolynomial.X k
    have hf : f.IsHomogeneous 1 :=
      (MvPolynomial.isHomogeneous_X K i.val).sub
        ((MvPolynomial.isHomogeneous_X K k).C_mul _)
    have hcoef : projectivePullbackHomogeneousEquation e k 1 f hf =
        φ (MvPolynomial.X i) - algebraMap K _ (α (φ (MvPolynomial.X i))) := by
      rw [← projectivePullbackAffinePolynomialMap_dehomogenize]
      simp only [f, map_sub, map_mul, projectiveDehomogenize_X_other,
        projectiveDehomogenize_C, projectiveDehomogenize_X_self, mul_one]
      rw [projectivePullbackAffinePolynomialMap_C_eq_algebraMap e he k]
      rfl
    have hfx : f ∈ (e x).asHomogeneousIdeal := by
      apply (projectivePullback_pointed_form_evaluation e k x hxk β f hf).mpr
      rw [hcoef]
      change α (φ (MvPolynomial.X i) - algebraMap K _ (α (φ (MvPolynomial.X i)))) = 0
      simp
    change φ (MvPolynomial.X i) - algebraMap K _ (α (φ (MvPolynomial.X i))) ∈ _
    rw [← hcoef]
    exact Ideal.subset_span
      (Set.mem_range_self (⟨⟨f, hf⟩, hfx⟩ : polynomialProjectiveVanishingForms 1 (e x)))

omit [Y.Over (Spec (CommRingCat.of K))] in
theorem projectivePointedChartEquation_span_of_notMem
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (k : Fin n) (x : Y) (hxk : x ∉ projectivePullbackCoordinateOpen e k) :
    Ideal.span (Set.range (projectivePointedChartEquation e x k)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem : MvPolynomial.X k ∈ (e x).asHomogeneousIdeal := by
    simpa only [projectivePullbackCoordinateOpen, Scheme.Hom.mem_preimage,
      Proj.mem_basicOpen, not_not] using hxk
  let f : polynomialProjectiveVanishingForms 1 (e x) :=
    ⟨⟨MvPolynomial.X k, MvPolynomial.isHomogeneous_X K k⟩, hmem⟩
  have h : projectivePointedChartEquation e x k f ∈
      Ideal.span (Set.range (projectivePointedChartEquation e x k)) :=
    Ideal.subset_span (Set.mem_range_self f)
  have hf : projectivePointedChartEquation e x k f = 1 := by
    unfold projectivePointedChartEquation
    rw [← projectivePullbackAffinePolynomialMap_dehomogenize]
    simp only [f, projectiveDehomogenize_X_self, map_one]
  exact hf ▸ h

end MixedFujita

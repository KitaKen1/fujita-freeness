/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Hironaka.Resolution.Algebraic.Hir64.ComponentDeletion
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.BRAffinePullback
public import Hironaka.Scheme.Smooth.AdaptedCoordinates
public import Hironaka.Algebra.RegularSmooth.SmoothAt
public import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv
public import Mathlib.AlgebraicGeometry.Noetherian

/-! A regular Noetherian scheme has an actual integral open around every point. An actual smooth point over a field therefore has an integral smooth open neighborhood, expressed by an open immersion, using an affine neighborhood and its disjoint integral components. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem regularScheme_exists_integral_open {X : Scheme.{u}} [IsNoetherian X] [IsRegular X]
    (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsIntegral U := by
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hX := Hironaka.Sequence.hasDisjointIntegralComponents_of_isRegular (X := X)
  refine ⟨X.irreducibleComponentOpen C, ?_, ?_⟩
  · change x ∈ ((X.irreducibleComponentOpen C : X.Opens) : Set X)
    rw [hX.irreducibleComponentOpen_eq C hC]
    exact mem_irreducibleComponent
  · exact Hironaka.Resolution.isIntegral_irreducibleComponentOpen hX C hC

theorem smoothPoint_exists_integral_smooth_neighborhood
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    (x : X) (hx : x ∈ f.smoothLocus) :
    ∃ (T : Scheme.{u}) (j : T ⟶ X), IsOpenImmersion j ∧ IsIntegral T ∧
      Smooth (j ≫ f) ∧ ∃ t : T, j t = x := by
  obtain ⟨U, hxU, hU⟩ := (Scheme.Hom.mem_smoothLocus_iff_exists_smooth f).mp hx
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  let : IsAffine V := hV
  have hVf : Smooth (V.ι ≫ f) := by
    have : Smooth ((X.homOfLE hVU) ≫ U.ι ≫ f) := inferInstance
    simpa only [Scheme.homOfLE_ι_assoc] using this
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (V.ι ≫ f)
  let : IsNoetherian V := {}
  let : IsRegular V := ⟨fun y => isRegularLocalRing_stalk (V.ι ≫ f) y⟩
  obtain ⟨W, hxW, hW⟩ := regularScheme_exists_integral_open (X := V) (⟨x, hxV⟩ : V)
  refine ⟨W, W.ι ≫ V.ι, inferInstance, hW, ?_, ⟨⟨⟨x, hxV⟩, hxW⟩, rfl⟩⟩
  simpa only [Category.assoc] using (inferInstance : Smooth (W.ι ≫ V.ι ≫ f))

end MixedFujita
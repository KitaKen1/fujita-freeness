/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FirstOrderCartierCutSmoothness
public import MixedFujita.ProjectivePointedFirstOrderAvoidance
public import MixedFujita.GeometricSmoothTaylor
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! The actual pointed order-one projective cut has a regular stalk and a smooth open neighborhood at the prescribed closed point, while retaining finite avoidance and the original effective Cartier ideal. No global smoothness or integrality of the whole cut is asserted. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projectivePullbackCartierIdealSheaf_stalk_eq_span
    {R : Type u} [CommRing R] {Y : Scheme.{u}} [IsIntegral Y] {n : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme n R) [IsAffineHom e]
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hgeneric : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (k : Fin n) (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k) :
    (projectivePullbackCartierIdealSheaf e d f hf hd hgeneric).stalkIdeal x =
      Ideal.span (Set.singleton (Y.presheaf.germ _ x hxk
        (projectivePullbackHomogeneousEquation e k d f hf))) := by
  let j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨x, hxk⟩⟩⟩
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _
    (projectivePullbackNonemptyCoordinateAffineOpen e j) hxk,
    projectivePullbackCartierIdealSheaf_coordinate_ideal, Ideal.map_span, Set.image_singleton]
  rfl

theorem polynomialProjective_smooth_positive_dimension_pointed_smoothCut
    {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (hdim : 0 < topologicalKrullDim Y) (x : Y) (hx : IsClosed {x})
    (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        (∀ y ∈ Z, y ∉ Set.range I.subschemeι) ∧
        ∃ (z : I.subscheme) (U : I.subscheme.Opens), I.subschemeι z = x ∧ z ∈ U ∧
          Smooth (U.ι ≫ I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
          ringKrullDim (I.subscheme.presheaf.stalk z) + 1 =
            ringKrullDim (Y.presheaf.stalk x) := by
  obtain ⟨k, hxk, f, hgeneric, hpres, hxI, havoid, horder⟩ :=
    polynomialProjective_smooth_positive_dimension_pointed_order_one_effectiveCartierCut
      e hdim x hx Z hZ hxZ
  let I := projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hgeneric
  refine ⟨f, hgeneric, hpres, havoid, ?_⟩
  obtain ⟨z, rfl⟩ := hxI
  let := isRegularLocalRing_stalk (Y ↘ Spec (CommRingCat.of K)) (I.subschemeι z)
  have hI := projectivePullbackCartierIdealSheaf_stalk_eq_span e 1 f.val f.property
    Nat.zero_lt_one hgeneric k (I.subschemeι z) hxk
  obtain ⟨U, hzU, hU⟩ := subscheme_exists_smooth_open_of_stalk_order_one
    (Y ↘ Spec (CommRingCat.of K)) I z _ hI horder
  exact ⟨z, U, rfl, hzU, hU, subscheme_stalk_dimension_drop_of_order_one I z _ hI horder⟩

end MixedFujita
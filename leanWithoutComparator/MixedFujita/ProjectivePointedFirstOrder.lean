/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialLocalLinearGenerators
public import MixedFujita.ProjectiveClosedPointLinearGeneration
public import MixedFujita.PositiveDimensionPointedCartier
public import MixedFujita.SmoothSchemeCoordinates
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
An actual closed projective immersion gives a surjective affine polynomial
presentation. At a closed point of positive local dimension, one degree-one
form has actual local order exactly one. For a smooth integral positive
dimensional source, the local dimension and Noetherian hypotheses are derived.
This supplies the base-point first-order condition for pointed Bertini,
not smoothness or integrality of the whole cut or finite avoidance.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n K)

noncomputable def projectivePullbackAffinePolynomialMap (k : Fin n) :
    MvPolynomial {j : Fin n // j ≠ k} K →+*
      Γ(Y, projectivePullbackCoordinateOpen e k) :=
  (e.app _).hom.comp ((Proj.awayToSection
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)).hom.comp
      (projectiveChartAffineToLocalization K k))

theorem projectivePullbackAffinePolynomialMap_surjective [IsClosedImmersion e] (k : Fin n) :
    Function.Surjective (projectivePullbackAffinePolynomialMap e k) := by
  have hU := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one
  let a := Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin n) K)
    (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one
  have ha : Function.Surjective (Proj.awayToSection
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)) := by
    simpa only [a, Proj.basicOpenIsoAway_hom] using
      (ConcreteCategory.bijective_of_isIso a.hom).2
  exact (e.app_surjective _ hU).comp (ha.comp (projectiveChartRingEquiv K k).symm.surjective)

theorem projectivePullbackAffinePolynomialMap_dehomogenize (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    projectivePullbackAffinePolynomialMap e k (projectiveDehomogenize K k f) =
      projectivePullbackHomogeneousEquation e k d f hf := by
  change e.app _ (Proj.awayToSection _ (MvPolynomial.X k)
    (projectiveChartAffineToLocalization K k (projectiveDehomogenize K k f))) = _
  rw [projectiveChartAffineToLocalization_dehomogenize K k d f hf]
  rfl

theorem projectivePullback_order_one_mem_point [IsIntegral Y]
    (k : Fin n) (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
    (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
    (h : localAdicOrder (Y.presheaf.stalk x)
      (Y.presheaf.germ _ x hxk
        (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1) :
    f.val ∈ (e x).asHomogeneousIdeal ∧
      f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal := by
  let U := projectivePullbackCoordinateOpen e k
  let s := projectivePullbackHomogeneousEquation e k 1 f.val f.property
  let : Nonempty U := ⟨⟨x, hxk⟩⟩
  have hm : Y.presheaf.germ U x hxk s ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
    simpa only [pow_one] using ((localAdicOrder_eq_nat_iff _ 1).mp h).1
  have hs : s ≠ 0 := by
    intro hz
    have hsq := ((localAdicOrder_eq_nat_iff _ 1).mp h).2
    change Y.presheaf.germ U x hxk s ∉ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ 2 at hsq
    rw [hz, map_zero] at hsq
    exact hsq (Ideal.zero_mem _)
  constructor
  · by_contra hn
    have hb : x ∈ Y.basicOpen s := by
      rw [projectivePullbackHomogeneousEquation_basicOpen e k 1 f.val f.property Nat.zero_lt_one]
      exact ⟨hxk, hn⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ((Y.mem_basicOpen s x hxk).mp hb)
  · have hg : genericPoint Y ∈ U := integral_genericPoint_mem_nonempty_open U
    have hgn : Y.presheaf.germ U (genericPoint Y) hg s ≠ 0 := by
      intro hz
      apply hs
      apply germ_injective_of_isIntegral Y (genericPoint Y) hg
      simpa only [map_zero] using hz
    have hu : IsUnit (Y.presheaf.germ U (genericPoint Y) hg s) :=
      (isUnit_iff_ne_zero (G₀ := Y.functionField)).mpr hgn
    have hb := (Y.mem_basicOpen s (genericPoint Y) hg).mpr hu
    rw [projectivePullbackHomogeneousEquation_basicOpen e k 1 f.val f.property Nat.zero_lt_one] at hb
    exact hb.2

variable [IsAlgClosed K] [IsClosedImmersion e]

theorem polynomialProjective_closedImmersion_local_exists_order_one_form
    (k : Fin n) (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
    (hx : IsClosed {x}) [IsNoetherianRing (Y.presheaf.stalk x)]
    (hdim : ringKrullDim (Y.presheaf.stalk x) ≠ 0) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
        (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1 := by
  let U := projectivePullbackCoordinateOpen e k
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one).preimage e
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨x, hxk⟩ : U)
  let p := (hU.primeIdealOf ⟨x, hxk⟩).asIdeal
  let : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxk⟩ hx
  let : IsLocalization.AtPrime (Y.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hxk⟩
  obtain ⟨a, i, hi⟩ := polynomial_quotient_localization_exists_order_one_coordinate
    (S := Y.presheaf.stalk x) (projectivePullbackAffinePolynomialMap e k)
      (projectivePullbackAffinePolynomialMap_surjective e k) p hdim
  let f := MvPolynomial.X i.val - MvPolynomial.C (a i) * MvPolynomial.X k
  have hf : f.IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X K i.val).sub ((MvPolynomial.isHomogeneous_X K k).C_mul (a i))
  have hd : projectiveDehomogenize K k f = MvPolynomial.X i - MvPolynomial.C (a i) := by
    simp only [f, map_sub, map_mul, projectiveDehomogenize_X_other,
      projectiveDehomogenize_C, projectiveDehomogenize_X_self, mul_one]
  have hmap := projectivePullbackAffinePolynomialMap_dehomogenize e k 1 f hf
  rw [hd] at hmap
  refine ⟨⟨f, hf⟩, ?_⟩
  change localAdicOrder (Y.presheaf.stalk x)
    ((algebraMap Γ(Y, U) (Y.presheaf.stalk x))
      (projectivePullbackHomogeneousEquation e k 1 f hf)) = 1
  rw [← hmap]
  exact hi

theorem polynomialProjective_smooth_positive_dimension_exists_pointed_order_one_form
    [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (hdim : 0 < topologicalKrullDim Y) (x : Y) (hx : IsClosed {x}) :
    ∃ (k : Fin n) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
      (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1),
      f.val ∈ (e x).asHomogeneousIdeal ∧
        f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
        localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
          (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1 := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let := smoothScheme_stalk_isNoetherianRing (K := K) x
  have hd : ringKrullDim (Y.presheaf.stalk x) ≠ 0 := by
    rw [TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
      (Y ↘ Spec (CommRingCat.of K)) hx]
    exact ne_of_gt hdim
  obtain ⟨f, hf⟩ := polynomialProjective_closedImmersion_local_exists_order_one_form e k x hk hx hd
  have hm := projectivePullback_order_one_mem_point e k f x hk hf
  exact ⟨k, hk, f, hm.1, hm.2, hf⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedEulerDifference
public import MixedFujita.CartierCurveIntrinsicDegree

/-! 実曲線次数による混合Euler係数の規格化と全高階差分消滅。 See reports/check-219-mixed-euler-intersection-foundation.json for the verified scope. The ordinary mixed-intersection dimension bound in dimension at least two remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On an actual proper smooth integral curve the full first Euler difference
is the existing intrinsic Cartier degree, independently of the base twist. -/
theorem properSmoothCurve_cartierMixedEulerDifference_singleton_eq_degree
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 1) (H E : CartierDivisor X) :
    cartierMixedEulerDifference K [H] E = properCurveCartierDegree (K := K) hdim H := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hdim2 : topologicalKrullDim X < 2 := by rw [hdim]; norm_num
  have hdegree (D : CartierDivisor X) :
      properCurveCartierDegree (K := K) hdim D =
        Scheme.Modules.eulerCharBelow K X D.sheaf 2 -
          Scheme.Modules.eulerCharBelow K X (SheafOfModules.unit X.ringCatSheaf) 2 := by
    rw [properSmoothCurveCartierDegree_eq_eulerDegree,
      TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_eq_sub_unit,
      CartierDivisor.toInvertibleSheaf_obj]
  have hadd := properCurveCartierDegree_add (K := K) hdim E H
  rw [hdegree (E + H), hdegree E, hdegree H] at hadd
  change Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + H).sheaf -
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) E.sheaf = _
  rw [moduleEulerChar_eq_eulerCharBelow_of_dim_lt K _ 2 hdim2,
    moduleEulerChar_eq_eulerCharBelow_of_dim_lt K _ 2 hdim2, hdegree H]
  omega


/-- Every mixed Cartier Euler difference of order at least two vanishes on an
actual proper smooth curve. This proves the dimension-one geometric nilpotence. -/
theorem properSmoothCurve_cartierMixedEulerDifference_two_or_more_vanishes
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 1) (D : List (CartierDivisor X))
    (H J E : CartierDivisor X) :
    cartierMixedEulerDifference K (H :: J :: D) E = 0 := by
  induction D generalizing E with
  | nil =>
    rw [cartierMixedEulerDifference_cons,
      properSmoothCurve_cartierMixedEulerDifference_singleton_eq_degree K hdim J (E + H),
      properSmoothCurve_cartierMixedEulerDifference_singleton_eq_degree K hdim J E,
      sub_self]
  | cons F D ih =>
    have hp : (H :: J :: F :: D).Perm (F :: H :: J :: D) :=
      (List.Perm.cons H (List.Perm.swap F J D)).trans (List.Perm.swap F H (J :: D))
    rw [cartierMixedEulerDifference_perm K hp E, cartierMixedEulerDifference_cons,
      ih (E + F), ih E, sub_self]

end MixedFujita

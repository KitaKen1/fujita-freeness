/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwoAffineCohomology

/-!
H0 and H1 of any actual invertible sheaf on a proper smooth integral curve
are finite over the base field. Given a two-affine-open cover, all higher
degrees vanish, so all degrees are finite and every Euler truncation at least
two computes the intrinsic pullback degree. No cohomology premise is supplied.
Existence of the two affine opens is not proved here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
universe u

theorem invertibleModule_isQuasicoherent {Y : Scheme.{u}} (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M] : M.IsQuasicoherent := by
  let F : _root_.SheafOfModules Y.ringCatSheaf := M
  let : F.IsLocallyFree := inferInstance
  exact inferInstanceAs F.IsQuasicoherent

theorem properTwoAffine_invertible_cohomology_vanish
    {K : Type u} [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology M q) := by
  let := invertibleModule_isQuasicoherent M
  exact properTwoAffine_cohomology_vanish (K := K) M hU hV hUV q hq

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
  [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_finiteDimensional_invertible_cohomology_lt_two
    (hY : topologicalKrullDim Y = 1) (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    (q : ℕ) (hq : q < 2) : FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : ∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint Y,
      IsDiscreteValuationRing (Y.presheaf.stalk (y : Y)) := fun y ↦
    smoothOverField_codimensionOne_stalk_DVR (K := K) y
  let := properSmoothCurve_finiteDimensional_cohomologyOne (K := K) hY
  have hdim (y : Y) : coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hY.le
  let L : InvertibleSheaf Y := ⟨M, inferInstance⟩
  rcases q with _ | q
  · exact InvertibleSheaf.finiteDimensional_cohomology_zero K hdim L
  · have : q = 0 := by omega
    subst q
    exact InvertibleSheaf.finiteDimensional_cohomology_one K hdim L

theorem properSmoothTwoAffineCurve_finiteDimensional_invertible_cohomology
    (hY : topologicalKrullDim Y = 1) (M : Y.Modules)
    [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M]
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (q : ℕ) : FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  by_cases hq : q < 2
  · exact properSmoothCurve_finiteDimensional_invertible_cohomology_lt_two hY M q hq
  · let := invertibleModule_isQuasicoherent M
    let := properTwoAffine_cohomology_vanish (K := K) M hU hV hUV q (by omega)
    infer_instance

variable {X : Scheme.{u}} [IsIntegral X]

theorem properSmoothTwoAffineCurve_finiteDimensional_cartierPullback_cohomology
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (q : ℕ) : FiniteDimensional K
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) q) := by
  let : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y
      ((Scheme.Modules.pullback φ).obj D.sheaf) := by
    rw [← cartierPullbackLineBundle_obj D φ]
    infer_instance
  exact properSmoothTwoAffineCurve_finiteDimensional_invertible_cohomology
    hY _ hU hV hUV q

omit [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem cartierCurvePullbackDegree_eq_eulerDifference_of_twoAffine
    (D : CartierDivisor X) (φ : Y ⟶ X)
    {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ⊔ V = ⊤) (n : ℕ) (hn : 2 ≤ n) :
    cartierCurvePullbackDegree (K := K) D φ =
      Scheme.Modules.eulerCharBelow K Y ((Scheme.Modules.pullback φ).obj D.sheaf) n -
        Scheme.Modules.eulerCharBelow K Y (SheafOfModules.unit Y.ringCatSheaf) n := by
  let : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y
      ((Scheme.Modules.pullback φ).obj D.sheaf) := by
    rw [← cartierPullbackLineBundle_obj D φ]
    infer_instance
  let := invertibleModule_isQuasicoherent ((Scheme.Modules.pullback φ).obj D.sheaf)
  let := invertibleModule_isQuasicoherent (SheafOfModules.unit Y.ringCatSheaf)
  exact cartierCurvePullbackDegree_eq_eulerCharBelowDifference D φ n hn
    (fun q hq _ ↦ properTwoAffine_cohomology_vanish (K := K) _ hU hV hUV q hq)
    (fun q hq _ ↦ properTwoAffine_cohomology_vanish (K := K) _ hU hV hUV q hq)

end MixedFujita

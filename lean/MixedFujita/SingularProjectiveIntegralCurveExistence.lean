/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PositiveDimensionPointedCartier
public import MixedFujita.ProjectiveCurveCohomology
public import MixedFujita.EffectiveCartierCutPureDimension

/-! 特異な正次元整射影源から実Cartier次元降下で整閉曲線を内部構成。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- An actual integral projective scheme of positive ordinary dimension
contains an ACTUAL integral closed curve, even when the source is singular.
Only the one-dimensional component is selected after each nonreduced cut. -/
theorem polynomialProjective_exists_integral_closed_curve
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {M : ℕ}
    (e : X ⟶ polynomialProjectiveScheme M K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase M K = X ↘ Spec (CommRingCat.of K))
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X), IsIntegral C ∧ IsClosedImmersion i ∧ topologicalKrullDim C = 1 := by
  induction n using Nat.strong_induction_on generalizing X M with
  | h n ih =>
    by_cases hn1 : n = 1
    · exact ⟨X, 𝟙 X, inferInstance, inferInstance, by simpa [hn1] using hdim⟩
    have hn2 : 2 ≤ n := by omega
    let : IsProper (X ↘ Spec (CommRingCat.of K)) :=
      polynomialProjective_closedImmersion_isProper_over_field e he
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
    obtain ⟨x, hx, hxc⟩ := (isClosed_univ (X := X)).exists_closed_singleton ⟨genericPoint X, Set.mem_univ _⟩
    have hpos : 0 < topologicalKrullDim X := by rw [hdim]; exact_mod_cast (by omega : 0 < n)
    obtain ⟨f, hfg, hp, hxcut, havoid⟩ :=
      polynomialProjective_positive_dimension_pointed_effectiveCartierCut e hpos x hxc ∅ Set.finite_empty (Set.notMem_empty x)
    let G := projectivePullbackHomogeneousCartier e 1 f.val f.property one_pos hfg
    have hG : G.IsEffective := projectivePullbackHomogeneousCartier_isEffective e 1 f.val f.property one_pos hfg
    have hne : Nonempty (effectiveCartierIdealSheaf G hG).subscheme := by
      obtain ⟨z, hz⟩ := hxcut
      exact ⟨z⟩
    have hdim' : topologicalKrullDim X = ((n - 1) + 1 : ℕ) := by
      rw [hdim]
      exact_mod_cast (show n = n - 1 + 1 by omega)
    obtain ⟨T, j, hT, hj, hdimT⟩ :=
      effectiveCartierCut_nonempty_exists_integral_expected_dimension K (n - 1) hdim' G hG hne
    let := hT
    let := hj
    let k := j ≫ (effectiveCartierIdealSheaf G hG).subschemeι
    let : T.Over (Spec (CommRingCat.of K)) := ⟨k ≫ (X ↘ Spec (CommRingCat.of K))⟩
    have heT : (k ≫ e) ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K) := by
      change (k ≫ e) ≫ polynomialProjectiveToBase M K = k ≫ (X ↘ Spec (CommRingCat.of K))
      rw [Category.assoc, he]
    obtain ⟨C, i, hC, hi, hdimC⟩ := ih (n - 1) (by omega) (k ≫ e) heT hdimT (by omega)
    let := hi
    exact ⟨C, i ≫ k, hC, inferInstance, hdimC⟩

end MixedFujita

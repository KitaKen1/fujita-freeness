/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleCoherentMixedEulerNonnegative

/-! 非空零次元properスキームの実構造層Euler標数の厳密正値性。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- On EVERY nonempty proper zero-dimensional scheme, including a
nonreduced one, the full actual structure Euler characteristic is positive. -/
theorem proper_zeroDimensional_unitEulerChar_positive
    (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim Y ≤ 0) (hne : Nonempty Y) :
    0 < Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) (CohomologyAux.unitModule Y) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let O : Y.Modules := CohomologyAux.unitModule Y
  let : FiniteDimensional K (Scheme.Modules.Cohomology O 0) := proper_invertible_cohomology_finite K O 0
  let e := Scheme.Modules.cohomologyZeroBaseLinearEquiv K Y O
  let : FiniteDimensional K Γ(O, ⊤) := Module.Finite.equiv e
  have hs : ∃ s : Γ(O, ⊤), s ≠ 0 := by
    refine ⟨(1 : Γ(Y, ⊤)), ?_⟩
    intro h
    let y := Classical.choice hne
    have hz := congrArg (Y.presheaf.germ ⊤ y (Opens.mem_top y)) h
    have hbad : (1 : Y.presheaf.stalk y) = 0 := by simpa only [map_one, map_zero] using hz
    exact one_ne_zero hbad
  have hpos : 0 < Module.finrank K (Scheme.Modules.Cohomology O 0) := by
    rw [e.finrank_eq]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr hs
  rw [moduleEulerChar_eq_eulerCharBelow_of_dim_lt K O 1
    (hdim.trans_lt (by norm_num : (0 : WithBot ℕ∞) < (1 : ℕ)))]
  simpa only [Scheme.Modules.eulerCharBelow_succ, Scheme.Modules.eulerCharBelow_zero,
    pow_zero, one_mul, zero_add] using (Int.natCast_pos.mpr hpos)


/-- The empty direction family and zero base with a unit coefficient
is literally the original structure Euler characteristic on any source. -/
theorem cartierPulledModuleMixedEulerDifference_empty_zero_unit
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X) :
    cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) [] 0 =
      Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) (CohomologyAux.unitModule Y) := by
  exact moduleEulerChar_congr K
    (tensorIso ((Scheme.Modules.pullback p).mapIso (cartierZeroSheafIso X) ≪≫
      Scheme.Modules.pullbackObjUnitIso p) (Iso.refl (CohomologyAux.unitModule Y)) ≪≫
      leftUnitor (CohomologyAux.unitModule Y))

end MixedFujita

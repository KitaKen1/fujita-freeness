/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperCartierCohomology
public import SGA.Foundations.Cohomology.EulerCharacteristicBasic

/-! 実基礎体線形Euler標数・有限打切りと完全列の加法性。 See reports/check-219-mixed-euler-intersection-foundation.json for the verified scope. The ordinary mixed-intersection dimension bound in dimension at least two remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The SGA Euler summands have the actual base-field-linear TauCeti cohomology dimensions. -/
theorem sgaFinrankH_eq_actual_finrank
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (M : X.Modules) (q : ℕ) :
    Scheme.Modules.finrankH (X ↘ Spec (CommRingCat.of K)) M q =
      Module.finrank K (Scheme.Modules.Cohomology M q) := by
  letI := M.moduleOver (X ↘ Spec (CommRingCat.of K)) q ⊤
  exact (sgaCohomologyBaseLinearEquiv K M q).finrank_eq


/-- The finite SGA Euler sum is exactly the actual TauCeti alternating sum,
without unfolding the external opaque definition. -/
theorem sgaEulerSum_eq_actual_eulerCharBelow
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (M : X.Modules) (n : ℕ) :
    (∑ q ∈ Finset.range n, (-1 : ℤ) ^ q *
      (Scheme.Modules.finrankH (X ↘ Spec (CommRingCat.of K)) M q : ℤ)) =
        Scheme.Modules.eulerCharBelow K X M n := by
  induction n with
  | zero => simp only [Finset.sum_range_zero, Scheme.Modules.eulerCharBelow_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, Scheme.Modules.eulerCharBelow_succ, ih,
      sgaFinrankH_eq_actual_finrank K M n]


/-- Full Euler characteristic agrees with the actual finite alternating sum
above the ordinary geometric dimension. -/
theorem moduleEulerChar_eq_eulerCharBelow_of_dim_lt
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [NoetherianSpace X] (M : X.Modules) (n : ℕ) (hn : topologicalKrullDim X < n) :
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) M =
      Scheme.Modules.eulerCharBelow K X M n := by
  rw [Scheme.Modules.eulerChar_eq_sum _ M (Finset.range n) (by
    intro q hq
    have hnq : n ≤ q := by simpa only [Finset.mem_range, not_lt] using hq
    let := actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt M q
      (hn.trans_le (by exact_mod_cast hnq))
    rw [sgaFinrankH_eq_actual_finrank K M q, Module.finrank_zero_of_subsingleton])]
  exact sgaEulerSum_eq_actual_eulerCharBelow K M n


/-- Proper coherent Euler characteristic has finite actual cohomology and one
uniform finite truncation, with no supplied finiteness or vanishing witness. -/
theorem proper_coherent_moduleEulerChar_finite_truncation
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] (M : X.Modules) [M.IsCoherent] :
    (∀ q : ℕ, FiniteDimensional K (Scheme.Modules.Cohomology M q)) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) M =
          Scheme.Modules.eulerCharBelow K X M n := by
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  obtain ⟨N, hN⟩ := Scheme.Modules.exists_H_subsingleton (X ↘ Spec (CommRingCat.of K))
  refine ⟨fun q => proper_coherent_cohomology_finite K M q, N, fun n hn => ?_⟩
  rw [Scheme.Modules.eulerChar_eq_sum _ M (Finset.range n) (by
    intro q hq
    have hnq : n ≤ q := by simpa only [Finset.mem_range, not_lt] using hq
    exact Scheme.Modules.finrankH_eq_zero_of_subsingleton _ M q (hN M q (hn.trans hnq)))]
  exact sgaEulerSum_eq_actual_eulerCharBelow K M n


/-- The full Euler characteristic is invariant under actual module sheaf isomorphism. -/
theorem moduleEulerChar_congr
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    {M N : X.Modules} (a : M ≅ N) :
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) M =
      Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) N := by
  simp only [Scheme.Modules.eulerChar_def]
  congr 1
  funext q
  rw [sgaFinrankH_eq_actual_finrank K M q, sgaFinrankH_eq_actual_finrank K N q,
    Scheme.Modules.finrank_cohomology_congr K a q]


/-- Full Euler characteristic is additive on actual proper coherent short exact sequences. -/
theorem proper_moduleEulerChar_of_shortExact
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) S.X₂ =
      Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) S.X₁ +
        Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) S.X₃ :=
  Scheme.Modules.eulerChar_of_shortExact _ hS

end MixedFujita

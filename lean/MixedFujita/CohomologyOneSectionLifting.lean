/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperCartierCohomology
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-! 源のH1消滅を要求しない実H1写像単射からの大域切断持ち上げ。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- An eventually nonincreasing natural sequence attains a permanent
minimum. No assumption that its eventual value is zero is made. -/
theorem nat_eventually_nonincreasing_stabilizes
    (v : ℕ → ℕ) (m₀ : ℕ) (hstep : ∀ m, m₀ ≤ m → v (m + 1) ≤ v m) :
    ∃ m₁ : ℕ, m₀ ≤ m₁ ∧ ∀ m, m₁ ≤ m → v m = v m₁ := by
  classical
  have hex : ∃ k : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ v m = k := ⟨v m₀, m₀, le_rfl, rfl⟩
  obtain ⟨m₁, hm₁, hval⟩ := Nat.find_spec hex
  refine ⟨m₁, hm₁, ?_⟩
  intro m hm
  have hmono : ∀ j : ℕ, m₁ ≤ j → v j ≤ v m₁ := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hstep j (hm₁.trans hj)).trans ih
  have hmin : Nat.find hex ≤ v m := Nat.find_min' hex ⟨m, hm₁.trans hm, rfl⟩
  exact le_antisymm (hmono m hm) (hval.symm ▸ hmin)


/-- Injectivity of the actual H1 map suffices to lift every quotient
section. Vanishing of H1 of the source is not required. -/
theorem moduleSections_surjective_of_cohomologyOne_injective
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hinj : Function.Injective (Scheme.Modules.cohomologyMap S.f 1)) :
    Function.Surjective (Scheme.Modules.Hom.app S.g ⊤) := by
  intro y
  let z := (Scheme.Modules.cohomologyZeroEquiv S.X₃).symm y
  have hz : Scheme.Modules.cohomologyδ hS 0 1 rfl z = 0 := by
    apply hinj
    rw [map_zero]
    exact (Scheme.Modules.exact_cohomologyδ_cohomologyMap hS 0 1 rfl _).mpr ⟨z, rfl⟩
  obtain ⟨x, hx⟩ := (Scheme.Modules.exact_cohomologyMap_cohomologyδ hS 0 1 rfl z).mp hz
  refine ⟨Scheme.Modules.cohomologyZeroEquiv S.X₂ x, ?_⟩
  rw [← Scheme.Modules.cohomologyZeroEquiv_cohomologyMap, hx]
  exact (Scheme.Modules.cohomologyZeroEquiv S.X₃).apply_symm_apply y


/-- Vanishing of quotient H1 makes the actual source H1 map surjective. -/
theorem cohomologyOne_surjective_of_quotient_vanish
    {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hQ : Subsingleton (Scheme.Modules.Cohomology S.X₃ 1)) :
    Function.Surjective (Scheme.Modules.cohomologyMap S.f 1) := by
  intro y
  apply (Scheme.Modules.exact_cohomologyMap_cohomologyMap hS 1 y).mp
  exact hQ.elim _ _


/-- The actual base-linear H1 map is the original additive cohomology map. -/
theorem cohomologyMapBaseLinear_eq_cohomologyMap
    (K : Type u) [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    {M N : X.Modules} (f : M ⟶ N) (q : ℕ) (x : Scheme.Modules.Cohomology M q) :
    Scheme.Modules.cohomologyMapBaseLinear K X f q x = Scheme.Modules.cohomologyMap f q x := by
  simp only [Scheme.Modules.cohomologyMapBaseLinear_apply, Scheme.Modules.cohomologyFunctor_map]
  rfl

end MixedFujita

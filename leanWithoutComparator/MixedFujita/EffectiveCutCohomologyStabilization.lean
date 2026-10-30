/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CohomologyOneSectionLifting
public import MixedFujita.SuccessiveCartierCutSequence

/-! 実切断のH1消滅から固定捻りH1次元安定化と全大冪の切断全射。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- If H1 on the actual possibly nonreduced cut eventually vanishes,
then the actual H1 dimensions of O(E+mG) stabilize. Source H1 need not vanish. -/
theorem proper_effectiveCut_cohomologyOne_eventually_stabilizes
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (E G : CartierDivisor X) (hG : G.IsEffective)
    (hvan : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Subsingleton
      (Scheme.Modules.Cohomology ((cartierSuccessiveCutShortComplex E G hG m).X₃) 1)) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Module.finrank K (Scheme.Modules.Cohomology (E + m • G).sheaf 1) =
        Module.finrank K (Scheme.Modules.Cohomology (E + m₁ • G).sheaf 1) := by
  obtain ⟨m₀, hm₀⟩ := hvan
  have hstep : ∀ m : ℕ, m₀ ≤ m →
      Module.finrank K (Scheme.Modules.Cohomology (E + (m + 1) • G).sheaf 1) ≤
        Module.finrank K (Scheme.Modules.Cohomology (E + m • G).sheaf 1) := by
    intro m hm
    let S := cartierSuccessiveCutShortComplex E G hG m
    let : FiniteDimensional K (Scheme.Modules.Cohomology S.X₁ 1) := proper_cartier_cohomology_finite K _ 1
    let : FiniteDimensional K (Scheme.Modules.Cohomology S.X₂ 1) := proper_cartier_cohomology_finite K _ 1
    let : FiniteDimensional K (Scheme.Modules.Cohomology (E + m • G).sheaf 1) := proper_cartier_cohomology_finite K _ 1
    let : FiniteDimensional K (Scheme.Modules.Cohomology (E + (m + 1) • G).sheaf 1) := proper_cartier_cohomology_finite K _ 1
    let F := Scheme.Modules.cohomologyMapBaseLinear K X S.f 1
    have hsurj : Function.Surjective F := by
      intro y
      obtain ⟨x, hx⟩ := cohomologyOne_surjective_of_quotient_vanish
        (cartierSuccessiveCutShortComplex_shortExact E G hG m) (hm₀ m hm) y
      exact ⟨x, (cohomologyMapBaseLinear_eq_cohomologyMap K S.f 1 x).trans hx⟩
    change Module.finrank K (Scheme.Modules.Cohomology S.X₂ 1) ≤
      Module.finrank K (Scheme.Modules.Cohomology S.X₁ 1)
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  obtain ⟨m₁, hm₁, hstable⟩ := nat_eventually_nonincreasing_stabilizes
    (fun m => Module.finrank K (Scheme.Modules.Cohomology (E + m • G).sheaf 1)) m₀ hstep
  exact ⟨m₁, hstable⟩


/-- Quotient sections of ALL sufficiently large actual Cartier powers
lift globally from eventual quotient H1 vanishing. The nonzero stable H1
of the ambient source is allowed and all rank witnesses are internal. -/
theorem proper_effectiveCut_eventually_sections_surjective
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (E G : CartierDivisor X) (hG : G.IsEffective)
    (hvan : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Subsingleton
      (Scheme.Modules.Cohomology ((cartierSuccessiveCutShortComplex E G hG m).X₃) 1)) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Function.Surjective (Scheme.Modules.Hom.app (cartierSuccessiveCutShortComplex E G hG m).g ⊤) := by
  obtain ⟨m₀, hm₀⟩ := hvan
  obtain ⟨m₂, hstable⟩ := proper_effectiveCut_cohomologyOne_eventually_stabilizes K E G hG ⟨m₀, hm₀⟩
  refine ⟨max m₀ m₂, ?_⟩
  intro m hm
  let S := cartierSuccessiveCutShortComplex E G hG m
  let : FiniteDimensional K (Scheme.Modules.Cohomology S.X₁ 1) := proper_cartier_cohomology_finite K _ 1
  let : FiniteDimensional K (Scheme.Modules.Cohomology S.X₂ 1) := proper_cartier_cohomology_finite K _ 1
  let F := Scheme.Modules.cohomologyMapBaseLinear K X S.f 1
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := cohomologyOne_surjective_of_quotient_vanish
      (cartierSuccessiveCutShortComplex_shortExact E G hG m) (hm₀ m ((le_max_left _ _).trans hm)) y
    exact ⟨x, (cohomologyMapBaseLinear_eq_cohomologyMap K S.f 1 x).trans hx⟩
  have hdim : Module.finrank K (Scheme.Modules.Cohomology S.X₁ 1) =
      Module.finrank K (Scheme.Modules.Cohomology S.X₂ 1) :=
    (hstable m ((le_max_right _ _).trans hm)).trans
      (hstable (m + 1) (by omega)).symm
  have hinj : Function.Injective (Scheme.Modules.cohomologyMap S.f 1) := by
    have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
    intro x y hxy
    apply hi
    exact (cohomologyMapBaseLinear_eq_cohomologyMap K S.f 1 x).trans
      (hxy.trans (cohomologyMapBaseLinear_eq_cohomologyMap K S.f 1 y).symm)
  exact moduleSections_surjective_of_cohomologyOne_injective (cartierSuccessiveCutShortComplex_shortExact E G hG m) hinj

end MixedFujita

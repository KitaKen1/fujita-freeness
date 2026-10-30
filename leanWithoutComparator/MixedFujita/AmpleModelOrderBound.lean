/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleEffectiveComparison
public import MixedFujita.PullbackOrderBound

/-!
Uniform order bounds on a smooth model with an ample divisor (step 5). The nonzero comparison
section of k J - B is now constructed by ample twisting, rather than supplied. Thus every Cartier
divisor B on such a model has one linear order bound for all its nonzero sections, all positive
degrees and all closed points. In particular the bound applies to the actual pullbacks of all
sections from any integral source under a dominant map. This still requires an ample divisor on
the smooth model; the field-projectivity of the Hironaka model remains a separate obligation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

variable {K : Type u} [Field K] [IsAlgClosed K] {T : Scheme.{u}} [IsIntegral T]
  [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]

/-- Any Cartier divisor on a smooth scheme carrying an ample divisor has a uniform linear
vanishing-order bound, with no comparison section supplied. -/
theorem vanishingOrder_le_of_ample_model {d : ℕ}
    (hn : topologicalKrullDim T = d) (hd : 1 ≤ d) {J : CartierDivisor T}
    (hJ : CartierIsAmpleProj K J) (B : CartierDivisor T) :
    ∃ c : ℕ, ∀ x : T, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
      ∀ s : Γ((j • B).sheaf, ⊤), s ≠ 0 →
        cartierSectionVanishingOrder (j • B) x s ≤ ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hJ (-B)
  have hgen : CartierIsGloballyGenerated ((max 1 j₀) • J - B) := by
    simpa only [sub_eq_add_neg, add_comm] using hj₀ (max 1 j₀) (le_max_right _ _)
  obtain ⟨τ, hτ⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgen
  exact vanishingOrder_le_of_effective_difference hn hd hJ B (le_max_left _ _) τ hτ

/-- A single constant bounds the orders of all actual pulled-back sections on the model,
uniformly in the closed point and degree; the source need not be smooth or projective. -/
theorem pulledSection_vanishingOrder_le_of_ample_model {d : ℕ}
    (hn : topologicalKrullDim T = d) (hd : 1 ≤ d) {J : CartierDivisor T}
    (hJ : CartierIsAmpleProj K J) {X : Scheme.{u}} [IsIntegral X]
    (ρ : T ⟶ X) [IsDominant ρ] (L : CartierDivisor X) :
    ∃ c : ℕ, ∀ x : T, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
      ∀ s : Γ((j • L).sheaf, ⊤), s ≠ 0 →
        cartierSectionVanishingOrder (cartierPullback ρ (j • L)) x
          (cartierDominantPullbackSection ρ (j • L) s) ≤ ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := vanishingOrder_le_of_ample_model hn hd hJ (cartierPullback ρ L)
  refine ⟨c, fun x hx j hj s hs => ?_⟩
  have hdiv := cartierPullback_nsmul ρ L j
  have ht := cartierDominantPullbackSection_ne_zero ρ (j • L) s hs
  have hbound := hc x hx j hj
    (cartierSectionCast hdiv (cartierDominantPullbackSection ρ (j • L) s))
    (cartierSectionCast_ne_zero _ _ ht)
  rwa [cartierSectionCast_vanishingOrder] at hbound

end MixedFujita

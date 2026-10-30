/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierNefPullback
public import MixedFujita.CartierNegativeGradedPullback
public import MixedFujita.AmpleEffectiveComparison

/-! Identify the module pullback of every actual Cartier sheaf on a projective
base with the sheaf of its actual Cartier pullback. Twist by an auxiliary ample
divisor until both terms have a nonzero section, then subtract using the existing
tensor inverse dictionary. The specified Cartier divisor itself is arbitrary. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {B T : Scheme.{u}} [IsIntegral B] [IsIntegral T]
  [B.Over (Spec (CommRingCat.of K))]

/-- Auxiliary ample twisting identifies the actual sheaf pullback for an arbitrary Cartier divisor. -/
theorem projective_cartier_pullback_nonempty_iso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] (D : CartierDivisor B) :
    Nonempty ((Scheme.Modules.pullback q).obj D.sheaf ≅ (cartierPullback q D).sheaf) := by
  classical
  obtain ⟨A, hA⟩ := hProj
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hA D
  obtain ⟨k₀, hk₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hA 0
  let j := max j₀ k₀
  have hDj : CartierIsGloballyGenerated (D + j • A) := hj₀ j (le_max_left _ _)
  have hAj : CartierIsGloballyGenerated (j • A) := by
    simpa only [zero_add] using hk₀ j (le_max_right _ _)
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hDj
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section hAj
  obtain ⟨a⟩ := cartierPullback_sheaf_iso_modulePullback q (D + j • A) s hs
  obtain ⟨b⟩ := cartierPullback_sheaf_iso_modulePullback q (j • A) t ht
  have hD : D + j • A - j • A = D := add_sub_cancel_right D _
  have hqD : cartierPullback q (D + j • A) - cartierPullback q (j • A) =
      cartierPullback q D := by rw [cartierPullback_add, add_sub_cancel_right]
  exact ⟨(Scheme.Modules.pullback q).mapIso (eqToIso (congrArg CartierDivisor.sheaf hD.symm)) ≪≫
    cartierPullbackSubIso (D + j • A) (j • A) q
      (cartierPullback q (D + j • A)) (cartierPullback q (j • A)) a b ≪≫
    eqToIso (congrArg CartierDivisor.sheaf hqD)⟩

/-- The actual sheaf isomorphism, requiring only the base's existing projectivity. -/
noncomputable def projectiveCartierPullbackIso
    (hProj : ∃ A : CartierDivisor B, CartierIsAmpleProj K A)
    (q : T ⟶ B) [IsDominant q] (D : CartierDivisor B) :
    (Scheme.Modules.pullback q).obj D.sheaf ≅ (cartierPullback q D).sheaf :=
  Classical.choice (projective_cartier_pullback_nonempty_iso hProj q D)

end MixedFujita

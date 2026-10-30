/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartCoordinateComparison
public import MixedFujita.ClosureCocycleSpreading

/-!
Lifting the chart relation along a dominant map (step 10, R4-3).

For a dominant morphism `φ : T → X` of integral schemes, the germ of the pullback
(`pullbackGerm φ W`, check 540) is injective on the functions on any nonempty open `W`
(`pullbackGerm_injective_of_isDominant`, check 535). Hence functions `u_i, M_i, w_i, r_i, J_i` on
opens of `X` whose germs on `T` satisfy the chart relation of check 541 satisfy, restricted to
`W_i ⊆ V_i ∩ V_0`, the relation of check 540 (`relation_of_pullbackGerm_relation`).

For `φ : T → T_A` this turns the chartwise relation on `T` (check 541, with units spread to `T_A`
by check 535) into an identity of functions on `T_A`, which check 540 carries to the fibre `T_κ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (φ : T ⟶ X) [IsDominant φ]

/-- **The germ of the pullback along a dominant morphism is injective.** -/
theorem pullbackGerm_injective_of_isDominant (W : X.Opens) [Nonempty W] [Nonempty (φ ⁻¹ᵁ W)] :
    Function.Injective (pullbackGerm φ W) := by
  intro a b hab
  apply appLE_injective_of_isDominant φ (le_rfl : φ ⁻¹ᵁ W ≤ φ ⁻¹ᵁ W)
  apply Scheme.germToFunctionField_injective T (φ ⁻¹ᵁ W)
  exact hab

/-- **A relation among germs lifts to a relation among functions.** -/
theorem relation_of_pullbackGerm_relation {N : ℕ} {V W R : Fin (N + 1) → X.Opens}
    (hWV : ∀ i, W i ≤ V i) (hWV₀ : ∀ i, W i ≤ V 0) (hVR : ∀ i, V i ≤ R i)
    [∀ i, Nonempty (W i)] [∀ i, Nonempty (φ ⁻¹ᵁ W i)] [∀ i, Nonempty (φ ⁻¹ᵁ V i)]
    [∀ i, Nonempty (φ ⁻¹ᵁ (V i ⊓ V 0))] [∀ i, Nonempty (φ ⁻¹ᵁ R i)]
    (u : ∀ i, Γ(X, V i ⊓ V 0)) (M : ∀ i, Γ(X, V i)) (w : ∀ i, Γ(X, V i)) (rr : ∀ i, Γ(X, R i))
    (J : ∀ i, Γ(X, W i)) (m m' : ℕ)
    (hrel : ∀ i, pullbackGerm φ (V i ⊓ V 0) (u i) ^ (m * m') * pullbackGerm φ (V 0) (M 0) ^ m' *
        pullbackGerm φ (V 0) (w 0) =
      pullbackGerm φ (V i) (w i) * pullbackGerm φ (R i) (rr i) *
        pullbackGerm φ (W i) (J i) ^ (m * m') * pullbackGerm φ (V i) (M i) ^ m') (i : Fin (N + 1)) :
    (X.presheaf.map (homOfLE (le_inf (hWV i) (hWV₀ i))).op (u i)) ^ (m * m') *
        (X.presheaf.map (homOfLE (hWV₀ i)).op (M 0)) ^ m' *
        X.presheaf.map (homOfLE (hWV₀ i)).op (w 0) =
      X.presheaf.map (homOfLE (hWV i)).op (w i) *
        X.presheaf.map (homOfLE ((hWV i).trans (hVR i))).op (rr i) * J i ^ (m * m') *
        (X.presheaf.map (homOfLE (hWV i)).op (M i)) ^ m' := by
  apply pullbackGerm_injective_of_isDominant φ (W i)
  simp only [map_mul, map_pow, pullbackGerm_restrict]
  exact hrel i

end MixedFujita

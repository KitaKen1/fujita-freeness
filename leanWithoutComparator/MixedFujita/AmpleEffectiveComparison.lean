/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleCoprimeBridgeProof
public import MixedFujita.CartierSectionPullbackAvoidance

/-!
Ample comparison for arbitrary Cartier divisors (step 5). On an integral scheme over a field,
if H is ample in the projective sense, A + j H is very ample for every sufficiently large j.
The residue classes modulo a very ample multiple of H reduce this to the existing hyperplane
twist theorem. Consequently j H - L has an actual effective representative modulo an explicit
principal divisor, for every large j and every Cartier divisor L. This supplies effective
comparison once an ample divisor on a birational model is known; relative projectivity of the
model does not by itself supply that ample divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Every sufficiently large twist of any Cartier divisor by an ample divisor is very ample. -/
theorem cartierIsAmpleProj_eventually_twist_veryAmple {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) (A : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → CartierIsVeryAmpleProj K (A + j • H) := by
  obtain ⟨m, hm, n, e, he, hbase, g, hg, hggen, f, hmH⟩ := hH
  choose N₀ hN₀ using fun r : ℕ =>
    eventually_nsmul_add_cartierIsVeryAmpleProj e hbase g hg hggen (A + r • H)
  refine ⟨(Finset.range m).sup (fun r => r + N₀ r * m), fun j hj => ?_⟩
  have h1 : j % m + N₀ (j % m) * m ≤ j :=
    (Finset.le_sup (f := fun r => r + N₀ r * m)
      (Finset.mem_range.mpr (Nat.mod_lt j hm))).trans hj
  have h3 : N₀ (j % m) * m ≤ m * (j / m) :=
    Nat.le_of_add_le_add_left (a := j % m) (by
      rw [Nat.mod_add_div]
      exact h1)
  have h4 : m * N₀ (j % m) ≤ m * (j / m) := by
    rw [Nat.mul_comm]
    exact h3
  have h2 : N₀ (j % m) ≤ j / m := Nat.le_of_mul_le_mul_left h4 hm
  have h : A + j • H = (A + (j % m) • H) +
      (j / m) • projectiveHyperplaneCartier e g hg hggen +
      principalCartierDivisor X (f ^ (j / m)) := by
    conv_lhs => rw [← Nat.mod_add_div j m]
    rw [add_nsmul, mul_comm m (j / m), mul_nsmul', hmH, nsmul_add,
      principalCartierDivisor_power]
    abel
  rw [h]
  exact cartierIsVeryAmpleProj_add_principal (hN₀ (j % m) (j / m) h2) _

/-- Every sufficiently large ample twist is globally generated. -/
theorem cartierIsAmpleProj_eventually_twist_globallyGenerated {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) (A : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → CartierIsGloballyGenerated (A + j • H) := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hH A
  exact ⟨j₀, fun j hj => cartierIsVeryAmpleProj_isGloballyGenerated (hj₀ j hj)⟩

/-- Global generation gives an actual nonzero section on an integral scheme. -/
theorem cartierIsGloballyGenerated_exists_nonzero_section {D : CartierDivisor X}
    (hD : CartierIsGloballyGenerated D) : ∃ s : Γ(D.sheaf, ⊤), s ≠ 0 := by
  obtain ⟨s, hs⟩ := hD (genericPoint X)
  refine ⟨s, fun h => ?_⟩
  rw [h, map_zero] at hs
  exact not_isUnit_zero hs

/-- A globally generated Cartier divisor has an actual effective principal translate. -/
theorem cartierIsGloballyGenerated_exists_effective_principal_shift {D : CartierDivisor X}
    (hD : CartierIsGloballyGenerated D) :
    ∃ f : X.functionFieldˣ, (D + principalCartierDivisor X f).IsEffective := by
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hD
  exact ⟨cartierSectionUnit D s hs, cartierSectionZeroDivisor_isEffective D s hs⟩

/-- Every large ample multiple dominates any Cartier divisor modulo an explicit principal
divisor. The threshold is uniform in the choice of the large integer j. -/
theorem cartierIsAmpleProj_eventually_effective_comparison {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) (L : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
      ∃ f : X.functionFieldˣ, (j • H - L + principalCartierDivisor X f).IsEffective := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (-L)
  refine ⟨j₀, fun j hj => ?_⟩
  have hgen : CartierIsGloballyGenerated (j • H - L) := by
    simpa only [sub_eq_add_neg, add_comm] using hj₀ j hj
  exact cartierIsGloballyGenerated_exists_effective_principal_shift hgen

end MixedFujita

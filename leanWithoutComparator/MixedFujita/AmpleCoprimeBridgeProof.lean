/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleTwistVeryAmple
public import MixedFujita.CoprimeAmpleNumericalBound
public import MixedFujita.CoprimeAmpleGlobalGeneration

/-!
The bridge from one very ample multiple to two coprime very ample multiples (step 4). Let A be
ample in the projective sense: m A = J + div f for the hyperplane divisor J of a closed immersion
over the base field. Then A + N J is very ample for a suitable N, and
(1 + N m) A = (A + N J) + div f^N. So m A and (1 + N m) A are very ample, with coprime
multipliers. This proves the bridge without smoothness, characteristic or dimension hypotheses,
and makes the numerical input for F1 for ample divisors unconditional: the integrality
L^d · W ≥ 1 for ample L follows from the two coprime projective embeddings. All sufficiently
large multiples of an ample divisor are very ample, and globally generated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section VeryAmple

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- Very ampleness in the projective sense is invariant under principal shifts. -/
theorem cartierIsVeryAmpleProj_add_principal {D : CartierDivisor X}
    (hD : CartierIsVeryAmpleProj K D) (f : X.functionFieldˣ) :
    CartierIsVeryAmpleProj K (D + principalCartierDivisor X f) := by
  obtain ⟨n, e, he, hbase, g, hg, hggen, f₁, hD⟩ := hD
  exact ⟨n, e, he, hbase, g, hg, hggen, f₁ * f, by
    rw [hD, principalCartierDivisor_mul, add_assoc]⟩

/-- An ample divisor has two coprime very ample multiples. -/
theorem cartierIsAmpleCoprime_of_ampleProj {A : CartierDivisor X}
    (hA : CartierIsAmpleProj K A) : CartierIsAmpleCoprime K A := by
  obtain ⟨m, hm, n, e, he, hbase, g, hg, hggen, f, hmA⟩ := hA
  obtain ⟨N, hN⟩ := exists_nsmul_add_cartierIsVeryAmpleProj e hbase g hg hggen A
  refine ⟨m, 1 + N * m, hm, Nat.le_add_right 1 _, ?_,
    ⟨n, e, he, hbase, g, hg, hggen, f, hmA⟩, ?_⟩
  · show Nat.gcd m (1 + N * m) = 1
    rw [Nat.gcd_add_mul_right_right, Nat.gcd_one_right]
  · have h : (1 + N * m) • A = A + N • projectiveHyperplaneCartier e g hg hggen +
        principalCartierDivisor X (f ^ N) := by
      rw [add_nsmul, one_nsmul, mul_nsmul', hmA, nsmul_add, principalCartierDivisor_power,
        add_assoc]
    rw [h]
    exact cartierIsVeryAmpleProj_add_principal hN _

/-- All sufficiently large multiples of an ample divisor are very ample: for each residue r modulo
m the divisor r A + N J is very ample for all large N, and j A = (j mod m) A + (j / m) m A. -/
theorem cartierIsAmpleProj_eventually_veryAmple {A : CartierDivisor X}
    (hA : CartierIsAmpleProj K A) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → CartierIsVeryAmpleProj K (j • A) := by
  obtain ⟨m, hm, n, e, he, hbase, g, hg, hggen, f, hmA⟩ := hA
  choose N₀ hN₀ using fun r : ℕ =>
    eventually_nsmul_add_cartierIsVeryAmpleProj e hbase g hg hggen (r • A)
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
  have h : j • A = (j % m) • A + (j / m) • projectiveHyperplaneCartier e g hg hggen +
      principalCartierDivisor X (f ^ (j / m)) := by
    conv_lhs => rw [← Nat.mod_add_div j m]
    rw [add_nsmul, mul_comm m (j / m), mul_nsmul', hmA, nsmul_add, principalCartierDivisor_power,
      add_assoc]
  rw [h]
  exact cartierIsVeryAmpleProj_add_principal (hN₀ (j % m) (j / m) h2) _

/-- All sufficiently large multiples of an ample divisor are globally generated. -/
theorem cartierIsAmpleProj_eventually_globallyGenerated {A : CartierDivisor X}
    (hA : CartierIsAmpleProj K A) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → CartierIsGloballyGenerated (j • A) :=
  cartierIsAmpleCoprime_eventually_globallyGenerated (cartierIsAmpleCoprime_of_ampleProj hA)

end VeryAmple

/-- The bridge: on a smooth projective variety an ample divisor has two coprime very ample
multiples. -/
theorem ampleCoprimeBridge : AmpleCoprimeBridge.{u} := by
  intro K _ _ _ _ X _ _ n _ _ _ A hA
  exact cartierIsAmpleCoprime_of_ampleProj hA

/-- The numerical input for F1 for ample divisors, without further hypotheses. -/
theorem mixedAmpleNumericalBound : MixedAmpleNumericalBound.{u} :=
  mixedAmpleNumericalBound_of_ampleCoprimeBridge ampleCoprimeBridge

/-- F1 follows from S-NF for ample sums alone. -/
theorem mixedFujitaFreeness_of_strongNumericalFreenessSum_unconditional
    (h : StrongNumericalFreenessSum.{u}) : MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_strongNumericalFreenessSum_of_ampleCoprimeBridge h ampleCoprimeBridge

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCurveIntrinsicDegree
public import MixedFujita.BoundedEulerDifference

/-!
Ambient Euler computations may use a truncation larger than two. Its terminal
curve value can be compared with the intrinsic line-bundle degree only after
proving the needed higher-degree vanishing. This file keeps those inputs
explicit, and connects two finite Euler recurrences to that degree. Recurrences
for actual Cartier flags are supplied by CartierFlagEuler, not postulated here
as a theorem about all projective varieties. Bertini, intersection invariance,
and geometric finite-cohomology/vanishing theorems remain separate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
variable (K : Type u) [Field K] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

theorem eulerCharBelow_eq_of_vanishing_between (M : Y.Modules) (m n : ℕ)
    (hmn : m ≤ n)
    (hvan : ∀ q, m ≤ q → q < n → Subsingleton (Scheme.Modules.Cohomology M q)) :
    Scheme.Modules.eulerCharBelow K Y M n = Scheme.Modules.eulerCharBelow K Y M m := by
  induction n with
  | zero =>
    have : m = 0 := by omega
    subst m
    rfl
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · let := hvan n hmn' (Nat.lt_succ_self n)
      rw [Scheme.Modules.eulerCharBelow_succ, Module.finrank_zero_of_subsingleton,
        Int.natCast_zero, mul_zero, add_zero]
      exact ih hmn' (fun q hmq hqn ↦ hvan q hmq (Nat.lt_trans hqn (Nat.lt_succ_self n)))
    · have : m = n + 1 := by omega
      subst m
      rfl

variable {K} {X : Scheme.{u}} [IsIntegral X]

theorem cartierCurvePullbackDegree_eq_eulerCharBelowDifference
    (D : CartierDivisor X) (φ : Y ⟶ X) (n : ℕ) (hn : 2 ≤ n)
    (hL : ∀ q, 2 ≤ q → q < n → Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) q))
    (hO : ∀ q, 2 ≤ q → q < n → Subsingleton
      (Scheme.Modules.Cohomology (SheafOfModules.unit Y.ringCatSheaf) q)) :
    cartierCurvePullbackDegree (K := K) D φ =
      Scheme.Modules.eulerCharBelow K Y ((Scheme.Modules.pullback φ).obj D.sheaf) n -
        Scheme.Modules.eulerCharBelow K Y (SheafOfModules.unit Y.ringCatSheaf) n := by
  rw [eulerCharBelow_eq_of_vanishing_between K _ 2 n hn hL,
    eulerCharBelow_eq_of_vanishing_between K _ 2 n hn hO]
  exact cartierCurvePullbackDegree_eq_eulerCharacteristicDifference D φ

theorem cartierCurvePullbackDegree_binomial_of_bounded_euler_recurrences
    (D : CartierDivisor X) (φ : Y ⟶ X) (N n : ℕ) (hn : 2 ≤ n)
    (c d : ℕ → ℕ → ℤ)
    (hc : ∀ r j, r + j < N → c (r + 1) j = c r j - c r (j + 1))
    (hd : ∀ r j, r + j < N → d (r + 1) j = d r j - d r (j + 1))
    (hcLast : c N 0 = Scheme.Modules.eulerCharBelow K Y
      ((Scheme.Modules.pullback φ).obj D.sheaf) n)
    (hdLast : d N 0 = Scheme.Modules.eulerCharBelow K Y
      (SheafOfModules.unit Y.ringCatSheaf) n)
    (hL : ∀ q, 2 ≤ q → q < n → Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) q))
    (hO : ∀ q, 2 ≤ q → q < n → Subsingleton
      (Scheme.Modules.Cohomology (SheafOfModules.unit Y.ringCatSheaf) q)) :
    cartierCurvePullbackDegree (K := K) D φ =
      ∑ k ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ k * (N.choose k : ℤ) * (c 0 k - d 0 k) := by
  rw [cartierCurvePullbackDegree_eq_eulerCharBelowDifference D φ n hn hL hO,
    ← hcLast, ← hdLast]
  exact boundedEulerCut_difference_binomial N c d hc hd

end MixedFujita

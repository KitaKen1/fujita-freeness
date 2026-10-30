/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.MvPolynomial.Funext

/-! 全符号付き整数格子による有理多変数多項式の一意性。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Rational multivariate polynomials are determined by all signed integer
tuples; uniqueness uses the actual infinite-box extensionality theorem. -/
theorem rationalMvPolynomial_eq_of_eval_int {σ : Type*} (P Q : MvPolynomial σ ℚ)
    (h : ∀ z : σ → ℤ, MvPolynomial.eval (fun i => (z i : ℚ)) P =
      MvPolynomial.eval (fun i => (z i : ℚ)) Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun z : ℤ => (z : ℚ)))
    (fun _ => Set.infinite_range_of_injective (Int.cast_injective :
      Function.Injective (fun z : ℤ => (z : ℚ))))
  intro x hx
  have hxi : ∀ i, ∃ z : ℤ, (z : ℚ) = x i := fun i => hx i (Set.mem_univ i)
  choose z hz using hxi
  have heq : x = fun i => (z i : ℚ) := funext fun i => (hz i).symm
  rw [heq]
  exact h z

end MixedFujita

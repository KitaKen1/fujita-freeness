/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierNefDefinition

/-!
Numerical triviality tested by actual pullback degrees on all proper smooth integral curves.
It is equivalent to nefness of both D and -D for the existing curve-test definition of nefness.
No identification with numerical dimension zero, or existence of numerical dimension, is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- Every actual proper smooth curve mapping over K has degree-zero pullback. -/
def CartierIsNumericallyTrivial (D : CartierDivisor Y) : Prop :=
  ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
    topologicalKrullDim C = 1 → ∀ φ : C ⟶ Y,
      φ ≫ (Y ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) →
        cartierCurvePullbackDegree (K := K) D φ = 0

variable {K}

omit [Y.Over (Spec (CommRingCat.of K))] in
theorem cartierCurvePullbackDegree_neg {C : Scheme.{u}} [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (D : CartierDivisor Y) (φ : C ⟶ Y) :
    cartierCurvePullbackDegree (K := K) (-D) φ =
      -cartierCurvePullbackDegree (K := K) D φ :=
  map_neg (cartierCurvePullbackDegreeHom (K := K) hC φ) D

/-- Numerical triviality is precisely nefness of a divisor and its negative, for curve tests. -/
theorem cartierIsNumericallyTrivial_iff_nef_and_neg_nef (D : CartierDivisor Y) :
    CartierIsNumericallyTrivial K D ↔ CartierIsNef K D ∧ CartierIsNef K (-D) := by
  constructor
  · intro h
    constructor
    · intro C _ _ _ _ hC φ hφ
      exact le_of_eq (h C hC φ hφ).symm
    · intro C _ _ _ _ hC φ hφ
      rw [cartierCurvePullbackDegree_neg (K := K) hC, h C hC φ hφ, neg_zero]
  · rintro ⟨hD, hneg⟩ C _ _ _ _ hC φ hφ
    have h1 := hD C hC φ hφ
    have h2 := hneg C hC φ hφ
    rw [cartierCurvePullbackDegree_neg (K := K) hC] at h2
    omega

theorem cartierIsNumericallyTrivial_zero :
    CartierIsNumericallyTrivial K (0 : CartierDivisor Y) := by
  intro C _ _ _ _ hC φ _
  exact cartierCurvePullbackDegree_zero (K := K) hC φ

theorem cartierIsNumericallyTrivial_add {D E : CartierDivisor Y}
    (hD : CartierIsNumericallyTrivial K D) (hE : CartierIsNumericallyTrivial K E) :
    CartierIsNumericallyTrivial K (D + E) := by
  intro C _ _ _ _ hC φ hφ
  rw [cartierCurvePullbackDegree_add (K := K) hC, hD C hC φ hφ, hE C hC φ hφ, add_zero]

theorem cartierIsNumericallyTrivial_neg {D : CartierDivisor Y}
    (hD : CartierIsNumericallyTrivial K D) : CartierIsNumericallyTrivial K (-D) := by
  intro C _ _ _ _ hC φ hφ
  rw [cartierCurvePullbackDegree_neg (K := K) hC, hD C hC φ hφ, neg_zero]

theorem cartierIsNumericallyTrivial_nsmul {D : CartierDivisor Y}
    (hD : CartierIsNumericallyTrivial K D) (q : ℕ) :
    CartierIsNumericallyTrivial K (q • D) := by
  intro C _ _ _ _ hC φ hφ
  rw [cartierCurvePullbackDegree_nsmul (K := K) hC, hD C hC φ hφ, mul_zero]

/-- A positive multiple is numerically trivial exactly when the divisor is. -/
theorem cartierIsNumericallyTrivial_nsmul_iff (D : CartierDivisor Y) {q : ℕ} (hq : 0 < q) :
    CartierIsNumericallyTrivial K (q • D) ↔ CartierIsNumericallyTrivial K D := by
  constructor
  · intro h C _ _ _ _ hC φ hφ
    have he := h C hC φ hφ
    rw [cartierCurvePullbackDegree_nsmul (K := K) hC] at he
    exact (mul_eq_zero.mp he).resolve_left (by exact_mod_cast (Nat.ne_of_gt hq))
  · exact fun h => cartierIsNumericallyTrivial_nsmul h q

theorem cartierIsNumericallyTrivial_of_iso {D E : CartierDivisor Y}
    (e : D.sheaf ≅ E.sheaf) (hD : CartierIsNumericallyTrivial K D) :
    CartierIsNumericallyTrivial K E := by
  intro C _ _ _ _ hC φ hφ
  rw [← cartierCurvePullbackDegree_congr (K := K) D E φ e]
  exact hD C hC φ hφ

theorem cartierIsNumericallyTrivial_principal (f : Y.functionFieldˣ) :
    CartierIsNumericallyTrivial K (principalCartierDivisor Y f) := by
  intro C _ _ _ _ hC φ _
  exact cartierCurvePullbackDegree_principal (K := K) hC φ f

theorem cartierIsNumericallyTrivial_add_principal_iff (D : CartierDivisor Y)
    (f : Y.functionFieldˣ) :
    CartierIsNumericallyTrivial K (D + principalCartierDivisor Y f) ↔
      CartierIsNumericallyTrivial K D := by
  constructor
  · intro h C _ _ _ _ hC φ hφ
    have he := h C hC φ hφ
    simpa only [cartierCurvePullbackDegree_add (K := K) hC,
      cartierCurvePullbackDegree_principal (K := K) hC, add_zero] using he
  · exact fun h => cartierIsNumericallyTrivial_add h (cartierIsNumericallyTrivial_principal f)

/-- Torsion in the Cartier divisor class group is numerically trivial. -/
theorem cartierIsNumericallyTrivial_of_principal_multiple (D : CartierDivisor Y)
    {q : ℕ} (hq : 0 < q)
    (hprin : ∃ f : Y.functionFieldˣ, q • D = principalCartierDivisor Y f) :
    CartierIsNumericallyTrivial K D := by
  apply (cartierIsNumericallyTrivial_nsmul_iff D hq).mp
  obtain ⟨f, hf⟩ := hprin
  rw [hf]
  exact cartierIsNumericallyTrivial_principal f

end MixedFujita

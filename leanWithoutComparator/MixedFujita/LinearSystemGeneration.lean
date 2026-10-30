/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GradedLinearSystem

/-!
Generation of the coordinate ring over a linear system of parameters. Suppose every
monomial of degree t lies in the degree-t part of P + (y_0, ..., y_d). Then every form of
degree e lies in P plus the span of the products q(y) f, where f is a form of degree
e' < t, e' ≤ e, and q is a form of degree e - e' in d + 1 variables evaluated at y. So
the graded coordinate ring K[X]/P is generated in degrees below t as a module over the
polynomial ring in the y_i. The proof is the recursion of GradedLinearSystem read
upwards.
-/

@[expose] public section

open MvPolynomial Finset

namespace MixedFujita

variable {σ K : Type*} [Field K] {d : ℕ} (y : Fin (d + 1) → MvPolynomial σ K)

/-- The forms of degree m in d + 1 variables evaluated at y. -/
noncomputable def linearSystemPowerSpan (m : ℕ) : Submodule K (MvPolynomial σ K) :=
  (homogeneousSubmodule (Fin (d + 1)) K m).map (aeval y).toLinearMap

/-- The span of q(y) f with f of degree e' < t, e' ≤ e, and q of degree e - e'. -/
noncomputable def linearSystemLowSpan (t e : ℕ) : Submodule K (MvPolynomial σ K) :=
  ⨆ (e' : ℕ) (_ : e' < t) (_ : e' ≤ e),
    linearSystemPowerSpan y (e - e') * homogeneousSubmodule σ K e'

theorem one_mem_linearSystemPowerSpan_zero : (1 : MvPolynomial σ K) ∈ linearSystemPowerSpan y 0 :=
  ⟨1, (mem_homogeneousSubmodule 0 _).mpr (isHomogeneous_one (Fin (d + 1)) K), by simp⟩

theorem linearSystemPowerSpan_mul_mem (i : Fin (d + 1)) {m : ℕ} {q : MvPolynomial σ K}
    (hq : q ∈ linearSystemPowerSpan y m) : y i * q ∈ linearSystemPowerSpan y (m + 1) := by
  obtain ⟨Q, hQ, rfl⟩ := hq
  refine ⟨X i * Q, ?_, ?_⟩
  · have h := (isHomogeneous_X K i).mul ((mem_homogeneousSubmodule m Q).mp hQ)
    rw [Nat.add_comm 1 m] at h
    exact (mem_homogeneousSubmodule (m + 1) _).mpr h
  · simp

theorem mem_linearSystemLowSpan {t e e' : ℕ} (het : e' < t) (hee : e' ≤ e) {q f : MvPolynomial σ K}
    (hq : q ∈ linearSystemPowerSpan y (e - e')) (hf : f ∈ homogeneousSubmodule σ K e') :
    q * f ∈ linearSystemLowSpan y t e := by
  have hmem : q * f ∈ linearSystemPowerSpan y (e - e') * homogeneousSubmodule σ K e' :=
    Submodule.mul_mem_mul hq hf
  unfold linearSystemLowSpan
  exact Submodule.mem_iSup_of_mem e' (Submodule.mem_iSup_of_mem het
    (Submodule.mem_iSup_of_mem hee hmem))

/-- Multiplying by y_i raises the low span by one degree. -/
theorem linearSystemLowSpan_mulLeft_le (i : Fin (d + 1)) (t e : ℕ) :
    (linearSystemLowSpan y t e).map (LinearMap.mulLeft K (y i)) ≤ linearSystemLowSpan y t (e + 1) := by
  unfold linearSystemLowSpan
  rw [Submodule.map_iSup]
  refine iSup_le fun e' => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun het => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hee => ?_
  rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
  intro q hq f hf
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc]
  have hq' : y i * q ∈ linearSystemPowerSpan y (e + 1 - e') := by
    rw [show e + 1 - e' = e - e' + 1 by omega]
    exact linearSystemPowerSpan_mul_mem y i hq
  exact mem_linearSystemLowSpan y het (by omega) hq' hf

variable (P : Ideal (MvPolynomial σ K))

/-- Every form is congruent modulo P to the low span: the coordinate ring is generated over
K[y] in degrees below t. -/
theorem homogeneousSubmodule_le_linearSystemLowSpan (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) :
    ∀ e, homogeneousSubmodule σ K e ≤ P.restrictScalars K ⊔ linearSystemLowSpan y t e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    by_cases het : e < t
    · intro f hf
      apply Submodule.mem_sup_right
      have h := mem_linearSystemLowSpan y het le_rfl
        (by rw [Nat.sub_self]; exact one_mem_linearSystemPowerSpan_zero y) hf
      simpa using h
    · have hfilt : ∀ k, linearSystemFiltration P y k e ≤
          P.restrictScalars K ⊔ linearSystemLowSpan y t e := by
        intro k
        induction k with
        | zero =>
          rw [linearSystemFiltration_zero]
          exact inf_le_left.trans le_sup_left
        | succ k ihk =>
          cases e with
          | zero =>
            rw [linearSystemFiltration_succ_zero]
            exact ihk
          | succ e₀ =>
            by_cases hk : k < d + 1
            · rw [linearSystemFiltration_succ_succ P y k e₀ hk]
              refine sup_le ihk ?_
              have hle := ih e₀ (Nat.lt_succ_self e₀)
              calc (homogeneousSubmodule σ K e₀).map (LinearMap.mulLeft K (y ⟨k, hk⟩))
                  ≤ (P.restrictScalars K ⊔ linearSystemLowSpan y t e₀).map
                      (LinearMap.mulLeft K (y ⟨k, hk⟩)) := Submodule.map_mono hle
                _ = (P.restrictScalars K).map (LinearMap.mulLeft K (y ⟨k, hk⟩)) ⊔
                      (linearSystemLowSpan y t e₀).map (LinearMap.mulLeft K (y ⟨k, hk⟩)) :=
                    Submodule.map_sup _ _ _
                _ ≤ P.restrictScalars K ⊔ linearSystemLowSpan y t (e₀ + 1) := by
                    refine sup_le_sup ?_ (linearSystemLowSpan_mulLeft_le y ⟨k, hk⟩ t e₀)
                    rintro _ ⟨p, hp, rfl⟩
                    exact P.mul_mem_left _ hp
            · rw [linearSystemFiltration_succ_succ_of_le P y k e₀ hk]
              exact ihk
      exact (linearSystemFiltration_top hy hnull e (not_lt.mp het)).trans (hfilt (d + 1))

end MixedFujita

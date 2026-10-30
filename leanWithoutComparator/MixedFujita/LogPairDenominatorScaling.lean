/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantBoundaryPerturbation

/-!
Increasing the denominator and Cartier presentation by the same positive integer
does not change actual klt or boundary effectivity. Actual discrepancies and
crepant boundaries scale, rather than being supplied as comparison assumptions.
Adding an actual effective section divisor preserves source boundary effectivity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Actual discrepancy scales with the denominator-cleared Cartier presentation. -/
theorem logDiscrepancyDivisor_scale_denominator (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d m : ℕ) (D : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) :
    logDiscrepancyDivisor n ρ hρ c f (m * d) (m • D) cT hT =
      m • logDiscrepancyDivisor n ρ hρ c f d D cT hT := by
  unfold logDiscrepancyDivisor
  rw [cartierPullback_nsmul, smul_sub, smul_smul]

/-- The actual crepant boundary scales with the same denominator change. -/
theorem crepantBoundaryCartier_scale_denominator (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d m : ℕ) (D : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) :
    crepantBoundaryCartier ρ hρ c f (m * d) (m • D) cT hT =
      m • crepantBoundaryCartier ρ hρ c f d D cT hT := by
  unfold crepantBoundaryCartier
  rw [cartierPullback_nsmul, smul_sub, smul_smul]

omit [IsIntegral X] [IsIntegral T] [X.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))] in
/-- The strict discrepancy inequality is unchanged by a positive denominator scaling. -/
theorem scaled_discrepancy_strict_iff (d m : ℕ) (hm : 1 ≤ m) (a : ℤ) :
    -((m * d : ℕ) : ℤ) < (m : ℤ) * a ↔ -(d : ℤ) < a := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  have h : -((m * d : ℕ) : ℤ) = (m : ℤ) * -(d : ℤ) := by push_cast; ring
  rw [h, mul_lt_mul_iff_of_pos_left hm0]

/-- The actual all-test-model klt predicate is invariant under positive denominator scaling. -/
theorem logPairIsKlt_scale_denominator_iff (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d m : ℕ) (hm : 1 ≤ m) (D : CartierDivisor X) :
    LogPairIsKlt c f (m * d) (m • D) ↔ LogPairIsKlt c f d D := by
  constructor
  · intro h U _ _ _ _ σ _ _ _ hσ cU x hx
    have h' := h U σ hσ cU x hx
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul,
      scaled_discrepancy_strict_iff d m hm] at h'
    exact h'
  · intro h U _ _ _ _ σ _ _ _ hσ cU x hx
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul,
      scaled_discrepancy_strict_iff d m hm]
    exact h U σ hσ cU x hx

variable [IsLocallyNoetherian X]

/-- Actual source boundary effectivity is invariant under positive denominator scaling. -/
theorem logPairBoundaryEffective_scale_denominator_iff (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d m : ℕ) (hm : 1 ≤ m) (D : CartierDivisor X) :
    LogPairBoundaryEffective c f (m * d) (m • D) ↔ LogPairBoundaryEffective c f d D := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm
  unfold LogPairBoundaryEffective
  simp only [cartierCoefficient_nsmul, Nat.cast_mul, mul_assoc,
    mul_le_mul_iff_of_pos_left hm0]

/-- Actual effective Cartier divisors have nonnegative actual prime coefficients. -/
theorem cartierCoefficient_nonneg_of_isEffective (E : CartierDivisor X)
    (hE : E.IsEffective) (x : X) : 0 ≤ cartierCoefficient E x := by
  obtain ⟨f, hf, hreg⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
  exact cartierCoefficient_nonneg_of_mem_range hf hreg

/-- Adding an actual effective Cartier divisor preserves effectivity of the source boundary. -/
theorem logPairBoundaryEffective_add_effective (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D E : CartierDivisor X)
    (h : LogPairBoundaryEffective c f d D) (hE : E.IsEffective) :
    LogPairBoundaryEffective c f d (D + E) := by
  intro e x he hx
  rw [cartierCoefficient_add]
  exact (h e x he hx).trans
    (le_add_of_nonneg_right (cartierCoefficient_nonneg_of_isEffective E hE x))

/-- Any nonnegative multiple of an actual section zero divisor preserves source effectivity. -/
theorem logPairBoundaryEffective_section_perturbation (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d k : ℕ) (D H : CartierDivisor X)
    (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0) (h : LogPairBoundaryEffective c f d D) :
    LogPairBoundaryEffective c f d (D + k • cartierSectionZeroDivisor H s hs) := by
  intro e x he hx
  rw [cartierCoefficient_add, cartierCoefficient_nsmul]
  exact (h e x he hx).trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k)
    (cartierCoefficient_nonneg_of_isEffective _ (cartierSectionZeroDivisor_isEffective H s hs) x)))

end MixedFujita

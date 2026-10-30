/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryDiscrepancy

/-!
The algebraic cancellation behind the actual DVR Jacobian estimate. An alternating
expression in rows π*a_i + b_i*w is divisible by π^(card i - 1): terms containing
two copies of w vanish. This is a ring-theoretic divisibility statement, with no
formal power-series coordinates or model-to-test-valuation comparison.
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

/-- At most one row of an alternating expression can contribute the common direction w. -/
theorem alternating_scalar_rank_one_dvd {R M ι : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (f : M [⋀^ι]→ₗ[R] R) (π : R) (a : ι → M) (b : ι → R) (w : M) :
    π ^ (Fintype.card ι - 1) ∣ f (fun i => π • a i + b i • w) := by
  classical
  change π ^ (Fintype.card ι - 1) ∣ f ((fun i => π • a i) + fun i => b i • w)
  rw [f.map_add_univ]
  apply Finset.dvd_sum
  intro s _
  have hfactor :
      f (s.piecewise (fun i => π • a i) (fun i => b i • w)) =
        (∏ i, if i ∈ s then π else b i) * f (s.piecewise a (fun _ => w)) := by
    convert f.map_smul_univ (fun i => if i ∈ s then π else b i)
      (s.piecewise a (fun _ => w)) using 1
    · congr 1
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [hfactor]
  by_cases hlarge : 1 < sᶜ.card
  · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card_iff_nontrivial.mp hlarge
    have hi' : i ∉ s := Finset.mem_compl.mp hi
    have hj' : j ∉ s := Finset.mem_compl.mp hj
    have hz : f (s.piecewise a (fun _ => w)) = 0 :=
      f.map_eq_zero_of_eq _ (by simp [Finset.piecewise, hi', hj']) hij
    rw [hz, mul_zero]
    exact dvd_zero _
  · have hcard : Fintype.card ι - 1 ≤ s.card := by
      have h := s.card_add_card_compl
      omega
    have hprod : (∏ i, if i ∈ s then π else b i) =
        π ^ s.card * ∏ i, if i ∈ s then 1 else b i := by
      calc
        _ = ∏ i, (if i ∈ s then π else 1) * (if i ∈ s then 1 else b i) := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i ∈ s <;> simp [hi]
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]
    rw [hprod]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow π hcard) _) _

/-- Adding a rank-one matrix to π times any square matrix leaves n-1 powers of π
in the determinant. The statement also handles the zero-dimensional matrix. -/
theorem matrix_scalar_rank_one_det_dvd {R ι : Type*} [CommRing R] [Fintype ι]
    [DecidableEq ι] (π : R) (A : Matrix ι ι R) (b w : ι → R) :
    π ^ (Fintype.card ι - 1) ∣ (π • A + Matrix.vecMulVec b w).det := by
  exact alternating_scalar_rank_one_dvd Matrix.detRowAlternating π A b w

end MixedFujita

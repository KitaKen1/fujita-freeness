/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesExponents
public import MixedFujita.LatticeBrunnMinkowski

/-!
A mixed lower bound by Brunn–Minkowski on initial exponents, replacing the positivity of mixed
intersection numbers in §9.1. For finite-dimensional spaces S, T of power series in D + 1
variables and a space C whose initial exponents contain the cube {0,1}^(D+1), if all products
φ ψ χ (φ ∈ S, ψ ∈ T, χ ∈ C) lie in U, then the initial exponents of U contain E_S + E_T + cube,
so dim(S)^(1/(D+1)) + dim(T)^(1/(D+1)) ≤ dim(U)^(1/(D+1)). Iterating along A_k = L_1 + ... + L_k,
the restricted sections of the sum of s divisors have (dim)^(1/(D+1)) at least the sum of the
roots for the summands: with Lemma 4 for each very ample summand (λ = 1), the sum satisfies (13)
with λ = s, which is what F1 needs from A^d·W ≥ s^d.
-/

@[expose] public section

namespace MixedFujita

open scoped Pointwise

variable {K : Type*} [Field K] {D : ℕ}

/-- The initial exponents of a subspace, as integer vectors. -/
noncomputable def initialExponentSet (m : MonomialOrder (Fin (D + 1)))
    (S : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [FiniteDimensional K S] :
    Finset (Fin (D + 1) → ℤ) := by
  classical
  exact (initialMonomialFinset m S).image fun p i => (p i : ℤ)

theorem initialExponentSet_card (m : MonomialOrder (Fin (D + 1)))
    (S : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [FiniteDimensional K S] :
    (initialExponentSet m S).card = Module.finrank K S := by
  classical
  rw [initialExponentSet, Finset.card_image_of_injective, initialMonomialFinset_card]
  intro p q h
  ext i
  have h' := congrFun h i
  simp only at h'
  exact_mod_cast h'

theorem mem_initialExponentSet (m : MonomialOrder (Fin (D + 1)))
    (S : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [FiniteDimensional K S]
    {γ : Fin (D + 1) → ℤ} :
    γ ∈ initialExponentSet m S ↔
      ∃ p ∈ initialMonomialFinset m S, (fun i => (p i : ℤ)) = γ := by
  classical
  simp [initialExponentSet]

/-- Initial exponents of products: E_S + E_T ⊆ E_U when S · T ⊆ U. -/
theorem initialExponentSet_add_subset (m : MonomialOrder (Fin (D + 1)))
    (S T U : Submodule K (MvPowerSeries (Fin (D + 1)) K))
    [FiniteDimensional K S] [FiniteDimensional K T] [FiniteDimensional K U]
    (hmul : ∀ φ ∈ S, ∀ ψ ∈ T, φ * ψ ∈ U) :
    initialExponentSet m S + initialExponentSet m T ⊆ initialExponentSet m U := by
  classical
  intro γ hγ
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hγ
  obtain ⟨p, hp, rfl⟩ := (mem_initialExponentSet m S).mp ha
  obtain ⟨q, hq, rfl⟩ := (mem_initialExponentSet m T).mp hb
  refine (mem_initialExponentSet m U).mpr ⟨p + q, initialMonomialFinset_add_subset m S T U hmul
    (Finset.mem_add.mpr ⟨p, hp, q, hq, rfl⟩), ?_⟩
  funext i
  simp only [Finsupp.add_apply, Nat.cast_add, Pi.add_apply]

theorem initialExponentSet_nonempty (m : MonomialOrder (Fin (D + 1)))
    (S : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [FiniteDimensional K S]
    (hS : 0 < Module.finrank K S) : (initialExponentSet m S).Nonempty := by
  rw [← Finset.card_pos, initialExponentSet_card]
  exact hS

/-- The mixed Brunn–Minkowski step: dim(S)^(1/(D+1)) + dim(T)^(1/(D+1)) ≤ dim(U)^(1/(D+1)) when
S · T · C ⊆ U and the initial exponents of C contain the cube. -/
theorem mixed_root_step (m : MonomialOrder (Fin (D + 1)))
    (S T C U : Submodule K (MvPowerSeries (Fin (D + 1)) K))
    [FiniteDimensional K S] [FiniteDimensional K T] [FiniteDimensional K C]
    [FiniteDimensional K U]
    (hmul : ∀ φ ∈ S, ∀ ψ ∈ T, ∀ χ ∈ C, φ * ψ * χ ∈ U)
    (hcube : binaryVectors (D + 1) ⊆ initialExponentSet m C)
    (hS : 0 < Module.finrank K S) (hT : 0 < Module.finrank K T) :
    (Module.finrank K S : ℝ) ^ ((D : ℝ) + 1)⁻¹ + (Module.finrank K T : ℝ) ^ ((D : ℝ) + 1)⁻¹ ≤
      (Module.finrank K U : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
  classical
  -- the space spanned by the products of S and T
  set ST : Submodule K (MvPowerSeries (Fin (D + 1)) K) :=
    Submodule.span K {x | ∃ φ ∈ S, ∃ ψ ∈ T, φ * ψ = x} with hST
  have hSTU : ∀ x ∈ ST, ∀ χ ∈ C, x * χ ∈ U := by
    intro x hx χ hχ
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, hφ, ψ, hψ, rfl⟩ := hy
      exact hmul φ hφ ψ hψ χ hχ
    | zero => rw [zero_mul]; exact U.zero_mem
    | add y z _ _ hy hz => rw [add_mul]; exact U.add_mem hy hz
    | smul c y _ hy => rw [smul_mul_assoc]; exact U.smul_mem c hy
  -- ST is finite dimensional: it lies in the span of products of bases
  have hSTfin : FiniteDimensional K ST := by
    have hle : ST ≤ Submodule.span K
        ((fun p : Fin (Module.finrank K S) × Fin (Module.finrank K T) =>
          ((Module.finBasis K S p.1 : S) : MvPowerSeries (Fin (D + 1)) K) *
            ((Module.finBasis K T p.2 : T) : MvPowerSeries (Fin (D + 1)) K)) '' Set.univ) := by
      rw [hST, Submodule.span_le]
      rintro _ ⟨φ, hφ, ψ, hψ, rfl⟩
      have hφ' := (Module.finBasis K S).sum_repr ⟨φ, hφ⟩
      have hψ' := (Module.finBasis K T).sum_repr ⟨ψ, hψ⟩
      have hφe : φ = ∑ i, (Module.finBasis K S).repr ⟨φ, hφ⟩ i •
          ((Module.finBasis K S i : S) : MvPowerSeries (Fin (D + 1)) K) := by
        have := congrArg Subtype.val hφ'
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
      have hψe : ψ = ∑ i, (Module.finBasis K T).repr ⟨ψ, hψ⟩ i •
          ((Module.finBasis K T i : T) : MvPowerSeries (Fin (D + 1)) K) := by
        have := congrArg Subtype.val hψ'
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using this.symm
      rw [SetLike.mem_coe, hφe, hψe, Finset.sum_mul]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [Finset.mul_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [smul_mul_smul_comm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), Set.mem_univ _, rfl⟩)
    have hfin : FiniteDimensional K (Submodule.span K
        ((fun p : Fin (Module.finrank K S) × Fin (Module.finrank K T) =>
          ((Module.finBasis K S p.1 : S) : MvPowerSeries (Fin (D + 1)) K) *
            ((Module.finBasis K T p.2 : T) : MvPowerSeries (Fin (D + 1)) K)) '' Set.univ)) :=
      FiniteDimensional.span_of_finite K (Set.toFinite _)
    exact Submodule.finiteDimensional_of_le hle
  have hEST : initialExponentSet m S + initialExponentSet m T ⊆ initialExponentSet m ST :=
    initialExponentSet_add_subset m S T ST fun φ hφ ψ hψ =>
      Submodule.subset_span ⟨φ, hφ, ψ, hψ, rfl⟩
  have hESTC : initialExponentSet m ST + initialExponentSet m C ⊆ initialExponentSet m U :=
    initialExponentSet_add_subset m ST C U hSTU
  have hthick : thickenedSum (initialExponentSet m S) (initialExponentSet m T) ⊆
      initialExponentSet m U := by
    intro γ hγ
    obtain ⟨a, ha, c, hc, rfl⟩ := Finset.mem_add.mp hγ
    exact hESTC (Finset.mem_add.mpr ⟨a, hEST ha, c, hcube hc, rfl⟩)
  have h := lattice_brunn_minkowski_of_subset _ _ _ (initialExponentSet_nonempty m S hS)
    (initialExponentSet_nonempty m T hT) hthick
  simpa only [initialExponentSet_card] using h

/-- The mixed bound along A_k = L_0 + ... + L_k: if U_0 ⊇ S_0 and U_k · S_{k+1} · C ⊆ U_{k+1}, then
Σ_{i ≤ k} dim(S_i)^(1/(D+1)) ≤ dim(U_k)^(1/(D+1)). -/
theorem mixed_root_sum (m : MonomialOrder (Fin (D + 1)))
    (S U : ℕ → Submodule K (MvPowerSeries (Fin (D + 1)) K))
    (C : Submodule K (MvPowerSeries (Fin (D + 1)) K))
    [∀ i, FiniteDimensional K (S i)] [∀ k, FiniteDimensional K (U k)] [FiniteDimensional K C]
    (h0 : S 0 ≤ U 0)
    (hstep : ∀ k, ∀ φ ∈ U k, ∀ ψ ∈ S (k + 1), ∀ χ ∈ C, φ * ψ * χ ∈ U (k + 1))
    (hcube : binaryVectors (D + 1) ⊆ initialExponentSet m C)
    (hpos : ∀ i, 0 < Module.finrank K (S i)) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ ≤
      (Module.finrank K (U k) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
  induction k with
  | zero =>
    rw [Finset.sum_range_one]
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
    exact_mod_cast Submodule.finrank_mono h0
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hUpos : 0 < Module.finrank K (U k) := by
      have h1 : 0 < (Module.finrank K (S 0) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        Real.rpow_pos_of_pos (by exact_mod_cast hpos 0) _
      have h2 : (Module.finrank K (S 0) : ℝ) ^ ((D : ℝ) + 1)⁻¹ ≤
          ∑ i ∈ Finset.range (k + 1), (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        Finset.single_le_sum (f := fun i => (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹)
          (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (Finset.mem_range.mpr (by omega))
      have h3 : 0 < (Module.finrank K (U k) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        (h1.trans_le h2).trans_le ih
      by_contra hzero
      push Not at hzero
      have h4 : Module.finrank K (U k) = 0 := by omega
      rw [h4, Nat.cast_zero, Real.zero_rpow (by positivity)] at h3
      exact lt_irrefl 0 h3
    have hst := mixed_root_step m (U k) (S (k + 1)) C (U (k + 1)) (hstep k) hcube hUpos (hpos _)
    linarith

/-- (13) for a sum of s divisors with λ = s: if each summand has (D'! dim)^(1/D') ≥ q, the sum has
(D'! dim)^(1/D') ≥ s q, where D' = D + 1. -/
theorem mixed_root_sum_lower (m : MonomialOrder (Fin (D + 1)))
    (S U : ℕ → Submodule K (MvPowerSeries (Fin (D + 1)) K))
    (C : Submodule K (MvPowerSeries (Fin (D + 1)) K))
    [∀ i, FiniteDimensional K (S i)] [∀ k, FiniteDimensional K (U k)] [FiniteDimensional K C]
    (h0 : S 0 ≤ U 0)
    (hstep : ∀ k, ∀ φ ∈ U k, ∀ ψ ∈ S (k + 1), ∀ χ ∈ C, φ * ψ * χ ∈ U (k + 1))
    (hcube : binaryVectors (D + 1) ⊆ initialExponentSet m C)
    (hpos : ∀ i, 0 < Module.finrank K (S i)) {q : ℝ}
    (hlow : ∀ i, q ≤ (((D + 1).factorial * Module.finrank K (S i) : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹)
    (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * q ≤
      (((D + 1).factorial * Module.finrank K (U k) : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
  have hsum := mixed_root_sum m S U C h0 hstep hcube hpos k
  set c : ℝ := ((D + 1).factorial : ℝ) ^ ((D : ℝ) + 1)⁻¹ with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  have hfac : ∀ x : ℕ, (((D + 1).factorial * x : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹ =
      c * (x : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
    intro x
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
  have hlow' : ∀ i, q ≤ c * (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
    intro i
    rw [← hfac]
    exact hlow i
  calc ((k + 1 : ℕ) : ℝ) * q = ∑ _i ∈ Finset.range (k + 1), q := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ i ∈ Finset.range (k + 1), c * (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        Finset.sum_le_sum fun i _ => hlow' i
    _ = c * ∑ i ∈ Finset.range (k + 1), (Module.finrank K (S i) : ℝ) ^ ((D : ℝ) + 1)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ c * (Module.finrank K (U k) : ℝ) ^ ((D : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_left hsum hc0
    _ = _ := (hfac _).symm

end MixedFujita

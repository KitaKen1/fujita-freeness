/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
Hilbert increments from a linear system of parameters, by repeated hyperplane
sections and no Hilbert polynomial. Let P be an ideal of K[X] and y_0, ..., y_d
nonzero linear forms such that every monomial of degree t lies in the degree-t part
of P + (y_0, ..., y_d). Killing y_0, ..., y_d one at a time gives degree filtrations
whose quotient dimensions satisfy q_k(e+1) ≤ q_k(e) + q_(k+1)(e+1), and the last one
vanishes from degree t on. Downward induction gives q_1(e) ≤ C (e+1)^(d-1), hence
h(k+j) - h(k) ≤ C j (k+j+1)^(d-1) for the Hilbert function h(e) = dim (K[X]/P)_e.
Noether normalization, Hilbert–Serre and dimension theory are not used.
-/

@[expose] public section

namespace MixedFujita

open MvPolynomial Finset

section

variable {σ K : Type*} [Fintype σ] [Field K]

instance homogeneousSubmodule_finiteDimensional (e : ℕ) :
    FiniteDimensional K (homogeneousSubmodule σ K e) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have hfin : {d : σ →₀ ℕ | d.degree = e}.Finite :=
    (Finsupp.finite_of_degree_le e).subset (fun d hd => le_of_eq hd)
  have := hfin.fintype
  exact LinearEquiv.finiteDimensional (AddMonoidAlgebra.supportedEquivFinsupp (R := K) _).symm

variable (P : Ideal (MvPolynomial σ K)) {d : ℕ} (y : Fin (d + 1) → MvPolynomial σ K)

/-- The degree-e part of P plus the multiples of y_0, ..., y_(k-1), built recursively. -/
noncomputable def linearSystemFiltration : ℕ → ℕ → Submodule K (MvPolynomial σ K)
  | 0, e => P.restrictScalars K ⊓ homogeneousSubmodule σ K e
  | k + 1, 0 => linearSystemFiltration k 0
  | k + 1, e + 1 =>
      if hk : k < d + 1 then
        linearSystemFiltration k (e + 1) ⊔
          (homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (y ⟨k, hk⟩))
      else linearSystemFiltration k (e + 1)

omit [Fintype σ] in
theorem linearSystemFiltration_zero (e : ℕ) :
    linearSystemFiltration P y 0 e = P.restrictScalars K ⊓ homogeneousSubmodule σ K e := by
  rw [linearSystemFiltration]

omit [Fintype σ] in
theorem linearSystemFiltration_succ_zero (k : ℕ) :
    linearSystemFiltration P y (k + 1) 0 = linearSystemFiltration P y k 0 := by
  rw [linearSystemFiltration]

omit [Fintype σ] in
theorem linearSystemFiltration_succ_succ (k e : ℕ) (hk : k < d + 1) :
    linearSystemFiltration P y (k + 1) (e + 1) = linearSystemFiltration P y k (e + 1) ⊔
      (homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (y ⟨k, hk⟩)) := by
  simp only [linearSystemFiltration, hk, ↓reduceDIte]

omit [Fintype σ] in
theorem linearSystemFiltration_succ_succ_of_le (k e : ℕ) (hk : ¬ k < d + 1) :
    linearSystemFiltration P y (k + 1) (e + 1) = linearSystemFiltration P y k (e + 1) := by
  simp only [linearSystemFiltration, hk, ↓reduceDIte]

omit [Fintype σ] in
theorem homogeneous_mulLeft_map_le {ℓ : MvPolynomial σ K} (hℓ : ℓ.IsHomogeneous 1) (e : ℕ) :
    (homogeneousSubmodule σ K e).map (LinearMap.mulLeft K ℓ) ≤ homogeneousSubmodule σ K (e + 1) := by
  rintro _ ⟨f, hf, rfl⟩
  have h := hℓ.mul ((mem_homogeneousSubmodule e f).mp hf)
  rw [Nat.add_comm 1 e] at h
  exact (mem_homogeneousSubmodule (e + 1) _).mpr h

variable {P y}

omit [Fintype σ] in
theorem linearSystemFiltration_le_homogeneous (hy : ∀ i, (y i).IsHomogeneous 1) :
    ∀ k e, linearSystemFiltration P y k e ≤ homogeneousSubmodule σ K e
  | 0, e => by rw [linearSystemFiltration_zero]; exact inf_le_right
  | k + 1, 0 => by
      rw [linearSystemFiltration_succ_zero]
      exact linearSystemFiltration_le_homogeneous hy k 0
  | k + 1, e + 1 => by
      by_cases hk : k < d + 1
      · rw [linearSystemFiltration_succ_succ P y k e hk]
        exact sup_le (linearSystemFiltration_le_homogeneous hy k (e + 1))
          (homogeneous_mulLeft_map_le (hy _) e)
      · rw [linearSystemFiltration_succ_succ_of_le P y k e hk]
        exact linearSystemFiltration_le_homogeneous hy k (e + 1)

omit [Fintype σ] in
theorem linearSystemFiltration_mono_succ (k e : ℕ) :
    linearSystemFiltration P y k e ≤ linearSystemFiltration P y (k + 1) e := by
  cases e with
  | zero => rw [linearSystemFiltration_succ_zero]
  | succ e =>
    by_cases hk : k < d + 1
    · rw [linearSystemFiltration_succ_succ P y k e hk]
      exact le_sup_left
    · rw [linearSystemFiltration_succ_succ_of_le P y k e hk]

omit [Fintype σ] in
theorem mulLeft_map_mulLeft_map_comm (ℓ ℓ' : MvPolynomial σ K) (W : Submodule K (MvPolynomial σ K)) :
    (W.map (LinearMap.mulLeft K ℓ')).map (LinearMap.mulLeft K ℓ) =
      (W.map (LinearMap.mulLeft K ℓ)).map (LinearMap.mulLeft K ℓ') := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro f
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
  ring

omit [Fintype σ] in
/-- Multiplication by a linear form respects the filtrations. -/
theorem linearSystemFiltration_mulLeft_le (hy : ∀ i, (y i).IsHomogeneous 1)
    {ℓ : MvPolynomial σ K} (hℓ : ℓ.IsHomogeneous 1) :
    ∀ k e, (linearSystemFiltration P y k e).map (LinearMap.mulLeft K ℓ) ≤
      linearSystemFiltration P y k (e + 1)
  | 0, e => by
      rw [linearSystemFiltration_zero, linearSystemFiltration_zero]
      rintro _ ⟨f, ⟨hfP, hfe⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · exact P.mul_mem_left ℓ hfP
      · exact homogeneous_mulLeft_map_le hℓ e ⟨f, hfe, rfl⟩
  | k + 1, 0 => by
      rw [linearSystemFiltration_succ_zero]
      exact (linearSystemFiltration_mulLeft_le hy hℓ k 0).trans
        (linearSystemFiltration_mono_succ k 1)
  | k + 1, e + 1 => by
      by_cases hk : k < d + 1
      · rw [linearSystemFiltration_succ_succ P y k e hk,
          linearSystemFiltration_succ_succ P y k (e + 1) hk, Submodule.map_sup]
        apply sup_le
        · exact (linearSystemFiltration_mulLeft_le hy hℓ k (e + 1)).trans le_sup_left
        · rw [mulLeft_map_mulLeft_map_comm]
          exact (Submodule.map_mono (homogeneous_mulLeft_map_le hℓ e)).trans le_sup_right
      · rw [linearSystemFiltration_succ_succ_of_le P y k e hk,
          linearSystemFiltration_succ_succ_of_le P y k (e + 1) hk]
        exact linearSystemFiltration_mulLeft_le hy hℓ k (e + 1)

omit [Fintype σ] in
theorem monomial_mem_of_degree_succ {I : ℕ → Submodule K (MvPolynomial σ K)}
    (hmul : ∀ (i : σ) e, (I e).map (LinearMap.mulLeft K (X i)) ≤ I (e + 1))
    {e : ℕ} (he : ∀ α : σ →₀ ℕ, α.degree = e → monomial α (1 : K) ∈ I e)
    (α : σ →₀ ℕ) (hα : α.degree = e + 1) : monomial α (1 : K) ∈ I (e + 1) := by
  classical
  have hsupp : α.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    have h0 : (0 : σ →₀ ℕ).degree = 0 := map_zero _
    omega
  obtain ⟨i, hi⟩ := hsupp
  have hle : Finsupp.single i 1 ≤ α :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  set α' := α - Finsupp.single i 1 with hα'
  have hsum : α' + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
  have hdeg : α'.degree = e := by
    have h := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, hα] at h
    omega
  have hmono : monomial α (1 : K) = X i * monomial α' (1 : K) := by
    rw [X, monomial_mul_monomial, mul_one, add_comm (Finsupp.single i 1) α', hsum]
  rw [hmono]
  exact hmul i e ⟨monomial α' 1, he α' hdeg, rfl⟩

omit [Fintype σ] in
theorem homogeneousSubmodule_le_of_monomials {I : Submodule K (MvPolynomial σ K)} {e : ℕ}
    (h : ∀ α : σ →₀ ℕ, α.degree = e → monomial α (1 : K) ∈ I) :
    homogeneousSubmodule σ K e ≤ I := by
  rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single,
    Submodule.span_le]
  rintro _ ⟨α, hα, rfl⟩
  exact h α hα

omit [Fintype σ] in
/-- The last filtration is everything from degree t on. -/
theorem linearSystemFiltration_top (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) :
    ∀ e, t ≤ e → homogeneousSubmodule σ K e ≤ linearSystemFiltration P y (d + 1) e := by
  have hmul : ∀ (i : σ) e, (linearSystemFiltration P y (d + 1) e).map (LinearMap.mulLeft K (X i)) ≤
      linearSystemFiltration P y (d + 1) (e + 1) := fun i e =>
    linearSystemFiltration_mulLeft_le hy (isHomogeneous_X K i) (d + 1) e
  have hmono : ∀ e, t ≤ e → ∀ α : σ →₀ ℕ, α.degree = e →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) e := by
    intro e he
    induction e, he using Nat.le_induction with
    | base => exact hnull
    | succ e _ ih => exact monomial_mem_of_degree_succ hmul ih
  intro e he
  exact homogeneousSubmodule_le_of_monomials (hmono e he)

theorem linearSystemFiltration_finiteDimensional (hy : ∀ i, (y i).IsHomogeneous 1) (k e : ℕ) :
    FiniteDimensional K (linearSystemFiltration P y k e) :=
  Submodule.finiteDimensional_of_le (linearSystemFiltration_le_homogeneous hy k e)

/-- One hyperplane section: the dimension identity behind q_k(e+1) ≤ q_k(e) + q_(k+1)(e+1). -/
theorem linearSystemFiltration_finrank_step (hy : ∀ i, (y i).IsHomogeneous 1)
    (hy0 : ∀ i, y i ≠ 0) (k e : ℕ) (hk : k < d + 1) :
    Module.finrank K (linearSystemFiltration P y (k + 1) (e + 1)) +
        Module.finrank K (linearSystemFiltration P y k e) ≤
      Module.finrank K (linearSystemFiltration P y k (e + 1)) +
        Module.finrank K (homogeneousSubmodule σ K e) := by
  rw [linearSystemFiltration_succ_succ P y k e hk]
  set B := linearSystemFiltration P y k (e + 1)
  set M := (homogeneousSubmodule σ K e).map (LinearMap.mulLeft K (y ⟨k, hk⟩))
  set N := (linearSystemFiltration P y k e).map (LinearMap.mulLeft K (y ⟨k, hk⟩))
  have hBfin : FiniteDimensional K B := linearSystemFiltration_finiteDimensional hy k (e + 1)
  have hMle : M ≤ homogeneousSubmodule σ K (e + 1) := homogeneous_mulLeft_map_le (hy _) e
  have hMfin : FiniteDimensional K M := Submodule.finiteDimensional_of_le hMle
  have hinj : Function.Injective (LinearMap.mulLeft K (y ⟨k, hk⟩)) := by
    intro f g hfg
    exact mul_left_cancel₀ (hy0 ⟨k, hk⟩) hfg
  have hMrank : Module.finrank K M = Module.finrank K (homogeneousSubmodule σ K e) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hNrank : Module.finrank K N = Module.finrank K (linearSystemFiltration P y k e) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)).symm
  have hNle : N ≤ B ⊓ M := le_inf (linearSystemFiltration_mulLeft_le hy (hy _) k e)
    (Submodule.map_mono (linearSystemFiltration_le_homogeneous hy k e))
  have hNinf : Module.finrank K N ≤ Module.finrank K ↥(B ⊓ M) := by
    have : FiniteDimensional K ↥(B ⊓ M) := Submodule.finiteDimensional_of_le inf_le_left
    exact Submodule.finrank_mono hNle
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq B M
  omega

variable (P y) in
/-- The quotient dimensions q_k(e) = dim S_e - dim I_k(e). -/
noncomputable def linearSystemQuotientDim (k e : ℕ) : ℕ :=
  Module.finrank K (homogeneousSubmodule σ K e) - Module.finrank K (linearSystemFiltration P y k e)

theorem linearSystemQuotientDim_step (hy : ∀ i, (y i).IsHomogeneous 1) (hy0 : ∀ i, y i ≠ 0)
    (k e : ℕ) (hk : k < d + 1) :
    linearSystemQuotientDim P y k (e + 1) ≤
      linearSystemQuotientDim P y k e + linearSystemQuotientDim P y (k + 1) (e + 1) := by
  have h := linearSystemFiltration_finrank_step (P := P) hy hy0 k e hk
  have h1 := Submodule.finrank_mono (linearSystemFiltration_le_homogeneous (P := P) hy k e)
  have h2 := Submodule.finrank_mono (linearSystemFiltration_le_homogeneous (P := P) hy k (e + 1))
  have h3 := Submodule.finrank_mono
    (linearSystemFiltration_le_homogeneous (P := P) hy (k + 1) (e + 1))
  unfold linearSystemQuotientDim
  omega

omit [Fintype σ] in
theorem linearSystemQuotientDim_le (k e : ℕ) :
    linearSystemQuotientDim P y k e ≤ Module.finrank K (homogeneousSubmodule σ K e) :=
  Nat.sub_le _ _

theorem linearSystemQuotientDim_top_eq_zero (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) (e : ℕ) (he : t ≤ e) :
    linearSystemQuotientDim P y (d + 1) e = 0 := by
  have hle := linearSystemFiltration_top hy hnull e he
  have := linearSystemFiltration_finiteDimensional (P := P) hy (d + 1) e
  have h := Submodule.finrank_mono hle
  unfold linearSystemQuotientDim
  omega

/-- Telescoping one filtration step. -/
theorem linearSystemQuotientDim_telescope (hy : ∀ i, (y i).IsHomogeneous 1)
    (hy0 : ∀ i, y i ≠ 0) (k : ℕ) (hk : k < d + 1) :
    ∀ e, linearSystemQuotientDim P y k e ≤
      linearSystemQuotientDim P y k 0 + ∑ i ∈ range e, linearSystemQuotientDim P y (k + 1) (i + 1)
  | 0 => by simp
  | e + 1 => by
      rw [sum_range_succ]
      have h := linearSystemQuotientDim_step (P := P) hy hy0 k e hk
      have ih := linearSystemQuotientDim_telescope hy hy0 k hk e
      omega

/-- The constant C0 = dim S_0 + Σ_(e<t) dim S_e. -/
noncomputable def linearSystemConstant (σ K : Type*) [Fintype σ] [Field K] (t : ℕ) : ℕ :=
  Module.finrank K (homogeneousSubmodule σ K 0) +
    ∑ e ∈ range t, Module.finrank K (homogeneousSubmodule σ K e)

theorem linearSystemQuotientDim_last_le (hy : ∀ i, (y i).IsHomogeneous 1) (hy0 : ∀ i, y i ≠ 0)
    {t : ℕ} (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) (e : ℕ) :
    linearSystemQuotientDim P y d e ≤ linearSystemConstant σ K t := by
  have htel := linearSystemQuotientDim_telescope (P := P) hy hy0 d (Nat.lt_succ_self d) e
  have h0 := linearSystemQuotientDim_le (P := P) (y := y) d 0
  have hsum : ∑ i ∈ range e, linearSystemQuotientDim P y (d + 1) (i + 1) ≤
      ∑ e' ∈ range t, Module.finrank K (homogeneousSubmodule σ K e') := by
    calc ∑ i ∈ range e, linearSystemQuotientDim P y (d + 1) (i + 1)
        = ∑ i ∈ (range e).filter (fun i => i + 1 < t),
            linearSystemQuotientDim P y (d + 1) (i + 1) := by
          rw [sum_filter_of_ne]
          intro i _ hne
          by_contra hlt
          exact hne (linearSystemQuotientDim_top_eq_zero hy hnull (i + 1) (not_lt.mp hlt))
      _ ≤ ∑ i ∈ (range e).filter (fun i => i + 1 < t),
            Module.finrank K (homogeneousSubmodule σ K (i + 1)) :=
          sum_le_sum fun i _ => linearSystemQuotientDim_le _ _
      _ ≤ ∑ e' ∈ range t, Module.finrank K (homogeneousSubmodule σ K e') := by
          rw [← sum_image (s := (range e).filter (fun i => i + 1 < t)) (g := fun i => i + 1)
            (f := fun e' => Module.finrank K (homogeneousSubmodule σ K e'))
            (fun a _ b _ h => by simpa using h)]
          apply sum_le_sum_of_subset
          intro x hx
          simp only [mem_image, mem_filter, mem_range] at hx
          obtain ⟨a, ⟨_, ha⟩, rfl⟩ := hx
          exact mem_range.mpr ha
  unfold linearSystemConstant
  omega

/-- Downward induction: q_(d-r)(e) ≤ C0 (e+1)^r. -/
theorem linearSystemQuotientDim_le_pow (hy : ∀ i, (y i).IsHomogeneous 1) (hy0 : ∀ i, y i ≠ 0)
    {t : ℕ} (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) :
    ∀ r, r ≤ d → ∀ e, linearSystemQuotientDim P y (d - r) e ≤
      linearSystemConstant σ K t * (e + 1) ^ r
  | 0, _, e => by simpa using linearSystemQuotientDim_last_le hy hy0 hnull e
  | r + 1, hr, e => by
      have hk : d - (r + 1) < d + 1 := by omega
      have hsucc : d - (r + 1) + 1 = d - r := by omega
      have htel := linearSystemQuotientDim_telescope (P := P) hy hy0 (d - (r + 1)) hk e
      rw [hsucc] at htel
      have h0 : linearSystemQuotientDim P y (d - (r + 1)) 0 ≤ linearSystemConstant σ K t := by
        have := linearSystemQuotientDim_le (P := P) (y := y) (d - (r + 1)) 0
        unfold linearSystemConstant
        omega
      have hterm : ∀ i ∈ range e, linearSystemQuotientDim P y (d - r) (i + 1) ≤
          linearSystemConstant σ K t * (e + 1) ^ r := by
        intro i hi
        have hi' : i + 1 + 1 ≤ e + 1 := by rw [mem_range] at hi; omega
        exact (linearSystemQuotientDim_le_pow hy hy0 hnull r (by omega) (i + 1)).trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi' r))
      have hsum := sum_le_sum hterm
      rw [sum_const, card_range, smul_eq_mul] at hsum
      have hpos : 1 ≤ (e + 1) ^ r := Nat.one_le_pow _ _ (Nat.succ_pos e)
      calc linearSystemQuotientDim P y (d - (r + 1)) e
          ≤ linearSystemConstant σ K t + e * (linearSystemConstant σ K t * (e + 1) ^ r) := by
            omega
        _ ≤ linearSystemConstant σ K t * (e + 1) ^ r +
              e * (linearSystemConstant σ K t * (e + 1) ^ r) := by
            have := Nat.mul_le_mul_left (linearSystemConstant σ K t) hpos
            omega
        _ = linearSystemConstant σ K t * (e + 1) ^ (r + 1) := by ring

/-- The Hilbert increment bound for h(e) = dim (K[X]/P)_e from a linear system of
parameters y_0, ..., y_d (d ≥ 1). -/
theorem linearSystem_hilbert_increment (hy : ∀ i, (y i).IsHomogeneous 1) (hy0 : ∀ i, y i ≠ 0)
    (hd : 1 ≤ d) {t : ℕ} (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) (k j : ℕ) :
    (linearSystemQuotientDim P y 0 (k + j) : ℝ) - linearSystemQuotientDim P y 0 k ≤
      (linearSystemConstant σ K t : ℝ) * j * ((k : ℝ) + j + 1) ^ (d - 1) := by
  have hq1 : ∀ e, linearSystemQuotientDim P y 1 e ≤ linearSystemConstant σ K t * (e + 1) ^ (d - 1) := by
    intro e
    have h := linearSystemQuotientDim_le_pow hy hy0 hnull (d - 1) (by omega) e
    rwa [show d - (d - 1) = 1 by omega] at h
  have hstep : ∀ i, linearSystemQuotientDim P y 0 (k + i + 1) ≤
      linearSystemQuotientDim P y 0 (k + i) + linearSystemConstant σ K t * (k + j + 1) ^ (d - 1) ∨
      j ≤ i := by
    intro i
    by_cases hij : i < j
    · left
      have h := linearSystemQuotientDim_step (P := P) hy hy0 0 (k + i) (by omega)
      rw [zero_add] at h
      have h1 := hq1 (k + i + 1)
      have hmono : linearSystemConstant σ K t * (k + i + 1 + 1) ^ (d - 1) ≤
          linearSystemConstant σ K t * (k + j + 1) ^ (d - 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      omega
    · right
      omega
  have hsum : ∀ i, i ≤ j → linearSystemQuotientDim P y 0 (k + i) ≤
      linearSystemQuotientDim P y 0 k + i * (linearSystemConstant σ K t * (k + j + 1) ^ (d - 1)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      rcases hstep i with h | h
      · rw [show k + (i + 1) = k + i + 1 by omega]
        calc linearSystemQuotientDim P y 0 (k + i + 1)
            ≤ linearSystemQuotientDim P y 0 (k + i) +
                linearSystemConstant σ K t * (k + j + 1) ^ (d - 1) := h
          _ ≤ _ := by rw [Nat.succ_mul]; omega
      · omega
  have hfinal := hsum j le_rfl
  have hreal : (linearSystemQuotientDim P y 0 (k + j) : ℝ) ≤
      (linearSystemQuotientDim P y 0 k : ℝ) +
        (j : ℝ) * ((linearSystemConstant σ K t : ℝ) * ((k : ℝ) + j + 1) ^ (d - 1)) := by
    exact_mod_cast hfinal
  linarith

end

end MixedFujita

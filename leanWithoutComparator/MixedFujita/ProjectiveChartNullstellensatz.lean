/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.ProjectiveHomogenization

/-!
The chart Nullstellensatz for a linear system. Let degree-one forms y_0, ..., y_d have
no common zero on an actual integral closed subscheme Y of polynomial projective space.
On every nonempty chart the pulled-back equations generate the unit ideal of the affine
chart. Lifting the coefficients through the surjective polynomial presentation and
homogenizing gives X_k^N ∈ P + (y_0, ..., y_d) in degree N, where P is the homogeneous
ideal of the generic point; an empty chart has X_k ∈ P. Pigeonhole then puts every
monomial of one degree t into the degree-t filtration used by GradedLinearSystem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Filtration

variable {σ K : Type*} [Fintype σ] [Field K] {P : Ideal (MvPolynomial σ K)} {d : ℕ}
  (y : Fin (d + 1) → MvPolynomial σ K)

omit [Fintype σ] in
theorem linearSystemFiltration_mono {k k' : ℕ} (h : k ≤ k') (e : ℕ) :
    linearSystemFiltration P y k e ≤ linearSystemFiltration P y k' e := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (linearSystemFiltration_mono_succ _ _)

omit [Fintype σ] in
theorem linearSystemFiltration_mulLeft_mem_top (i : Fin (d + 1)) {N : ℕ}
    {h : MvPolynomial σ K} (hh : h ∈ homogeneousSubmodule σ K N) :
    y i * h ∈ linearSystemFiltration P y (d + 1) (N + 1) := by
  have hle : (homogeneousSubmodule σ K N).map (LinearMap.mulLeft K (y i)) ≤
      linearSystemFiltration P y (i.val + 1) (N + 1) := by
    rw [linearSystemFiltration_succ_succ P y i.val N i.isLt]
    exact le_sup_right
  exact linearSystemFiltration_mono y (Nat.succ_le_of_lt i.isLt) _ (hle ⟨h, hh, rfl⟩)

omit [Fintype σ] in
theorem finsupp_degree_succ_decompose {α : σ →₀ ℕ} {m : ℕ} (hα : α.degree = m + 1) :
    ∃ (i : σ) (β : σ →₀ ℕ), β.degree = m ∧ β + Finsupp.single i 1 = α := by
  classical
  have hsupp : α.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    have h0 : (0 : σ →₀ ℕ).degree = 0 := map_zero _
    omega
  obtain ⟨i, hi⟩ := hsupp
  have hle : Finsupp.single i 1 ≤ α :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  refine ⟨i, α - Finsupp.single i 1, ?_, tsub_add_cancel_of_le hle⟩
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, hα] at h
  omega

omit [Fintype σ] in
theorem linearSystemFiltration_mul_monomial_mem (hy : ∀ i, (y i).IsHomogeneous 1) (k : ℕ) :
    ∀ (m : ℕ) (β : σ →₀ ℕ), β.degree = m → ∀ (e : ℕ) (f : MvPolynomial σ K),
      f ∈ linearSystemFiltration P y k e →
      monomial β (1 : K) * f ∈ linearSystemFiltration P y k (e + m)
  | 0, β, hβ, e, f, hf => by
      have hβ0 : β = 0 := by
        ext i
        have h := Finsupp.le_degree i β
        rw [hβ] at h
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        omega
      subst hβ0
      simpa using hf
  | m + 1, β, hβ, e, f, hf => by
      obtain ⟨i, β', hβ', rfl⟩ := finsupp_degree_succ_decompose hβ
      have ih := linearSystemFiltration_mul_monomial_mem hy k m β' hβ' e f hf
      have hstep := linearSystemFiltration_mulLeft_le hy (isHomogeneous_X K i) k (e + m)
        ⟨_, ih, rfl⟩
      have heq : monomial (β' + Finsupp.single i 1) (1 : K) * f =
          X i * (monomial β' (1 : K) * f) := by
        rw [X, ← mul_assoc, monomial_mul_monomial, mul_one, add_comm (Finsupp.single i 1) β']
      rw [heq, show e + (m + 1) = e + m + 1 by omega]
      exact hstep

end Filtration

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  {d : ℕ} (y : Fin (d + 1) → MvPolynomial (Fin n) K)

/-- On every chart some power of the coordinate lies in P + (y) in its degree. -/
theorem projective_chart_power_mem (hy : ∀ i, (y i).IsHomogeneous 1)
    (hnz : ∀ z : Y, ∃ i, y i ∉ (e z).asHomogeneousIdeal) (k : Fin n) :
    ∃ N, 1 ≤ N ∧ X k ^ N ∈ linearSystemFiltration
      ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y (d + 1) N := by
  by_cases hne : Nonempty (projectivePullbackCoordinateOpen e k)
  swap
  · refine ⟨1, le_rfl, ?_⟩
    have hXk : X k ∈ (e (genericPoint Y)).asHomogeneousIdeal := by
      by_contra h
      exact hne ⟨⟨genericPoint Y, h⟩⟩
    apply linearSystemFiltration_mono y (Nat.zero_le (d + 1)) 1
    rw [linearSystemFiltration_zero, pow_one]
    exact ⟨hXk, isHomogeneous_X K k⟩
  let U := projectivePullbackCoordinateOpen e k
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one).preimage e
  let s : Set Γ(Y, U) := Set.range fun i => projectivePullbackHomogeneousEquation e k 1 (y i) (hy i)
  have hcov : U ≤ ⨆ f : s, Y.basicOpen f.1 := by
    intro z hz
    obtain ⟨i, hi⟩ := hnz z
    have hb := projectivePullbackHomogeneousEquation_basicOpen e k 1 (y i) (hy i) Nat.one_pos
    have hz' : z ∈ Y.basicOpen (projectivePullbackHomogeneousEquation e k 1 (y i) (hy i)) := by
      rw [hb]
      exact ⟨hz, hi⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨_, ⟨i, rfl⟩⟩, hz'⟩
  have hspan := (hU.self_le_iSup_basicOpen_iff).mp hcov
  have h1 : (1 : Γ(Y, U)) ∈ Ideal.span s := hspan ▸ Submodule.mem_top
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp h1
  choose B hB using fun i => projectivePullbackAffinePolynomialMap_surjective e k (b i)
  let N' := ∑ i, (B i).totalDegree
  have hdeg : ∀ i, (B i).totalDegree ≤ N' := fun i =>
    Finset.single_le_sum (fun j _ => Nat.zero_le ((B j).totalDegree)) (Finset.mem_univ i)
  let H : Fin (d + 1) → MvPolynomial (Fin n) K := fun i => projectiveHomogenize k N' (B i)
  have hH : ∀ i, (H i).IsHomogeneous N' := fun i => projectiveHomogenize_isHomogeneous k (B i) (hdeg i)
  let F := X k ^ (N' + 1) - ∑ i, y i * H i
  have hFh : F.IsHomogeneous (N' + 1) := by
    apply IsHomogeneous.sub
    · simpa using (isHomogeneous_X K k).pow (N' + 1)
    · apply IsHomogeneous.sum
      intro i _
      simpa [add_comm] using (hy i).mul (hH i)
  have hFzero : projectivePullbackHomogeneousEquation e k (N' + 1) F hFh = 0 := by
    rw [projectivePullbackHomogeneousEquation_eq_affine]
    simp only [F, H, map_sub, map_pow, map_sum, map_mul, projectiveDehomogenize_X_self, one_pow,
      projectiveDehomogenize_homogenize, map_one, hB]
    have hyi : ∀ i, projectivePullbackAffinePolynomialMap e k (projectiveDehomogenize K k (y i)) =
        projectivePullbackHomogeneousEquation e k 1 (y i) (hy i) := fun i =>
      (projectivePullbackHomogeneousEquation_eq_affine e k 1 (y i) (hy i)).symm
    simp only [hyi]
    rw [← hb]
    simp only [smul_eq_mul, mul_comm]
    exact sub_self _
  have hFP : F ∈ (e (genericPoint Y)).asHomogeneousIdeal :=
    (projectivePullbackHomogeneousEquation_eq_zero_iff e k (N' + 1) F hFh).mp hFzero
  refine ⟨N' + 1, Nat.succ_pos N', ?_⟩
  have hsplit : X k ^ (N' + 1) = F + ∑ i, y i * H i := by
    simp only [F, sub_add_cancel]
  rw [hsplit]
  apply Submodule.add_mem
  · apply linearSystemFiltration_mono y (Nat.zero_le (d + 1)) (N' + 1)
    rw [linearSystemFiltration_zero]
    exact ⟨hFP, hFh⟩
  · apply Submodule.sum_mem
    intro i _
    exact linearSystemFiltration_mulLeft_mem_top y i ((mem_homogeneousSubmodule N' (H i)).mpr (hH i))

/-- The degree-t condition of GradedLinearSystem, from no common zeros. -/
theorem projective_linearSystem_monomials_mem (hy : ∀ i, (y i).IsHomogeneous 1)
    (hnz : ∀ z : Y, ∃ i, y i ∉ (e z).asHomogeneousIdeal) :
    ∃ t, ∀ α : Fin n →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration
        ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y (d + 1) t := by
  choose N hN1 hN using fun k => projective_chart_power_mem e y hy hnz k
  refine ⟨∑ k, (N k - 1) + 1, ?_⟩
  intro α hα
  have hex : ∃ k, N k ≤ α k := by
    by_contra h
    simp only [not_exists, not_le] at h
    have hle : α.degree ≤ ∑ k, (N k - 1) := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.sum_le_sum fun k _ => by have := h k; omega
    omega
  obtain ⟨k, hk⟩ := hex
  have hle : Finsupp.single k (N k) ≤ α := Finsupp.single_le_iff.mpr hk
  set β := α - Finsupp.single k (N k) with hβdef
  have hsum : β + Finsupp.single k (N k) = α := tsub_add_cancel_of_le hle
  have hdeg : β.degree + N k = α.degree := by
    rw [← hsum, map_add, Finsupp.degree_single]
  have hmono : monomial α (1 : K) = monomial β (1 : K) * X k ^ N k := by
    rw [← hsum, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rw [hmono]
  have hmem := linearSystemFiltration_mul_monomial_mem y hy (d + 1) β.degree β rfl (N k) _ (hN k)
  have ht : N k + β.degree = ∑ k, (N k - 1) + 1 := by omega
  rwa [ht] at hmem

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemGeneration
public import MixedFujita.ProjectiveChartNullstellensatz

/-!
A relation among the parameters lowers the growth of the coordinate ring. If a nonzero
form Φ of degree δ in d + 1 variables vanishes on the parameters y modulo P, then the
degree-D part of K[X]/P has dimension at most C (D+1)^(d-1). The forms of degree m in the
y modulo P are killed on Φ times the forms of degree m - δ, so their dimension is at most
the increment dim R_m - dim R_(m-δ) of the polynomial ring R in d + 1 variables, which
GradedLinearSystem bounds by applying it to the variables themselves. Generation in
degrees below t and the bound dim (M N) <= dim M dim N for products of subspaces finish.
-/

@[expose] public section

open MvPolynomial Finset

namespace MixedFujita

variable {K : Type*} [Field K]

/-- The increment of the polynomial ring in d + 1 variables, by GradedLinearSystem applied to
the variables with t = 1. -/
theorem homogeneousSubmodule_finrank_le_add {d : ℕ} (hd : 1 ≤ d) (k j : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K (k + j)) ≤
      Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K k) +
        linearSystemConstant (Fin (d + 1)) K 1 * j * (k + j + 1) ^ (d - 1) := by
  have hnull : ∀ α : Fin (d + 1) →₀ ℕ, α.degree = 1 →
      monomial α (1 : K) ∈ linearSystemFiltration (⊥ : Ideal (MvPolynomial (Fin (d + 1)) K))
        (fun i => X i) (d + 1) 1 := by
    intro α hα
    obtain ⟨i, β, hβ, rfl⟩ := finsupp_degree_succ_decompose (m := 0) hα
    have hβ0 : β = 0 := (Finsupp.degree_eq_zero_iff β).mp hβ
    subst hβ0
    rw [zero_add, ← X]
    have h := linearSystemFiltration_mulLeft_mem_top (P := ⊥)
      (fun i : Fin (d + 1) => (X i : MvPolynomial (Fin (d + 1)) K)) i
      ((mem_homogeneousSubmodule 0 (1 : MvPolynomial (Fin (d + 1)) K)).mpr
        (isHomogeneous_one (Fin (d + 1)) K))
    simpa using h
  have h := linearSystem_hilbert_increment (P := ⊥)
    (y := fun i => (X i : MvPolynomial (Fin (d + 1)) K))
    (fun i => isHomogeneous_X K i) (fun i => X_ne_zero i) hd hnull k j
  have hq : ∀ e, linearSystemQuotientDim (⊥ : Ideal (MvPolynomial (Fin (d + 1)) K))
      (fun i => X i) 0 e = Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K e) := by
    intro e
    unfold linearSystemQuotientDim
    rw [linearSystemFiltration_zero, Submodule.restrictScalars_bot, bot_inf_eq, finrank_bot,
      Nat.sub_zero]
  rw [hq, hq] at h
  have h' : (Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K (k + j)) : ℝ) ≤
      Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K k) +
        ((linearSystemConstant (Fin (d + 1)) K 1 * j * (k + j + 1) ^ (d - 1) : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h'

/-- The dimension of a product of finite-dimensional subspaces is at most the product of the
dimensions. -/
theorem finrank_mul_le_mul {A : Type*} [Ring A] [Algebra K A] (M N : Submodule K A)
    [FiniteDimensional K M] [FiniteDimensional K N] :
    FiniteDimensional K ↥(M * N) ∧
      Module.finrank K ↥(M * N) ≤ Module.finrank K M * Module.finrank K N := by
  classical
  let bM := Module.finBasis K M
  let bN := Module.finBasis K N
  let f : Fin (Module.finrank K M) × Fin (Module.finrank K N) → A := fun p => (bM p.1 : A) * bN p.2
  have hle : M * N ≤ Submodule.span K (Set.range f) := by
    rw [Submodule.mul_le]
    intro m hm n hn
    have hm' : (⟨m, hm⟩ : M) = ∑ i, bM.repr ⟨m, hm⟩ i • bM i := (bM.sum_repr _).symm
    have hn' : (⟨n, hn⟩ : N) = ∑ j, bN.repr ⟨n, hn⟩ j • bN j := (bN.sum_repr _).symm
    have hm'' : m = ∑ i, bM.repr ⟨m, hm⟩ i • (bM i : A) := by
      have h := congrArg (fun z : M => (z : A)) hm'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    have hn'' : n = ∑ j, bN.repr ⟨n, hn⟩ j • (bN j : A) := by
      have h := congrArg (fun z : N => (z : A)) hn'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [hm'', hn'', Finset.sum_mul_sum]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    rw [smul_mul_smul_comm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have hfin : FiniteDimensional K ↥(Submodule.span K (Set.range f)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range f)
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  calc Module.finrank K ↥(M * N) ≤ Module.finrank K ↥(Submodule.span K (Set.range f)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank K M) × Fin (Module.finrank K N)) := finrank_range_le_card f
    _ = Module.finrank K M * Module.finrank K N := by simp

section Relation

variable {σ : Type*} [Fintype σ] {P : Ideal (MvPolynomial σ K)} {d : ℕ}
  (y : Fin (d + 1) → MvPolynomial σ K)

/-- The image modulo P of the degree-m forms in the y. -/
noncomputable abbrev linearSystemPowerImage (m : ℕ) : Submodule K (MvPolynomial σ K ⧸ P) :=
  (linearSystemPowerSpan y m).map (Ideal.Quotient.mkₐ K P).toLinearMap

instance linearSystemPowerImage_finiteDimensional (m : ℕ) :
    FiniteDimensional K (linearSystemPowerImage (P := P) y m) := by
  unfold linearSystemPowerImage linearSystemPowerSpan
  infer_instance

omit [Fintype σ] in
/-- A relation Φ(y) ∈ P of degree δ ≤ m kills Φ times the degree-(m - δ) forms. -/
theorem linearSystemPowerImage_finrank_add_le {Φ : MvPolynomial (Fin (d + 1)) K} {δ : ℕ}
    (hΦ : Φ.IsHomogeneous δ) (hΦ0 : Φ ≠ 0) (hΦP : aeval y Φ ∈ P) {m : ℕ} (hm : δ ≤ m) :
    Module.finrank K (linearSystemPowerImage (P := P) y m) +
        Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K (m - δ)) ≤
      Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m) := by
  set ψ : homogeneousSubmodule (Fin (d + 1)) K m →ₗ[K] MvPolynomial σ K ⧸ P :=
    (Ideal.Quotient.mkₐ K P).toLinearMap.comp
      ((aeval y).toLinearMap.comp (homogeneousSubmodule (Fin (d + 1)) K m).subtype) with hψ
  have hrange : LinearMap.range ψ = linearSystemPowerImage (P := P) y m := by
    unfold linearSystemPowerImage linearSystemPowerSpan
    rw [hψ, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  have hmul : ∀ f : homogeneousSubmodule (Fin (d + 1)) K (m - δ),
      Φ * (f : MvPolynomial (Fin (d + 1)) K) ∈ homogeneousSubmodule (Fin (d + 1)) K m := by
    intro f
    have h := hΦ.mul ((mem_homogeneousSubmodule _ _).mp f.2)
    rw [Nat.add_sub_cancel' hm] at h
    exact (mem_homogeneousSubmodule _ _).mpr h
  let μ : homogeneousSubmodule (Fin (d + 1)) K (m - δ) →ₗ[K]
      homogeneousSubmodule (Fin (d + 1)) K m :=
    LinearMap.codRestrict _ ((LinearMap.mulLeft K Φ).comp
      (homogeneousSubmodule (Fin (d + 1)) K (m - δ)).subtype) hmul
  have hμinj : Function.Injective μ := by
    intro f f' h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hΦ0 h')
  have hμker : LinearMap.range μ ≤ LinearMap.ker ψ := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk P (aeval y (Φ * (f : MvPolynomial (Fin (d + 1)) K))) = 0
    rw [map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact P.mul_mem_right _ hΦP
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hμrank := LinearMap.finrank_range_of_inj hμinj
  have hker := Submodule.finrank_mono hμker
  rw [hrange] at hrn
  omega

omit [Fintype σ] in
theorem linearSystemPowerImage_finrank_le (m : ℕ) :
    Module.finrank K (linearSystemPowerImage (P := P) y m) ≤
      Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m) := by
  unfold linearSystemPowerImage linearSystemPowerSpan
  exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_map_le _ _)

/-- The images modulo P of the forms of degree e. -/
noncomputable abbrev linearSystemFormImage (e : ℕ) : Submodule K (MvPolynomial σ K ⧸ P) :=
  (homogeneousSubmodule σ K e).map (Ideal.Quotient.mkₐ K P).toLinearMap

instance linearSystemFormImage_finiteDimensional (e : ℕ) :
    FiniteDimensional K (linearSystemFormImage (P := P) e) := by
  unfold linearSystemFormImage
  infer_instance

theorem linearSystemQuotientDim_eq_finrank_formImage (e : ℕ) :
    linearSystemQuotientDim P y 0 e = Module.finrank K (linearSystemFormImage (P := P) e) := by
  set ψ : homogeneousSubmodule σ K e →ₗ[K] MvPolynomial σ K ⧸ P :=
    (Ideal.Quotient.mkₐ K P).toLinearMap.comp (homogeneousSubmodule σ K e).subtype with hψ
  have hrange : LinearMap.range ψ = linearSystemFormImage (P := P) e := by
    rw [hψ, LinearMap.range_comp, Submodule.range_subtype]
  have hker : Module.finrank K (LinearMap.ker ψ) =
      Module.finrank K ↥(P.restrictScalars K ⊓ homogeneousSubmodule σ K e) := by
    have hk : LinearMap.ker ψ = (P.restrictScalars K ⊓ homogeneousSubmodule σ K e).comap
        (homogeneousSubmodule σ K e).subtype := by
      ext f
      simp only [hψ, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_comap, Submodule.mem_inf,
        Submodule.restrictScalars_mem, SetLike.coe_mem, and_true]
    rw [hk]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_right)
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, hker] at hrn
  unfold linearSystemQuotientDim
  rw [linearSystemFiltration_zero]
  omega

omit [Fintype σ] in
/-- The image modulo P of every form lies in the sum of the images of the low products. -/
theorem linearSystemFormImage_le_sum (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) (e : ℕ) :
    linearSystemFormImage (P := P) e ≤
      (range t).sup fun e' => linearSystemPowerImage (P := P) y (e - e') *
        linearSystemFormImage (P := P) e' := by
  have hgen := homogeneousSubmodule_le_linearSystemLowSpan y P hy hnull e
  unfold linearSystemFormImage
  refine (Submodule.map_mono hgen).trans ?_
  rw [Submodule.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨p, hp, rfl⟩
    have : (Ideal.Quotient.mkₐ K P).toLinearMap p = 0 := by
      change Ideal.Quotient.mk P p = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [this]
    exact Submodule.zero_mem _
  · unfold linearSystemLowSpan
    rw [Submodule.map_iSup]
    refine iSup_le fun e' => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun het => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun _ => ?_
    rw [Submodule.map_mul]
    exact Finset.le_sup (f := fun e' => linearSystemPowerImage (P := P) y (e - e') *
      linearSystemFormImage (P := P) e') (Finset.mem_range.mpr het)

omit [Fintype σ] in
theorem finrank_finsetSup_le {ι : Type*} (s : Finset ι) (M : ι → Submodule K (MvPolynomial σ K ⧸ P))
    [∀ i, FiniteDimensional K (M i)] :
    FiniteDimensional K ↥(s.sup M) ∧
      Module.finrank K ↥(s.sup M) ≤ ∑ i ∈ s, Module.finrank K (M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (∅ : Finset ι).sup M = ⊥ := Finset.sup_empty
    refine ⟨?_, ?_⟩
    · rw [h]
      infer_instance
    · rw [h, finrank_bot]
      exact Nat.zero_le _
  | insert i s his ih =>
    obtain ⟨hfin, hle⟩ := ih
    rw [Finset.sup_insert, Finset.sum_insert his]
    refine ⟨Submodule.finiteDimensional_sup _ _, ?_⟩
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left hle _)

/-- A relation among the parameters bounds the coordinate ring by one degree less. -/
theorem linearSystemQuotientDim_le_of_relation (hy : ∀ i, (y i).IsHomogeneous 1) (hd : 1 ≤ d)
    {t : ℕ} (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t)
    {Φ : MvPolynomial (Fin (d + 1)) K} {δ : ℕ} (hΦ : Φ.IsHomogeneous δ) (hΦ0 : Φ ≠ 0)
    (hΦP : aeval y Φ ∈ P) :
    ∃ C : ℕ, ∀ D, linearSystemQuotientDim P y 0 D ≤ C * (D + 1) ^ (d - 1) := by
  let C₀ := linearSystemConstant (Fin (d + 1)) K 1
  let B₀ := ∑ m ∈ range δ, Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m)
  let S₀ := ∑ e' ∈ range t, Module.finrank K (homogeneousSubmodule σ K e')
  have hpow : ∀ m D, m ≤ D → (m + 1) ^ (d - 1) ≤ (D + 1) ^ (d - 1) := fun m D h =>
    Nat.pow_le_pow_left (by omega) _
  have hone : ∀ D, 1 ≤ (D + 1) ^ (d - 1) := fun D => Nat.one_le_pow _ _ (by omega)
  have hF : ∀ m D, m ≤ D → Module.finrank K (linearSystemPowerImage (P := P) y m) ≤
      (C₀ * δ + B₀) * (D + 1) ^ (d - 1) := by
    intro m D hmD
    by_cases hm : δ ≤ m
    · have h1 := linearSystemPowerImage_finrank_add_le (P := P) y hΦ hΦ0 hΦP hm
      have h2 := homogeneousSubmodule_finrank_le_add (K := K) hd (m - δ) δ
      rw [Nat.sub_add_cancel hm] at h2
      have h3 := hpow m D hmD
      have h4 : C₀ * δ * (m + 1) ^ (d - 1) ≤ (C₀ * δ + B₀) * (D + 1) ^ (d - 1) :=
        (Nat.mul_le_mul_left _ h3).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      linarith
    · have h1 := linearSystemPowerImage_finrank_le (P := P) y m
      have h2 : Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m) ≤ B₀ :=
        Finset.single_le_sum (f := fun m => Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m))
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      calc Module.finrank K (linearSystemPowerImage (P := P) y m) ≤ B₀ := h1.trans h2
        _ = B₀ * 1 := (mul_one _).symm
        _ ≤ B₀ * (D + 1) ^ (d - 1) := Nat.mul_le_mul_left _ (hone D)
        _ ≤ (C₀ * δ + B₀) * (D + 1) ^ (d - 1) := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  refine ⟨(C₀ * δ + B₀) * S₀, fun D => ?_⟩
  rw [linearSystemQuotientDim_eq_finrank_formImage y D]
  have hle := linearSystemFormImage_le_sum (P := P) y hy hnull D
  have hprod : ∀ e' ∈ range t, FiniteDimensional K ↥(linearSystemPowerImage (P := P) y (D - e') *
        linearSystemFormImage (P := P) e') ∧
      Module.finrank K ↥(linearSystemPowerImage (P := P) y (D - e') * linearSystemFormImage (P := P) e') ≤
        (C₀ * δ + B₀) * (D + 1) ^ (d - 1) * Module.finrank K (homogeneousSubmodule σ K e') := by
    intro e' _
    obtain ⟨hfin, hmul⟩ := finrank_mul_le_mul (linearSystemPowerImage (P := P) y (D - e'))
      (linearSystemFormImage (P := P) e')
    refine ⟨hfin, hmul.trans ?_⟩
    exact Nat.mul_le_mul (hF (D - e') D (Nat.sub_le D e')) (Submodule.finrank_map_le _ _)
  have : ∀ e', FiniteDimensional K ↥(linearSystemPowerImage (P := P) y (D - e') *
      linearSystemFormImage (P := P) e') := fun e' =>
    (finrank_mul_le_mul (linearSystemPowerImage (P := P) y (D - e'))
      (linearSystemFormImage (P := P) e')).1
  obtain ⟨hsumfin, hsum⟩ := finrank_finsetSup_le (range t) fun e' =>
    linearSystemPowerImage (P := P) y (D - e') * linearSystemFormImage (P := P) e'
  calc Module.finrank K (linearSystemFormImage (P := P) D)
      ≤ Module.finrank K ↥((range t).sup fun e' => linearSystemPowerImage (P := P) y (D - e') *
          linearSystemFormImage (P := P) e') := Submodule.finrank_mono hle
    _ ≤ ∑ e' ∈ range t, Module.finrank K ↥(linearSystemPowerImage (P := P) y (D - e') *
          linearSystemFormImage (P := P) e') := hsum
    _ ≤ ∑ e' ∈ range t, (C₀ * δ + B₀) * (D + 1) ^ (d - 1) *
          Module.finrank K (homogeneousSubmodule σ K e') :=
        Finset.sum_le_sum fun e' he' => (hprod e' he').2
    _ = (C₀ * δ + B₀) * S₀ * (D + 1) ^ (d - 1) := by
        rw [← Finset.mul_sum]
        simp only [S₀]
        ring

end Relation

end MixedFujita

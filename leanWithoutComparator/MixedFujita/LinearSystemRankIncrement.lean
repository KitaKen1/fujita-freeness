/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemFreePart

/-!
Rank increment for the coordinate ring over the parameters, and the algebraic form of the
uniform growth of the restricted forms (Lemma 4 of the manuscript). A form f of degree k is
dependent on a finite set S of monomials if a nonzero form c in the parameters multiplies it
into the span of S over the parameters modulo P. Dependence is preserved by sums, by
multiplication with the parameters, by cancelling c, and by multiplication with a variable
X_i once every X_i b, b ∈ S, is dependent. Hence if no monomial of degree at most e can be
added to an independent set S of degree below e, every monomial is dependent on S, the low
monomials give one common denominator, and counting dimensions bounds the size of every
independent set by |S|. So below the rank r the independent monomials can be found one degree
at a time: there are min(r, D₀) independent monomials of degree below D₀, and their free
multiples give dim (K[X]/P)_q ≥ min(r, D₀) · C(q + 1 - D₀ + d, d). The bound depends only on
D₀, q and d. This replaces the generic finite projection, the separable generic fibre and the
choice of points on it.
-/

@[expose] public section

open MvPolynomial Finset Filter Asymptotics

namespace MixedFujita

variable {K : Type*} [Field K] {σ : Type*} {P : Ideal (MvPolynomial σ K)} {d : ℕ}
  (y : Fin (d + 1) → MvPolynomial σ K)

/-- f of degree k is dependent on S: a nonzero form in the parameters multiplies it into the
span of S over the parameters modulo P. -/
def LinearSystemDependent (P : Ideal (MvPolynomial σ K)) (S : Finset (σ →₀ ℕ)) (k : ℕ)
    (f : MvPolynomial σ K) : Prop :=
  ∃ (c : MvPolynomial (Fin (d + 1)) K) (j : ℕ), c.IsHomogeneous j ∧ c ≠ 0 ∧
    LinearSystemSpanned y P S (k + j) (aeval y c * f)

theorem linearSystemDependent_of_spanned {S : Finset (σ →₀ ℕ)} {k : ℕ} {f : MvPolynomial σ K}
    (h : LinearSystemSpanned y P S k f) : LinearSystemDependent y P S k f :=
  ⟨1, 0, isHomogeneous_one _ _, one_ne_zero, by simpa using h⟩

theorem linearSystemDependent_of_mem {S : Finset (σ →₀ ℕ)} {k : ℕ} {f : MvPolynomial σ K}
    (h : f ∈ P) : LinearSystemDependent y P S k f :=
  linearSystemDependent_of_spanned y (linearSystemSpanned_of_mem y h)

theorem linearSystemDependent_zero (S : Finset (σ →₀ ℕ)) (k : ℕ) :
    LinearSystemDependent y P S k 0 :=
  linearSystemDependent_of_mem y P.zero_mem

theorem linearSystemDependent_add {S : Finset (σ →₀ ℕ)} {k : ℕ} {f f' : MvPolynomial σ K}
    (hf : LinearSystemDependent y P S k f) (hf' : LinearSystemDependent y P S k f') :
    LinearSystemDependent y P S k (f + f') := by
  obtain ⟨c, j, hc, hc0, hcf⟩ := hf
  obtain ⟨c', j', hc', hc'0, hcf'⟩ := hf'
  refine ⟨c * c', j + j', hc.mul hc', mul_ne_zero hc0 hc'0, ?_⟩
  have h1 := linearSystemSpanned_mul y hc' hcf
  have h2 := linearSystemSpanned_mul y hc hcf'
  rw [show k + j + j' = k + (j + j') by omega] at h1
  rw [show k + j' + j = k + (j + j') by omega] at h2
  convert linearSystemSpanned_add y h1 h2 using 1
  simp only [map_mul]
  ring

theorem linearSystemDependent_smul {S : Finset (σ →₀ ℕ)} {k : ℕ} {f : MvPolynomial σ K} (a : K)
    (hf : LinearSystemDependent y P S k f) : LinearSystemDependent y P S k (a • f) := by
  obtain ⟨c, j, hc, hc0, hcf⟩ := hf
  refine ⟨c, j, hc, hc0, ?_⟩
  rw [mul_smul_comm]
  exact linearSystemSpanned_smul y a hcf

theorem linearSystemDependent_of_sub_mem {S : Finset (σ →₀ ℕ)} {k : ℕ} {f f' : MvPolynomial σ K}
    (hf : LinearSystemDependent y P S k f) (h : f' - f ∈ P) : LinearSystemDependent y P S k f' := by
  obtain ⟨c, j, hc, hc0, hcf⟩ := hf
  refine ⟨c, j, hc, hc0, linearSystemSpanned_of_sub_mem y hcf ?_⟩
  rw [← mul_sub]
  exact P.mul_mem_left _ h

theorem linearSystemDependent_mul {S : Finset (σ →₀ ℕ)} {k i : ℕ} {f : MvPolynomial σ K}
    {q : MvPolynomial (Fin (d + 1)) K} (hq : q.IsHomogeneous i)
    (hf : LinearSystemDependent y P S k f) : LinearSystemDependent y P S (k + i) (aeval y q * f) := by
  obtain ⟨c, j, hc, hc0, hcf⟩ := hf
  refine ⟨c, j, hc, hc0, ?_⟩
  have h := linearSystemSpanned_mul y hq hcf
  rw [show k + j + i = k + i + j by omega] at h
  convert h using 1
  ring

/-- A nonzero form in the parameters can be cancelled. -/
theorem linearSystemDependent_of_mul {S : Finset (σ →₀ ℕ)} {k j : ℕ} {f : MvPolynomial σ K}
    {c : MvPolynomial (Fin (d + 1)) K} (hc : c.IsHomogeneous j) (hc0 : c ≠ 0)
    (h : LinearSystemDependent y P S (k + j) (aeval y c * f)) : LinearSystemDependent y P S k f := by
  obtain ⟨c', j', hc', hc'0, hcf⟩ := h
  refine ⟨c' * c, j' + j, hc'.mul hc, mul_ne_zero hc'0 hc0, ?_⟩
  rw [show k + (j' + j) = k + j + j' by omega, map_mul, mul_assoc]
  exact hcf

theorem linearSystemDependent_sum {ι : Type*} (s : Finset ι) {S : Finset (σ →₀ ℕ)} {k : ℕ}
    {f : ι → MvPolynomial σ K} (h : ∀ i ∈ s, LinearSystemDependent y P S k (f i)) :
    LinearSystemDependent y P S k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact linearSystemDependent_zero y S k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact linearSystemDependent_add y (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A spanned element times X_i is dependent once every X_i b, b ∈ S, is. -/
theorem linearSystemDependent_X_mul_of_spanned {S : Finset (σ →₀ ℕ)} (i : σ) {m : ℕ}
    {g : MvPolynomial σ K}
    (hS : ∀ b ∈ S, LinearSystemDependent y P S (b.degree + 1) (X i * monomial b (1 : K)))
    (hg : LinearSystemSpanned y P S m g) : LinearSystemDependent y P S (m + 1) (X i * g) := by
  obtain ⟨c, hc, hcP⟩ := hg
  refine linearSystemDependent_of_sub_mem y
    (f := ∑ b ∈ S, aeval y (c b) * (X i * monomial b (1 : K))) ?_ ?_
  · refine linearSystemDependent_sum y S fun b hb => ?_
    have hcb := hc b hb
    unfold linearSystemCoeffSpace at hcb
    by_cases hle : b.degree ≤ m
    · simp only [hle, ↓reduceIte] at hcb
      have h := linearSystemDependent_mul y ((mem_homogeneousSubmodule _ _).mp hcb) (hS b hb)
      rwa [show b.degree + 1 + (m - b.degree) = m + 1 by omega] at h
    · simp only [hle, ↓reduceIte, Submodule.mem_bot] at hcb
      rw [hcb, map_zero, zero_mul]
      exact linearSystemDependent_zero y S (m + 1)
  · have h := P.mul_mem_left (X i) hcP
    have heq : X i * (g - ∑ b ∈ S, aeval y (c b) * monomial b (1 : K)) =
        X i * g - ∑ b ∈ S, aeval y (c b) * (X i * monomial b (1 : K)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun b _ => by ring
    rwa [heq] at h

/-- Dependence is preserved by multiplication with a variable. -/
theorem linearSystemDependent_X_mul {S : Finset (σ →₀ ℕ)} (i : σ) {k : ℕ} {f : MvPolynomial σ K}
    (hS : ∀ b ∈ S, LinearSystemDependent y P S (b.degree + 1) (X i * monomial b (1 : K)))
    (hf : LinearSystemDependent y P S k f) : LinearSystemDependent y P S (k + 1) (X i * f) := by
  obtain ⟨c, j, hc, hc0, hcf⟩ := hf
  have h := linearSystemDependent_X_mul_of_spanned y i hS hcf
  refine linearSystemDependent_of_mul y hc hc0 ?_
  rw [show k + 1 + j = k + j + 1 by omega]
  convert h using 1
  ring

/-- The monomials of an independent set are dependent on it. -/
theorem linearSystemDependent_of_mem_set {S : Finset (σ →₀ ℕ)} {α : σ →₀ ℕ} (hα : α ∈ S) :
    LinearSystemDependent y P S α.degree (monomial α (1 : K)) := by
  have h := linearSystemSpanned_basis (P := P) y hα le_rfl (q := 1)
    (by rw [Nat.sub_self]; exact isHomogeneous_one _ _)
  rw [map_one, one_mul] at h
  exact linearSystemDependent_of_spanned y h

/-- A monomial that cannot be added to an independent set is dependent on it. -/
theorem linearSystemDependent_of_not_independent [DecidableEq σ] {S : Finset (σ →₀ ℕ)}
    (hS : LinearSystemIndependent y P S) {α : σ →₀ ℕ} (hαS : α ∉ S)
    (hnot : ¬ LinearSystemIndependent y P (insert α S)) :
    LinearSystemDependent y P S α.degree (monomial α (1 : K)) := by
  simp only [LinearSystemIndependent, not_forall] at hnot
  obtain ⟨m, c, hc, hsum, b, hb, hcb⟩ := hnot
  rw [Finset.sum_insert hαS] at hsum
  have hcα : c α ≠ 0 := by
    intro hcα
    rw [hcα, map_zero, zero_mul, zero_add] at hsum
    have hall := hS m c (fun b hb => hc b (Finset.mem_insert_of_mem hb)) hsum
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · exact hcb hcα
    · exact hcb (hall b hb')
  have hα := hc α (Finset.mem_insert_self α S)
  unfold linearSystemCoeffSpace at hα
  by_cases hle : α.degree ≤ m
  · simp only [hle, ↓reduceIte] at hα
    refine ⟨c α, m - α.degree, (mem_homogeneousSubmodule _ _).mp hα, hcα, ?_⟩
    rw [show α.degree + (m - α.degree) = m by omega]
    refine ⟨fun b => -c b, fun b hb => Submodule.neg_mem _ (hc b (Finset.mem_insert_of_mem hb)), ?_⟩
    convert hsum using 1
    simp only [map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  · simp only [hle, ↓reduceIte, Submodule.mem_bot] at hα
    exact absurd hα hcα

/-- If S has degrees below e and every monomial of degree at most e is dependent on S, every
monomial is. -/
theorem linearSystemDependent_monomial {S : Finset (σ →₀ ℕ)} {e : ℕ}
    (hSe : ∀ b ∈ S, b.degree < e)
    (hlow : ∀ α : σ →₀ ℕ, α.degree ≤ e →
      LinearSystemDependent y P S α.degree (monomial α (1 : K))) :
    ∀ α : σ →₀ ℕ, LinearSystemDependent y P S α.degree (monomial α (1 : K)) := by
  classical
  have hX : ∀ (i : σ), ∀ b ∈ S,
      LinearSystemDependent y P S (b.degree + 1) (X i * monomial b (1 : K)) := by
    intro i b hb
    have hXb : X i * monomial b (1 : K) = monomial (Finsupp.single i 1 + b) (1 : K) := by
      rw [X, monomial_mul_monomial, mul_one]
    have hdeg : (Finsupp.single i 1 + b).degree = b.degree + 1 := by
      rw [map_add, Finsupp.degree_single, Nat.add_comm]
    have hbe := hSe b hb
    have h := hlow (Finsupp.single i 1 + b) (by omega)
    rw [hdeg] at h
    rwa [hXb]
  have key : ∀ k, ∀ α : σ →₀ ℕ, α.degree = k →
      LinearSystemDependent y P S k (monomial α (1 : K)) := by
    intro k
    induction k with
    | zero =>
      intro α hα
      have h := hlow α (by omega)
      rwa [hα] at h
    | succ k ih =>
      intro α hα
      by_cases hk : k + 1 ≤ e
      · have h := hlow α (by omega)
        rwa [hα] at h
      · have hsupp : α.support.Nonempty := by
          rw [Finsupp.support_nonempty_iff]
          rintro rfl
          have h0 : (0 : σ →₀ ℕ).degree = 0 := map_zero _
          omega
        obtain ⟨i, hi⟩ := hsupp
        have hle : Finsupp.single i 1 ≤ α :=
          Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
        set α' := α - Finsupp.single i 1 with hα'
        have hsum : α' + Finsupp.single i 1 = α := tsub_add_cancel_of_le hle
        have hdeg : α'.degree = k := by
          have h := congrArg Finsupp.degree hsum
          rw [map_add, Finsupp.degree_single, hα] at h
          omega
        have hmono : monomial α (1 : K) = X i * monomial α' (1 : K) := by
          rw [X, monomial_mul_monomial, mul_one, add_comm (Finsupp.single i 1) α', hsum]
        rw [hmono]
        exact linearSystemDependent_X_mul y i (hX i) (ih α' hdeg)
  exact fun α => key α.degree α rfl

section Counting

variable [Fintype σ]

/-- If every low monomial is dependent on S, one nonzero form in the parameters multiplies every
form into the span of S. -/
theorem linearSystem_commonDenominator_of_dependent (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t)
    {S : Finset (σ →₀ ℕ)}
    (hdep : ∀ α ∈ lowMonomials (σ := σ) t,
      LinearSystemDependent y P S α.degree (monomial α (1 : K))) :
    ∃ (δ : MvPolynomial (Fin (d + 1)) K) (k₀ : ℕ), δ.IsHomogeneous k₀ ∧ δ ≠ 0 ∧
      ∀ e, ∀ f ∈ homogeneousSubmodule σ K e,
        LinearSystemSpanned y P S (e + k₀) (aeval y δ * f) := by
  classical
  let G : Finset (σ →₀ ℕ) := lowMonomials t
  choose! cg jg hcg hcg0 hspanG using hdep
  let δ : MvPolynomial (Fin (d + 1)) K := ∏ γ ∈ G, cg γ
  let k₀ : ℕ := ∑ γ ∈ G, jg γ
  have hδ : δ.IsHomogeneous k₀ := IsHomogeneous.prod _ _ _ fun γ hγ => hcg γ hγ
  have hδ0 : δ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun γ hγ => hcg0 γ hγ
  refine ⟨δ, k₀, hδ, hδ0, ?_⟩
  -- The forms f with δ f spanned in degree e + k₀ form a subspace.
  let W : ℕ → Submodule K (MvPolynomial σ K) := fun e =>
    { carrier := {f | LinearSystemSpanned y P S (e + k₀) (aeval y δ * f)}
      add_mem' := fun {f f'} hf hf' => by
        simp only [Set.mem_ofPred_eq, mul_add] at hf hf' ⊢
        exact linearSystemSpanned_add y hf hf'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, mul_zero]
        exact linearSystemSpanned_zero y S _
      smul_mem' := fun a f hf => by
        simp only [Set.mem_ofPred_eq, mul_smul_comm] at hf ⊢
        exact linearSystemSpanned_smul y a hf }
  -- Each low monomial times a form in the parameters is spanned after multiplying by δ.
  have hmono : ∀ (e e' : ℕ), e' < t → e' ≤ e → ∀ γ : σ →₀ ℕ, γ.degree = e' →
      ∀ q : MvPolynomial (Fin (d + 1)) K, q.IsHomogeneous (e - e') →
        aeval y q * monomial γ (1 : K) ∈ W e := by
    intro e e' het hee γ hγ q hq
    change LinearSystemSpanned y P S (e + k₀) (aeval y δ * (aeval y q * monomial γ (1 : K)))
    have hγG : γ ∈ G := mem_lowMonomials.mpr (hγ ▸ het)
    let δ' : MvPolynomial (Fin (d + 1)) K := ∏ g ∈ G.erase γ, cg g
    have hδsplit : δ = cg γ * δ' := (Finset.mul_prod_erase G (fun g => cg g) hγG).symm
    let k₁ : ℕ := ∑ g ∈ G.erase γ, jg g
    have hk : k₀ = jg γ + k₁ := (Finset.add_sum_erase G (fun g => jg g) hγG).symm
    have hδ' : δ'.IsHomogeneous k₁ := IsHomogeneous.prod _ _ _ fun g hg =>
      hcg g (Finset.mem_of_mem_erase hg)
    have h := linearSystemSpanned_mul y (hq.mul hδ') (hspanG γ hγG)
    rw [show γ.degree + jg γ + (e - e' + k₁) = e + k₀ by omega] at h
    convert h using 1
    rw [hδsplit]
    simp only [map_mul]
    ring
  intro e f hf
  have hgen := homogeneousSubmodule_le_linearSystemLowSpan y P hy hnull e hf
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hgen
  change LinearSystemSpanned y P S (e + k₀) (aeval y δ * (p + l))
  rw [mul_add]
  refine linearSystemSpanned_add y (linearSystemSpanned_of_mem y (P.mul_mem_left _ hp)) ?_
  change l ∈ W e
  have hlow : linearSystemLowSpan y t e ≤ W e := by
    unfold linearSystemLowSpan
    refine iSup_le fun e' => iSup_le fun het => iSup_le fun hee => ?_
    rw [Submodule.mul_le]
    intro q' hq' h hh
    obtain ⟨q, hq, rfl⟩ := hq'
    have hhW : h ∈ (W e).comap (LinearMap.mulLeft K ((aeval y).toLinearMap q)) := by
      refine homogeneousSubmodule_le_of_monomials (fun γ hγ => ?_) hh
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      exact hmono e e' het hee γ hγ q ((mem_homogeneousSubmodule _ _).mp hq)
    exact hhW
  exact hlow hl

/-- Counting: an independent set is no larger than a set over which one common denominator
spans every form. -/
theorem linearSystemIndependent_card_le [P.IsPrime] (hy : ∀ i, (y i).IsHomogeneous 1)
    {B S : Finset (σ →₀ ℕ)} (hB : LinearSystemIndependent y P B)
    {δ : MvPolynomial (Fin (d + 1)) K} {k₀ : ℕ} (hδP : aeval y δ ∉ P)
    (hspan : ∀ e, ∀ f ∈ homogeneousSubmodule σ K e,
      LinearSystemSpanned y P S (e + k₀) (aeval y δ * f)) :
    B.card ≤ S.card := by
  classical
  set T : ℕ := B.sup Finsupp.degree + 1 with hT
  have hBT : ∀ b ∈ B, b.degree < T := fun b hb =>
    Nat.lt_succ_of_le (Finset.le_sup (f := Finsupp.degree) hb)
  have hcomb : ∀ m, B.card * (m + 0 + d).choose d ≤ S.card * (m + (T + k₀) + d).choose d := by
    intro m
    have hlow : B.card * (m + 0 + d).choose d ≤
        Module.finrank K (linearSystemFormImage (P := P) (m + T)) := by
      refine le_trans ?_ (linearSystem_freePart_le y hy hB (m + T))
      rw [Finset.card_eq_sum_ones, Finset.sum_mul]
      refine Finset.sum_le_sum fun b hb => ?_
      have hbT := hBT b hb
      rw [one_mul, ite_eq_left (show b.degree ≤ m + T by omega)]
      exact Nat.choose_le_choose d (by omega)
    have hup : Module.finrank K (linearSystemFormImage (P := P) (m + T)) ≤
        S.card * (m + (T + k₀) + d).choose d := by
      refine (linearSystem_formImage_le_freePart y hδP hspan (m + T)).trans ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_mul]
      refine Finset.sum_le_sum fun b _ => ?_
      rw [one_mul]
      split_ifs
      · exact Nat.choose_le_choose d (by omega)
      · exact Nat.zero_le _
    exact hlow.trans hup
  -- divide by the binomial coefficient and let m → ∞
  have hequiv := (isEquivalent_choose_shift d (T + k₀)).trans (isEquivalent_choose_shift d 0).symm
  have hne : ∀ᶠ m : ℕ in atTop, ((m + 0 + d).choose d : ℝ) ≠ 0 :=
    Eventually.of_forall fun m => by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hratio := ((isEquivalent_iff_tendsto_one hne).mp hequiv).const_mul (S.card : ℝ)
  rw [mul_one] at hratio
  have hle : ∀ m : ℕ, (B.card : ℝ) ≤ (S.card : ℝ) *
      ((fun m : ℕ => ((m + (T + k₀) + d).choose d : ℝ)) /
        (fun m : ℕ => ((m + 0 + d).choose d : ℝ))) m := by
    intro m
    have hpos : (0 : ℝ) < ((m + 0 + d).choose d : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [Pi.div_apply, mul_div_assoc', le_div_iff₀ hpos]
    exact_mod_cast hcomb m
  exact_mod_cast ge_of_tendsto' hratio hle

/-- Rank increment: below the size of an independent set B, independent monomials can be found
one degree at a time. -/
theorem linearSystem_rank_increment [P.IsPrime] (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t)
    (hpar : ∀ (Φ : MvPolynomial (Fin (d + 1)) K) (k : ℕ), Φ.IsHomogeneous k → Φ ≠ 0 →
      aeval y Φ ∉ P)
    {B : Finset (σ →₀ ℕ)} (hB : LinearSystemIndependent y P B) (e : ℕ) :
    ∃ S : Finset (σ →₀ ℕ), LinearSystemIndependent y P S ∧ (∀ b ∈ S, b.degree < e) ∧
      min B.card e ≤ S.card := by
  classical
  induction e with
  | zero =>
    exact ⟨∅, fun _ _ _ _ b hb => absurd hb (Finset.notMem_empty b),
      fun b hb => absurd hb (Finset.notMem_empty b), by simp⟩
  | succ e ih =>
    obtain ⟨S, hS, hSe, hcard⟩ := ih
    by_cases hfull : B.card ≤ S.card
    · exact ⟨S, hS, fun b hb => Nat.lt_succ_of_lt (hSe b hb), (min_le_left _ _).trans hfull⟩
    push Not at hfull
    have he : e ≤ S.card := by
      rcases min_choice B.card e with h | h <;> rw [h] at hcard <;> omega
    by_cases hext : ∃ α : σ →₀ ℕ, α.degree ≤ e ∧ α ∉ S ∧ LinearSystemIndependent y P (insert α S)
    · obtain ⟨α, hα, hαS, hind⟩ := hext
      refine ⟨insert α S, hind, fun b hb => ?_, ?_⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb'
        · omega
        · exact Nat.lt_succ_of_lt (hSe b hb')
      · rw [Finset.card_insert_of_notMem hαS]
        exact (min_le_right _ _).trans (by omega)
    · exfalso
      push Not at hext
      have hlow : ∀ α : σ →₀ ℕ, α.degree ≤ e →
          LinearSystemDependent y P S α.degree (monomial α (1 : K)) := by
        intro α hα
        by_cases hαS : α ∈ S
        · exact linearSystemDependent_of_mem_set y hαS
        · exact linearSystemDependent_of_not_independent y hS hαS (hext α hα hαS)
      have hall := linearSystemDependent_monomial y hSe hlow
      obtain ⟨δ, k₀, hδ, hδ0, hspan⟩ :=
        linearSystem_commonDenominator_of_dependent y hy hnull (fun α _ => hall α)
      have := linearSystemIndependent_card_le y hy hB (hpar δ k₀ hδ hδ0) hspan
      omega

/-- Lemma 4, algebraic form: the degree-q part of the coordinate ring has dimension at least
min(r, D₀) · C(q + 1 - D₀ + d, d) for every independent set of size r. -/
theorem linearSystem_formImage_uniform_lower [P.IsPrime] (hy : ∀ i, (y i).IsHomogeneous 1)
    {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t)
    (hpar : ∀ (Φ : MvPolynomial (Fin (d + 1)) K) (k : ℕ), Φ.IsHomogeneous k → Φ ≠ 0 →
      aeval y Φ ∉ P)
    {B : Finset (σ →₀ ℕ)} (hB : LinearSystemIndependent y P B) {D₀ q : ℕ} (hq : D₀ ≤ q + 1) :
    min B.card D₀ * (q + 1 - D₀ + d).choose d ≤
      Module.finrank K (linearSystemFormImage (P := P) q) := by
  obtain ⟨S, hS, hSdeg, hcard⟩ := linearSystem_rank_increment y hy hnull hpar hB D₀
  refine le_trans ?_ (linearSystem_freePart_le y hy hS q)
  calc min B.card D₀ * (q + 1 - D₀ + d).choose d ≤ S.card * (q + 1 - D₀ + d).choose d :=
        Nat.mul_le_mul_right _ hcard
    _ = ∑ _b ∈ S, (q + 1 - D₀ + d).choose d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ b ∈ S, (if b.degree ≤ q then (q - b.degree + d).choose d else 0) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have hb := hSdeg b hb
        rw [ite_eq_left (show b.degree ≤ q by omega)]
        exact Nat.choose_le_choose d (by omega)

end Counting

end MixedFujita

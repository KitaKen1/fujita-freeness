/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemGeneration
public import Mathlib.Algebra.MvPolynomial.Division

/-!
A common denominator for the coordinate ring over the parameters, and the intersection of
two parameter charts. Among the monomials of degree below t, choose a maximal set B that is
independent over the polynomial ring R in the parameters, degree by degree, modulo P. Every
other low monomial has a homogeneous relation over B with a nonzero leading coefficient; the
product δ of these coefficients multiplies every form into the span of B over R modulo P.
If a form a₀ is congruent to y_0^N times something on the y_1-side, comparing coefficients
over B gives Y_1^N c₀ = Y_0^N c₁ in R, so Y_0^N divides c₀ because distinct variables are
prime and coprime. This replaces the finiteness of the section ring over the coordinate
ring, with no Serre theorem, cohomology or normalization.
-/

@[expose] public section

open MvPolynomial Finset

namespace MixedFujita

variable {K : Type*} [Field K] {σ : Type*} {P : Ideal (MvPolynomial σ K)} {d : ℕ}
  (y : Fin (d + 1) → MvPolynomial σ K)

variable (d) in
/-- The admissible coefficients of the monomial b in degree m. -/
noncomputable def linearSystemCoeffSpace (m : ℕ) (b : σ →₀ ℕ) :
    Submodule K (MvPolynomial (Fin (d + 1)) K) :=
  if b.degree ≤ m then homogeneousSubmodule (Fin (d + 1)) K (m - b.degree) else ⊥

/-- Graded independence of finitely many monomials over the parameters modulo P. -/
def LinearSystemIndependent (P : Ideal (MvPolynomial σ K)) (B : Finset (σ →₀ ℕ)) : Prop :=
  ∀ (m : ℕ) (c : (σ →₀ ℕ) → MvPolynomial (Fin (d + 1)) K),
    (∀ b ∈ B, c b ∈ linearSystemCoeffSpace d m b) →
    ∑ b ∈ B, aeval y (c b) * monomial b (1 : K) ∈ P → ∀ b ∈ B, c b = 0

/-- Degree-m elements congruent modulo P to a combination of B over the parameters. -/
def LinearSystemSpanned (P : Ideal (MvPolynomial σ K)) (B : Finset (σ →₀ ℕ)) (m : ℕ)
    (f : MvPolynomial σ K) : Prop :=
  ∃ c : (σ →₀ ℕ) → MvPolynomial (Fin (d + 1)) K,
    (∀ b ∈ B, c b ∈ linearSystemCoeffSpace d m b) ∧
      f - ∑ b ∈ B, aeval y (c b) * monomial b (1 : K) ∈ P

theorem linearSystemCoeffSpace_mul {m k : ℕ} {b : σ →₀ ℕ} {c q : MvPolynomial (Fin (d + 1)) K}
    (hc : c ∈ linearSystemCoeffSpace d m b) (hq : q.IsHomogeneous k) :
    q * c ∈ linearSystemCoeffSpace d (m + k) b := by
  unfold linearSystemCoeffSpace at hc ⊢
  by_cases hb : b.degree ≤ m
  · have hb' : b.degree ≤ m + k := by omega
    simp only [hb, hb', ↓reduceIte] at hc ⊢
    have h := hq.mul ((mem_homogeneousSubmodule _ _).mp hc)
    rw [show k + (m - b.degree) = m + k - b.degree by omega] at h
    exact (mem_homogeneousSubmodule _ _).mpr h
  · simp only [hb, ↓reduceIte, Submodule.mem_bot] at hc
    rw [hc, mul_zero]
    exact Submodule.zero_mem _

theorem linearSystemSpanned_zero (B : Finset (σ →₀ ℕ)) (m : ℕ) :
    LinearSystemSpanned y P B m 0 :=
  ⟨0, fun _ _ => Submodule.zero_mem _, by simp⟩

theorem linearSystemSpanned_add {B : Finset (σ →₀ ℕ)} {m : ℕ} {f f' : MvPolynomial σ K}
    (hf : LinearSystemSpanned y P B m f) (hf' : LinearSystemSpanned y P B m f') :
    LinearSystemSpanned y P B m (f + f') := by
  obtain ⟨c, hc, hcP⟩ := hf
  obtain ⟨c', hc', hc'P⟩ := hf'
  refine ⟨c + c', fun b hb => Submodule.add_mem _ (hc b hb) (hc' b hb), ?_⟩
  have h := P.add_mem hcP hc'P
  convert h using 1
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem linearSystemSpanned_smul {B : Finset (σ →₀ ℕ)} {m : ℕ} {f : MvPolynomial σ K} (a : K)
    (hf : LinearSystemSpanned y P B m f) : LinearSystemSpanned y P B m (a • f) := by
  obtain ⟨c, hc, hcP⟩ := hf
  refine ⟨a • c, fun b hb => Submodule.smul_mem _ a (hc b hb), ?_⟩
  have h := P.mul_mem_left (C a) hcP
  convert h using 1
  simp only [Pi.smul_apply, smul_eq_C_mul, map_mul, aeval_C, MvPolynomial.algebraMap_eq, mul_sub,
    Finset.mul_sum, mul_assoc]

theorem linearSystemSpanned_of_sub_mem {B : Finset (σ →₀ ℕ)} {m : ℕ} {f f' : MvPolynomial σ K}
    (hf : LinearSystemSpanned y P B m f) (h : f' - f ∈ P) : LinearSystemSpanned y P B m f' := by
  obtain ⟨c, hc, hcP⟩ := hf
  refine ⟨c, hc, ?_⟩
  have := P.add_mem h hcP
  simpa using this

theorem linearSystemSpanned_of_mem {B : Finset (σ →₀ ℕ)} {m : ℕ} {f : MvPolynomial σ K}
    (h : f ∈ P) : LinearSystemSpanned y P B m f :=
  linearSystemSpanned_of_sub_mem y (linearSystemSpanned_zero y B m) (by simpa using h)

theorem linearSystemSpanned_mul {B : Finset (σ →₀ ℕ)} {m k : ℕ} {f : MvPolynomial σ K}
    {q : MvPolynomial (Fin (d + 1)) K} (hq : q.IsHomogeneous k)
    (hf : LinearSystemSpanned y P B m f) : LinearSystemSpanned y P B (m + k) (aeval y q * f) := by
  obtain ⟨c, hc, hcP⟩ := hf
  refine ⟨fun b => q * c b, fun b hb => linearSystemCoeffSpace_mul (hc b hb) hq, ?_⟩
  have h := P.mul_mem_left (aeval y q) hcP
  convert h using 1
  simp only [map_mul, mul_sub, Finset.mul_sum, mul_assoc]

theorem linearSystemSpanned_basis {B : Finset (σ →₀ ℕ)} {m : ℕ} {b : σ →₀ ℕ} (hb : b ∈ B)
    (hbm : b.degree ≤ m) {q : MvPolynomial (Fin (d + 1)) K} (hq : q.IsHomogeneous (m - b.degree)) :
    LinearSystemSpanned y P B m (aeval y q * monomial b (1 : K)) := by
  classical
  refine ⟨Pi.single b q, fun b' _ => ?_, ?_⟩
  · by_cases h : b' = b
    · subst h
      rw [Pi.single_eq_same]
      unfold linearSystemCoeffSpace
      simp only [hbm, ↓reduceIte]
      exact (mem_homogeneousSubmodule _ _).mpr hq
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  · rw [Finset.sum_eq_single b (fun b' _ hb' => by rw [Pi.single_eq_of_ne hb', map_zero, zero_mul])
      (fun h => absurd hb h), Pi.single_eq_same, sub_self]
    exact P.zero_mem

/-- A combination over B with admissible coefficients is a form of degree m. -/
theorem linearSystemSum_isHomogeneous (hy : ∀ i, (y i).IsHomogeneous 1) {B : Finset (σ →₀ ℕ)}
    {m : ℕ} {c : (σ →₀ ℕ) → MvPolynomial (Fin (d + 1)) K}
    (hc : ∀ b ∈ B, c b ∈ linearSystemCoeffSpace d m b) :
    (∑ b ∈ B, aeval y (c b) * monomial b (1 : K)).IsHomogeneous m := by
  apply IsHomogeneous.sum
  intro b hb
  have h := hc b hb
  unfold linearSystemCoeffSpace at h
  by_cases hle : b.degree ≤ m
  · simp only [hle, ↓reduceIte] at h
    have h1 := ((mem_homogeneousSubmodule _ _).mp h).aeval y hy
    rw [one_mul] at h1
    have h2 := h1.mul (isHomogeneous_monomial (1 : K) (rfl : b.degree = b.degree))
    rwa [Nat.sub_add_cancel hle] at h2
  · simp only [hle, ↓reduceIte, Submodule.mem_bot] at h
    rw [h, map_zero, zero_mul]
    exact isHomogeneous_zero _ _ _

section Denominator

variable [Fintype σ]

/-- The finite set of monomials of degree below t. -/
noncomputable def lowMonomials (t : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact ((Fintype.piFinset fun _ : σ => Finset.range t).image Finsupp.equivFunOnFinite.symm).filter
    fun α => α.degree < t

theorem mem_lowMonomials {t : ℕ} {α : σ →₀ ℕ} : α ∈ lowMonomials t ↔ α.degree < t := by
  classical
  unfold lowMonomials
  simp only [Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    refine ⟨⟨α, fun i => ?_, by simp⟩, h⟩
    exact lt_of_le_of_lt (Finsupp.le_degree i α) h

/-- A maximal independent set of low monomials and a common denominator. -/
theorem linearSystem_exists_commonDenominator (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : σ →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration P y (d + 1) t) :
    ∃ (B : Finset (σ →₀ ℕ)) (δ : MvPolynomial (Fin (d + 1)) K) (k₀ : ℕ),
      δ.IsHomogeneous k₀ ∧ δ ≠ 0 ∧ LinearSystemIndependent y P B ∧ (∀ b ∈ B, b.degree < t) ∧
      ∀ e, ∀ f ∈ homogeneousSubmodule σ K e,
        LinearSystemSpanned y P B (e + k₀) (aeval y δ * f) := by
  classical
  let G₀ : Finset (σ →₀ ℕ) := lowMonomials t
  have hempty : (∅ : Finset (σ →₀ ℕ)) ∈ G₀.powerset.filter (LinearSystemIndependent y P) := by
    refine Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, ?_⟩
    intro m c _ _ b hb
    exact absurd hb (Finset.notMem_empty b)
  obtain ⟨B, hBmem, hBmax⟩ := Finset.exists_max_image
    (G₀.powerset.filter (LinearSystemIndependent y P)) Finset.card ⟨∅, hempty⟩
  have hBsub : B ⊆ G₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hBmem).1
  have hBind : LinearSystemIndependent y P B := (Finset.mem_filter.mp hBmem).2
  have hdep : ∀ g ∈ G₀, g ∉ B → ∃ (m : ℕ) (c : (σ →₀ ℕ) → MvPolynomial (Fin (d + 1)) K),
      (∀ b ∈ insert g B, c b ∈ linearSystemCoeffSpace d m b) ∧
        ∑ b ∈ insert g B, aeval y (c b) * monomial b (1 : K) ∈ P ∧ c g ≠ 0 := by
    intro g hg hgB
    have hnot : ¬ LinearSystemIndependent y P (insert g B) := by
      intro hind
      have h := hBmax (insert g B) (Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.insert_subset hg hBsub), hind⟩)
      rw [Finset.card_insert_of_notMem hgB] at h
      omega
    simp only [LinearSystemIndependent, not_forall] at hnot
    obtain ⟨m, c, hc, hsum, b, hb, hcb⟩ := hnot
    refine ⟨m, c, hc, hsum, fun hcg => ?_⟩
    rw [Finset.sum_insert hgB, hcg, map_zero, zero_mul, zero_add] at hsum
    have hall := hBind m c (fun b hb => hc b (Finset.mem_insert_of_mem hb)) hsum
    rcases Finset.mem_insert.mp hb with rfl | hb'
    · exact hcb hcg
    · exact hcb (hall b hb')
  choose! mg cg hcg hsumg hcgne using hdep
  let Dg : Finset (σ →₀ ℕ) := G₀ \ B
  have hDg : ∀ g ∈ Dg, g ∈ G₀ ∧ g ∉ B := fun g hg => Finset.mem_sdiff.mp hg
  have hdegg : ∀ g ∈ Dg, g.degree ≤ mg g ∧ (cg g g).IsHomogeneous (mg g - g.degree) := by
    intro g hg
    obtain ⟨hgG, hgB⟩ := hDg g hg
    have h := hcg g hgG hgB g (Finset.mem_insert_self g B)
    unfold linearSystemCoeffSpace at h
    by_cases hle : g.degree ≤ mg g
    · simp only [hle, ↓reduceIte] at h
      exact ⟨hle, (mem_homogeneousSubmodule _ _).mp h⟩
    · simp only [hle, ↓reduceIte, Submodule.mem_bot] at h
      exact absurd h (hcgne g hgG hgB)
  let δ : MvPolynomial (Fin (d + 1)) K := ∏ g ∈ Dg, cg g g
  let k₀ : ℕ := ∑ g ∈ Dg, (mg g - g.degree)
  have hδ : δ.IsHomogeneous k₀ := IsHomogeneous.prod _ _ _ fun g hg => (hdegg g hg).2
  have hδ0 : δ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun g hg => hcgne g (hDg g hg).1 (hDg g hg).2
  refine ⟨B, δ, k₀, hδ, hδ0, hBind, fun b hb => mem_lowMonomials.mp (hBsub hb), ?_⟩
  -- The forms f with δ f spanned in degree e + k₀ form a subspace.
  let W : ℕ → Submodule K (MvPolynomial σ K) := fun e =>
    { carrier := {f | LinearSystemSpanned y P B (e + k₀) (aeval y δ * f)}
      add_mem' := fun {f f'} hf hf' => by
        simp only [Set.mem_ofPred_eq, mul_add] at hf hf' ⊢
        exact linearSystemSpanned_add y hf hf'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, mul_zero]
        exact linearSystemSpanned_zero y B _
      smul_mem' := fun a f hf => by
        simp only [Set.mem_ofPred_eq, mul_smul_comm] at hf ⊢
        exact linearSystemSpanned_smul y a hf }
  -- Each low monomial times a form in the parameters is spanned after multiplying by δ.
  have hmono : ∀ (e e' : ℕ), e' < t → e' ≤ e → ∀ γ : σ →₀ ℕ, γ.degree = e' →
      ∀ q : MvPolynomial (Fin (d + 1)) K, q.IsHomogeneous (e - e') →
        aeval y q * monomial γ (1 : K) ∈ W e := by
    intro e e' het hee γ hγ q hq
    change LinearSystemSpanned y P B (e + k₀) (aeval y δ * (aeval y q * monomial γ (1 : K)))
    have hγG : γ ∈ G₀ := mem_lowMonomials.mpr (hγ ▸ het)
    by_cases hγB : γ ∈ B
    · rw [← mul_assoc, ← map_mul]
      refine linearSystemSpanned_basis y hγB (by omega) ?_
      have h := hδ.mul hq
      rw [show k₀ + (e - e') = e + k₀ - γ.degree by omega] at h
      exact h
    · have hγD : γ ∈ Dg := Finset.mem_sdiff.mpr ⟨hγG, hγB⟩
      obtain ⟨hγle, hγhom⟩ := hdegg γ hγD
      let δ' : MvPolynomial (Fin (d + 1)) K := ∏ g ∈ Dg.erase γ, cg g g
      have hδsplit : δ = cg γ γ * δ' := (Finset.mul_prod_erase Dg (fun g => cg g g) hγD).symm
      let k₁ : ℕ := ∑ g ∈ Dg.erase γ, (mg g - g.degree)
      have hk : k₀ = (mg γ - γ.degree) + k₁ :=
        (Finset.add_sum_erase Dg (fun g => mg g - g.degree) hγD).symm
      have hδ' : δ'.IsHomogeneous k₁ := IsHomogeneous.prod _ _ _ fun g hg =>
        (hdegg g (Finset.mem_of_mem_erase hg)).2
      -- the relation of γ over B
      have hrel := hsumg γ hγG hγB
      rw [Finset.sum_insert hγB] at hrel
      -- δ q X^γ ≡ - q δ' Σ_b c_γ(b) X^b
      have hspan : LinearSystemSpanned y P B (e + k₀)
          (aeval y (q * δ') * (-(∑ b ∈ B, aeval y (cg γ b) * monomial b (1 : K)))) := by
        refine ⟨fun b => -(q * δ' * cg γ b), fun b hb => ?_, ?_⟩
        · refine Submodule.neg_mem _ ?_
          have h := linearSystemCoeffSpace_mul (hcg γ hγG hγB b (Finset.mem_insert_of_mem hb))
            (hq.mul hδ')
          rw [show mg γ + (e - e' + k₁) = e + k₀ by omega] at h
          exact h
        · have hsum : aeval y (q * δ') * (-(∑ b ∈ B, aeval y (cg γ b) * monomial b (1 : K))) =
              ∑ b ∈ B, aeval y (-(q * δ' * cg γ b)) * monomial b (1 : K) := by
            rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [map_neg, map_mul]
            ring
          rw [hsum, sub_self]
          exact P.zero_mem
      refine linearSystemSpanned_of_sub_mem y hspan ?_
      have h := P.mul_mem_left (aeval y (q * δ')) hrel
      convert h using 1
      simp only [hδsplit, map_mul]
      ring
  intro e f hf
  have hgen := homogeneousSubmodule_le_linearSystemLowSpan y P hy hnull e hf
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hgen
  change LinearSystemSpanned y P B (e + k₀) (aeval y δ * (p + l))
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

end Denominator

theorem isHomogeneous_of_X_pow_mul {τ : Type*} {i : τ} {N k : ℕ} {p : MvPolynomial τ K}
    (h : (X i ^ N * p).IsHomogeneous k) : p.IsHomogeneous (k - N) := by
  intro m hm
  have hc : (X i ^ N * p).coeff (Finsupp.single i N + m) ≠ 0 := by
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact hm
  have hw := h hc
  have hdeg : (Finsupp.single i N + m).degree = k := by
    rw [Finsupp.degree_eq_weight_one]
    exact hw
  rw [map_add, Finsupp.degree_single] at hdeg
  have h2 : (Finsupp.weight fun _ : τ => (1 : ℕ)) m = k - N := by
    rw [← Finsupp.degree_eq_weight_one]
    omega
  exact h2

theorem le_of_isHomogeneous_X_pow_mul {τ : Type*} {i : τ} {N k : ℕ} {p : MvPolynomial τ K}
    (hp : p ≠ 0) (h : (X i ^ N * p).IsHomogeneous k) : N ≤ k := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hp
  have hc : (X i ^ N * p).coeff (Finsupp.single i N + m) ≠ 0 := by
    rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact hm
  have hw := h hc
  have hdeg : (Finsupp.single i N + m).degree = k := by
    rw [Finsupp.degree_eq_weight_one]
    exact hw
  rw [map_add, Finsupp.degree_single] at hdeg
  omega

/-- Intersection of two parameter charts: a form congruent over B on both the y_0- and the
y_1-side is y_0^N times a form spanned over B. -/
theorem linearSystem_intersection (hy : ∀ i, (y i).IsHomogeneous 1) (hd : 1 ≤ d)
    {B : Finset (σ →₀ ℕ)}
    (hB : LinearSystemIndependent y P B) {N D' : ℕ} {a₀ a₁ : MvPolynomial σ K}
    (h₀ : LinearSystemSpanned y P B (N + D') a₀) (h₁ : LinearSystemSpanned y P B (N + D') a₁)
    (hcross : y ⟨1, by omega⟩ ^ N * a₀ - y 0 ^ N * a₁ ∈ P) :
    ∃ G : MvPolynomial σ K, G.IsHomogeneous D' ∧ a₀ - y 0 ^ N * G ∈ P := by
  classical
  obtain ⟨c₀, hc₀, hc₀P⟩ := h₀
  obtain ⟨c₁, hc₁, hc₁P⟩ := h₁
  set i₁ : Fin (d + 1) := ⟨1, by omega⟩
  -- the cross relation over B
  have hrel : ∑ b ∈ B, aeval y (X i₁ ^ N * c₀ b - X 0 ^ N * c₁ b) * monomial b (1 : K) ∈ P := by
    have h := P.add_mem (P.sub_mem hcross (P.mul_mem_left (y i₁ ^ N) hc₀P))
      (P.mul_mem_left (y 0 ^ N) hc₁P)
    convert h using 1
    simp only [map_sub, map_mul, map_pow, aeval_X, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum,
      mul_assoc]
    ring
  have hcoef : ∀ b ∈ B, X i₁ ^ N * c₀ b - X 0 ^ N * c₁ b ∈ linearSystemCoeffSpace d (N + (N + D')) b := by
    intro b hb
    refine Submodule.sub_mem _ ?_ ?_
    · have h := linearSystemCoeffSpace_mul (hc₀ b hb) (isHomogeneous_X_pow i₁ N)
      rwa [show N + D' + N = N + (N + D') by omega] at h
    · have h := linearSystemCoeffSpace_mul (hc₁ b hb) (isHomogeneous_X_pow (0 : Fin (d + 1)) N)
      rwa [show N + D' + N = N + (N + D') by omega] at h
  have heq : ∀ b ∈ B, X i₁ ^ N * c₀ b = X 0 ^ N * c₁ b := fun b hb =>
    sub_eq_zero.mp (hB _ _ hcoef hrel b hb)
  -- Y_0^N divides c₀ b
  have hprime : Prime (X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) K) := X_prime
  have hndvd : ¬ (X (0 : Fin (d + 1)) : MvPolynomial (Fin (d + 1)) K) ∣ X i₁ ^ N := by
    intro h
    have h' := hprime.dvd_of_dvd_pow h
    rw [X_dvd_X] at h'
    exact absurd (congrArg Fin.val h') (by simp [i₁])
  have hdvd : ∀ b ∈ B, X 0 ^ N ∣ c₀ b := fun b hb =>
    hprime.pow_dvd_of_dvd_mul_left N hndvd ⟨c₁ b, (heq b hb)⟩
  choose! e₀ he₀ using hdvd
  -- the quotients are admissible coefficients in degree D'
  have he₀coef : ∀ b ∈ B, e₀ b ∈ linearSystemCoeffSpace d D' b := by
    intro b hb
    have hcb := hc₀ b hb
    rw [he₀ b hb] at hcb
    unfold linearSystemCoeffSpace at hcb ⊢
    by_cases hle : b.degree ≤ D'
    · have hle' : b.degree ≤ N + D' := by omega
      simp only [hle, hle', ↓reduceIte] at hcb ⊢
      by_cases he0 : e₀ b = 0
      · rw [he0]
        exact Submodule.zero_mem _
      · have hprod := (mem_homogeneousSubmodule _ _).mp hcb
        have h := isHomogeneous_of_X_pow_mul hprod
        rw [show N + D' - b.degree - N = D' - b.degree by omega] at h
        exact (mem_homogeneousSubmodule _ _).mpr h
    · simp only [hle, ↓reduceIte, Submodule.mem_bot]
      by_cases hle' : b.degree ≤ N + D'
      · simp only [hle', ↓reduceIte] at hcb
        by_contra he0
        have hprod := (mem_homogeneousSubmodule _ _).mp hcb
        have hdeg := le_of_isHomogeneous_X_pow_mul he0 hprod
        omega
      · simp only [hle', ↓reduceIte, Submodule.mem_bot] at hcb
        exact (mul_eq_zero.mp hcb).resolve_left (pow_ne_zero N (X_ne_zero 0))
  refine ⟨∑ b ∈ B, aeval y (e₀ b) * monomial b (1 : K), linearSystemSum_isHomogeneous y hy he₀coef, ?_⟩
  convert hc₀P using 1
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [he₀ b hb, map_mul, map_pow, aeval_X]
  ring

end MixedFujita

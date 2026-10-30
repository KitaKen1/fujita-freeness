/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalPolyhedronDensity
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Data.Fintype.Powerset

/-!
The choice of the rational support data of section 6.1 of the manuscript (step 12).

Let z_j ∈ ℝ^ι be finitely many profiles. For a set J of indices the polytope of J is the set of
convex combinations of the z_j, j ∈ J; it is compact, hence closed. So for a point q there is a
radius ε > 0 such that a point within ε of q lies in the polytope of J only if q does, for every J
at once: a nearby point avoids the finitely many polytopes not containing q.

Let z_j = e_j / A_j with rational e_j and A_j > 0, c a positive real vector and q = Σ_j λ_j z_j a
real convex combination with c · q = 1 and c · e_j ≤ A_j whenever λ_j ≠ 0 (the inequality (24) on
the polytope of the minimizer). Then c · e_j = A_j whenever λ_j ≠ 0, and there are a positive
rational vector c⁰ and rational weights λ⁰ ≥ 0 of sum one, supported in the support of λ, such
that with q⁰ = Σ_j λ⁰_j z_j:

* c⁰ · q⁰ = 1;
* c⁰ · e_j ≤ A_j for every j with c · e_j ≤ A_j;
* m Σ_i c⁰_i < b, if m Σ_i c_i < b: the inequality (25);
* q⁰ lies in the polytope of a set J only if q does.

The vector c⁰ is a rational point of the polyhedron of the equalities and inequalities satisfied
by c, and λ⁰ a rational point of the face of the simplex containing λ, close to λ.
-/

@[expose] public section

namespace MixedFujita

section Polytope

variable {ι τ : Type*} [Fintype τ]

/-- The polytope of the profiles z_j, j ∈ J: their convex combinations. -/
def profilePolytope (z : ι → τ → ℝ) (J : Set τ) : Set (ι → ℝ) :=
  {q | ∃ μ : τ → ℝ, (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧ (∀ j, μ j ≠ 0 → j ∈ J) ∧
    ∀ i, q i = ∑ j, μ j * z i j}

theorem profilePolytope_mono (z : ι → τ → ℝ) {J J' : Set τ} (h : J ⊆ J') :
    profilePolytope z J ⊆ profilePolytope z J' := by
  rintro q ⟨μ, h0, h1, hsupp, hq⟩
  exact ⟨μ, h0, h1, fun j hj => h (hsupp j hj), hq⟩

/-- The polytope of finitely many profiles is closed. -/
theorem isClosed_profilePolytope (z : ι → τ → ℝ) (J : Set τ) :
    IsClosed (profilePolytope z J) := by
  classical
  have hΔcl : IsClosed {μ : τ → ℝ | (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧ ∀ j, μ j ≠ 0 → j ∈ J} := by
    have h1 : IsClosed {μ : τ → ℝ | ∀ j, 0 ≤ μ j} := by
      have : {μ : τ → ℝ | ∀ j, 0 ≤ μ j} = ⋂ j, {μ : τ → ℝ | 0 ≤ μ j} := by
        ext μ
        simp
      rw [this]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {μ : τ → ℝ | ∑ j, μ j = 1} :=
      isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const
    have h3 : IsClosed {μ : τ → ℝ | ∀ j, μ j ≠ 0 → j ∈ J} := by
      have : {μ : τ → ℝ | ∀ j, μ j ≠ 0 → j ∈ J} = ⋂ j ∈ Jᶜ, {μ : τ → ℝ | μ j = 0} := by
        ext μ
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
        exact ⟨fun h j hj => by_contra fun h0 => hj (h j h0), fun h j hj => by_contra fun hJ =>
          hj (h j hJ)⟩
      rw [this]
      exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
    exact h1.inter (h2.inter h3)
  have hΔsub : {μ : τ → ℝ | (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧ ∀ j, μ j ≠ 0 → j ∈ J} ⊆
      Set.Icc (0 : τ → ℝ) 1 := by
    rintro μ ⟨h0, h1, -⟩
    refine ⟨fun j => h0 j, fun j => ?_⟩
    have := Finset.single_le_sum (f := μ) (fun j' _ => h0 j') (Finset.mem_univ j)
    rw [h1] at this
    exact this
  have hΔ := IsCompact.of_isClosed_subset isCompact_Icc hΔcl hΔsub
  have hcont : Continuous fun (μ : τ → ℝ) (i : ι) => ∑ j, μ j * z i j :=
    continuous_pi fun i => continuous_finsetSum _ fun j _ =>
      (continuous_apply j).mul continuous_const
  have himage : profilePolytope z J = (fun (μ : τ → ℝ) (i : ι) => ∑ j, μ j * z i j) ''
      {μ : τ → ℝ | (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧ ∀ j, μ j ≠ 0 → j ∈ J} := by
    ext q
    constructor
    · rintro ⟨μ, h0, h1, hsupp, hq⟩
      exact ⟨μ, ⟨h0, h1, hsupp⟩, (funext hq).symm⟩
    · rintro ⟨μ, ⟨h0, h1, hsupp⟩, rfl⟩
      exact ⟨μ, h0, h1, hsupp, fun _ => rfl⟩
  rw [himage]
  exact (hΔ.image hcont).isClosed

variable [Fintype ι]

/-- A point close to q lies in a polytope of the profiles only if q does: one radius for all the
polytopes. -/
theorem exists_profilePolytope_avoidance_radius (z : ι → τ → ℝ) (q : ι → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (J : Set τ) (q' : ι → ℝ), (∀ i, |q' i - q i| < ε) →
      q' ∈ profilePolytope z J → q ∈ profilePolytope z J := by
  classical
  have hJ : ∀ J : Set τ, ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ι → ℝ, dist q' q < ε →
      q' ∈ profilePolytope z J → q ∈ profilePolytope z J := by
    intro J
    by_cases hq : q ∈ profilePolytope z J
    · exact ⟨1, one_pos, fun _ _ _ => hq⟩
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isClosed_profilePolytope z J).isOpen_compl q hq
      exact ⟨ε, hε, fun q' hq' hmem => absurd hmem (hball hq')⟩
  choose εJ hεJ0 hεJ using hJ
  have hne : (Finset.univ : Finset (Set τ)).Nonempty := ⟨∅, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne εJ, (Finset.lt_inf'_iff hne).mpr fun J _ => hεJ0 J,
    fun J q' hq' hmem => hεJ J q' ?_ hmem⟩
  have hε : 0 < Finset.univ.inf' hne εJ := (Finset.lt_inf'_iff hne).mpr fun J _ => hεJ0 J
  have hdist : dist q' q < Finset.univ.inf' hne εJ :=
    (dist_pi_lt_iff hε).mpr fun i => by
      rw [Real.dist_eq]
      exact hq' i
  exact lt_of_lt_of_le hdist (Finset.inf'_le _ (Finset.mem_univ J))

end Polytope

section Choice

variable {N r : ℕ}

/-- The inequality (24) is an equality on the support of the convex combination: if c · q = 1
for q = Σ_j λ_j e_j / A_j and c · e_j ≤ A_j whenever λ_j ≠ 0, then c · e_j = A_j whenever
λ_j ≠ 0. -/
theorem polytope_condition_eq_on_support (e : Fin N → Fin r → ℝ) (Aj : Fin r → ℝ)
    (hAj : ∀ j, 0 < Aj j) (c : Fin N → ℝ) (lam : Fin r → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam1 : ∑ j, lam j = 1) (hpoly : ∀ j, lam j ≠ 0 → ∑ i, c i * e i j ≤ Aj j)
    (hcq : ∑ i, c i * ∑ j, lam j * (e i j / Aj j) = 1) (j : Fin r) (hj : lam j ≠ 0) :
    ∑ i, c i * e i j = Aj j := by
  have hswap : ∑ i, c i * ∑ j, lam j * (e i j / Aj j) =
      ∑ j, lam j * ((∑ i, c i * e i j) / Aj j) := by
    simp_rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ j, 0 ≤ lam j * (1 - (∑ i, c i * e i j) / Aj j) := by
    intro j
    by_cases hj : lam j = 0
    · rw [hj, zero_mul]
    · exact mul_nonneg (hlam j) (sub_nonneg.mpr ((div_le_one (hAj j)).mpr (hpoly j hj)))
  have hzero : ∑ j, lam j * (1 - (∑ i, c i * e i j) / Aj j) = 0 := by
    have h : ∑ j, lam j * (1 - (∑ i, c i * e i j) / Aj j) =
        ∑ j, lam j - ∑ j, lam j * ((∑ i, c i * e i j) / Aj j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h, hlam1, ← hswap, hcq, sub_self]
  have hj0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hzero j (Finset.mem_univ j)
  have h1 : (∑ i, c i * e i j) / Aj j = 1 := by
    have := (mul_eq_zero.mp hj0).resolve_left hj
    linarith
  exact (div_eq_one_iff_eq (hAj j).ne').mp h1

/-- The rational support data of section 6.1: a positive rational vector c⁰ and rational convex
weights λ⁰ supported in the support of λ, with c⁰ · q⁰ = 1 for q⁰ = Σ_j λ⁰_j e_j / A_j, keeping
every inequality c · e_j ≤ A_j and the budget m Σ c < b, and such that q⁰ lies in a polytope of
the profiles only if q does. -/
theorem exists_rational_support_data (e : Fin N → Fin r → ℚ) (Aj : Fin r → ℚ)
    (hAj : ∀ j, 0 < Aj j) (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) (lam : Fin r → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hlam1 : ∑ j, lam j = 1)
    (hpoly : ∀ j, lam j ≠ 0 → ∑ i, c i * (e i j : ℝ) ≤ Aj j)
    (hcq : ∑ i, c i * ∑ j, lam j * ((e i j : ℝ) / Aj j) = 1) {m b : ℝ} (hm : 0 ≤ m)
    (hb : m * ∑ i, c i < b) :
    ∃ (c₀ : Fin N → ℚ) (lam₀ : Fin r → ℚ), (∀ i, 0 < c₀ i) ∧ (∀ j, 0 ≤ lam₀ j) ∧
      ∑ j, lam₀ j = 1 ∧ (∀ j, lam₀ j ≠ 0 → lam j ≠ 0) ∧
      (∀ j, ∑ i, c i * (e i j : ℝ) ≤ Aj j → ∑ i, (c₀ i : ℝ) * (e i j : ℝ) ≤ Aj j) ∧
      ∑ i, (c₀ i : ℝ) * ∑ j, (lam₀ j : ℝ) * ((e i j : ℝ) / Aj j) = 1 ∧
      m * ∑ i, (c₀ i : ℝ) < b ∧
      ∀ J : Set (Fin r),
        (fun i => ∑ j, (lam₀ j : ℝ) * ((e i j : ℝ) / Aj j)) ∈
            profilePolytope (fun i j => (e i j : ℝ) / (Aj j : ℝ)) J →
          (fun i => ∑ j, lam j * ((e i j : ℝ) / Aj j)) ∈
            profilePolytope (fun i j => (e i j : ℝ) / (Aj j : ℝ)) J := by
  classical
  have hAjR : ∀ j, (0 : ℝ) < (Aj j : ℝ) := fun j => by exact_mod_cast hAj j
  -- the equalities satisfied by c on the support of λ
  have heqc : ∀ j, lam j ≠ 0 → ∑ i, c i * (e i j : ℝ) = Aj j := fun j hj =>
    polytope_condition_eq_on_support (fun i j => (e i j : ℝ)) (fun j => (Aj j : ℝ)) hAjR c lam
      hlam hlam1 hpoly hcq j hj
  -- the rational vector c⁰
  obtain ⟨c₀, hc₀eq, hc₀le, hc₀pos, hc₀b⟩ := exists_pos_rat_near_polyhedron
    (fun (k : {j : Fin r // lam j ≠ 0}) i => e i k.1) (fun k => Aj k.1)
    (fun (k : {j : Fin r // ∑ i, c i * (e i j : ℝ) ≤ Aj j}) i => e i k.1) (fun k => Aj k.1) c
    (fun k => by
      rw [← heqc k.1 k.2]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
    (fun k => by
      refine le_of_eq_of_le ?_ k.2
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _) hc hm hb
  have hc₀eqR : ∀ j, lam j ≠ 0 → ∑ i, (c₀ i : ℝ) * (e i j : ℝ) = Aj j := by
    intro j hj
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hc₀eq ⟨j, hj⟩)
    simp only [Rat.cast_sum, Rat.cast_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc₀leR : ∀ j, ∑ i, c i * (e i j : ℝ) ≤ Aj j → ∑ i, (c₀ i : ℝ) * (e i j : ℝ) ≤ Aj j := by
    intro j hj
    have h : ((∑ i, e i j * c₀ i : ℚ) : ℝ) ≤ ((Aj j : ℚ) : ℝ) := by
      exact_mod_cast hc₀le ⟨j, hj⟩
    simp only [Rat.cast_sum, Rat.cast_mul] at h
    refine le_of_eq_of_le ?_ h
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- the avoidance radius of q
  obtain ⟨ε, hε, havoid⟩ := exists_profilePolytope_avoidance_radius
    (fun (i : Fin N) (j : Fin r) => (e i j : ℝ) / (Aj j : ℝ))
    (fun i => ∑ j, lam j * ((e i j : ℝ) / Aj j))
  -- the rational weights λ⁰ close to λ in the face of the simplex containing λ
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i : Fin N, ∑ j : Fin r, |(e i j : ℝ) / (Aj j : ℝ)| := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hδ : 0 < ε / (1 + S) := div_pos hε (by linarith)
  obtain ⟨lam₀, hlam₀eq, hlam₀le, hlam₀near⟩ := exists_rat_near_polyhedron
    (fun (k : Unit ⊕ {j : Fin r // lam j = 0}) (j' : Fin r) =>
      Sum.elim (fun _ => (1 : ℚ)) (fun k' => if j' = k'.1 then 1 else 0) k)
    (fun k => Sum.elim (fun _ => (1 : ℚ)) (fun _ => 0) k)
    (fun (j : Fin r) (j' : Fin r) => if j' = j then (-1 : ℚ) else 0) (fun _ => 0) lam
    (fun k => by
      rcases k with u | k'
      · simp only [Sum.elim_inl, Rat.cast_one, one_mul]
        exact hlam1
      · simp only [Sum.elim_inr, Rat.cast_zero]
        rw [Finset.sum_eq_single k'.1 (fun j' _ hne => by rw [ite_eq_right hne]; simp)
          (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, Rat.cast_one, one_mul]
        exact k'.2)
    (fun j => by
      rw [Finset.sum_eq_single j (fun j' _ hne => by rw [ite_eq_right hne]; simp)
        (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl]
      simp only [Rat.cast_neg, Rat.cast_one, Rat.cast_zero, neg_mul, one_mul, neg_nonpos]
      exact hlam j) hδ
  have hlam₀sum : ∑ j, lam₀ j = 1 := by
    have h := hlam₀eq (Sum.inl ())
    simpa only [Sum.elim_inl, one_mul] using h
  have hlam₀zero : ∀ j, lam j = 0 → lam₀ j = 0 := by
    intro j hj
    have h := hlam₀eq (Sum.inr ⟨j, hj⟩)
    simp only [Sum.elim_inr] at h
    rw [Finset.sum_eq_single j (fun j' _ hne => by rw [ite_eq_right hne, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl, one_mul] at h
    exact h
  have hlam₀nonneg : ∀ j, 0 ≤ lam₀ j := by
    intro j
    have h := hlam₀le j
    rw [Finset.sum_eq_single j (fun j' _ hne => by rw [ite_eq_right hne, zero_mul])
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left rfl] at h
    linarith
  have hsupp : ∀ j, lam₀ j ≠ 0 → lam j ≠ 0 := fun j hj h0 => hj (hlam₀zero j h0)
  refine ⟨c₀, lam₀, hc₀pos, hlam₀nonneg, hlam₀sum, hsupp, hc₀leR, ?_, hc₀b, fun J hJ => ?_⟩
  · -- c⁰ · q⁰ = 1
    have hswap : ∑ i, (c₀ i : ℝ) * ∑ j, (lam₀ j : ℝ) * ((e i j : ℝ) / Aj j) =
        ∑ j, (lam₀ j : ℝ) * ((∑ i, (c₀ i : ℝ) * (e i j : ℝ)) / Aj j) := by
      simp_rw [Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    have hterm : ∀ j, (lam₀ j : ℝ) * ((∑ i, (c₀ i : ℝ) * (e i j : ℝ)) / Aj j) = (lam₀ j : ℝ) := by
      intro j
      by_cases hj : lam₀ j = 0
      · rw [hj, Rat.cast_zero, zero_mul]
      · rw [hc₀eqR j (hsupp j hj), div_self (hAjR j).ne', mul_one]
    rw [hswap, Finset.sum_congr rfl fun j _ => hterm j]
    exact_mod_cast hlam₀sum
  · -- q⁰ is close to q
    refine havoid J _ (fun i => ?_) hJ
    have hdiff : ∑ j, (lam₀ j : ℝ) * ((e i j : ℝ) / Aj j) - ∑ j, lam j * ((e i j : ℝ) / Aj j) =
        ∑ j, ((lam₀ j : ℝ) - lam j) * ((e i j : ℝ) / Aj j) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hbound : |∑ j, ((lam₀ j : ℝ) - lam j) * ((e i j : ℝ) / Aj j)| ≤
        ε / (1 + S) * S := by
      calc |∑ j, ((lam₀ j : ℝ) - lam j) * ((e i j : ℝ) / Aj j)|
          ≤ ∑ j, |((lam₀ j : ℝ) - lam j) * ((e i j : ℝ) / Aj j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, ε / (1 + S) * |(e i j : ℝ) / (Aj j : ℝ)| := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hlam₀near j).le (abs_nonneg _)
        _ = ε / (1 + S) * ∑ j, |(e i j : ℝ) / (Aj j : ℝ)| := by rw [Finset.mul_sum]
        _ ≤ ε / (1 + S) * S := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            rw [hS]
            exact Finset.single_le_sum
              (f := fun i => ∑ j : Fin r, |(e i j : ℝ) / (Aj j : ℝ)|)
              (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hlt : ε / (1 + S) * S < ε := by
      have h1S : (0 : ℝ) < 1 + S := by linarith
      rw [div_mul_eq_mul_div, div_lt_iff₀ h1S]
      nlinarith
    rw [hdiff]
    exact lt_of_le_of_lt hbound hlt

end Choice

end MixedFujita

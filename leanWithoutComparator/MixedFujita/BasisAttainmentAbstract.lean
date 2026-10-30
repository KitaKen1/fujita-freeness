/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MinimizingSequenceLimit
public import Mathlib.RingTheory.Polynomial.Basic

/-!
The attainment of the minimum over all bases, in abstract form (step 11, section 3.2 of the
manuscript).

* A decreasing sequence of zero sets of ideals of a polynomial ring in finitely many variables
  over a field, each of which meets a set G, has a common point in G: the vanishing ideals
  increase, hence stabilize (Hilbert's basis theorem). No properness is needed for this step.
* A nonnegative vector q is the limit of an increasing sequence of nonnegative rational vectors
  α_l whose nonzero entries are strictly below those of q.
* Attainment. Let the parameters c (coordinates of tuples of sections) range over K^σ, G the set of
  parameters of bases, P(c) a set of profile data (a, v) (log discrepancy and values of the
  weights on the models of c) and R(c, α) the relation "c realizes the normalized profile α".
  Assume: the realization sets of rational profiles are zero sets of ideals; R is decreasing in
  α; a profile datum with v_i > α_i a where α_i ≠ 0 realizes α; if c realizes a sequence α_l → q
  with some q_i > 0, then (1, v) ∈ P(c) for some v ≥ q; P(c) is stable under scaling; and the data
  whose objective Φ(a, v) = Σ_i exp(a/t − v_i/j) is at most a level L have a ∈ [a_*, a^*] and
  0 ≤ v_i ≤ C a. If some datum has objective below L and below N, the infimum of the objective
  over all bases and all their data is attained.

The proof is that of the manuscript, with tuples in place of flags: a minimizing sequence, a
limit (a, q) of the discrepancies and normalized values, rational profiles α_l increasing to q,
the nested closed realization sets, a common basis, and the limit datum on that basis scaled by a.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology Set

section Nested

variable {σ K : Type*} [Finite σ] [Field K]

/-- The common zero set in K^σ of an ideal of polynomials. -/
def polynomialZeroSet (I : Ideal (MvPolynomial σ K)) : Set (σ → K) :=
  {c | ∀ p ∈ I, MvPolynomial.eval c p = 0}

/-- The ideal of the polynomials vanishing on a subset of K^σ. -/
def polynomialVanishingIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ K) where
  carrier := {p | ∀ c ∈ V, MvPolynomial.eval c p = 0}
  add_mem' := fun {p q} hp hq c hc => by rw [map_add, hp c hc, hq c hc, add_zero]
  zero_mem' := fun c _ => map_zero _
  smul_mem' := fun a p hp c hc => by rw [smul_eq_mul, map_mul, hp c hc, mul_zero]

/-- A decreasing sequence of zero sets of ideals, each of which meets G, has a common point in
G. -/
theorem polynomialZeroSet_nested_inter_nonempty (I : ℕ → Ideal (MvPolynomial σ K))
    (G : Set (σ → K)) (hanti : Antitone fun l => polynomialZeroSet (I l))
    (hne : ∀ l, (polynomialZeroSet (I l) ∩ G).Nonempty) :
    ((⋂ l, polynomialZeroSet (I l)) ∩ G).Nonempty := by
  obtain ⟨l₀, hl₀⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherianRing (MvPolynomial σ K))
    ⟨fun l => polynomialVanishingIdeal (polynomialZeroSet (I l)),
      fun a b hab p hp c hc => hp c (hanti hab hc)⟩
  obtain ⟨c, hc, hcG⟩ := hne l₀
  refine ⟨c, mem_iInter.mpr fun l => ?_, hcG⟩
  by_cases hl : l ≤ l₀
  · exact hanti hl hc
  · have h := hl₀ l (le_of_not_ge hl)
    change polynomialVanishingIdeal (polynomialZeroSet (I l₀)) =
      polynomialVanishingIdeal (polynomialZeroSet (I l)) at h
    intro p hp
    have hp' : p ∈ polynomialVanishingIdeal (polynomialZeroSet (I l)) := fun c' hc' => hc' p hp
    rw [← h] at hp'
    exact hp' c hc

end Nested

section Approximation

/-- A nonnegative vector is the limit of an increasing sequence of nonnegative rational vectors
whose nonzero entries are strictly smaller than its entries. -/
theorem exists_monotone_rational_lower_approximation {N : ℕ} (q : Fin N → ℝ)
    (hq : ∀ i, 0 ≤ q i) :
    ∃ α : ℕ → Fin N → ℚ, (∀ l i, 0 ≤ α l i) ∧ (∀ l i, α l i ≤ α (l + 1) i) ∧
      (∀ l i, α l i = 0 ∨ (α l i : ℝ) < q i) ∧
      Tendsto (fun l => fun i => (α l i : ℝ)) atTop (𝓝 q) := by
  have hstep : ∀ (l : ℕ) (i : Fin N), q i - 1 / ((l : ℝ) + 1) < q i - 1 / ((l : ℝ) + 2) := by
    intro l i
    have h1 : (0 : ℝ) < (l : ℝ) + 1 := by positivity
    have h2 : 1 / ((l : ℝ) + 2) < 1 / ((l : ℝ) + 1) :=
      one_div_lt_one_div_of_lt h1 (by linarith)
    linarith
  choose r hr1 hr2 using fun (l : ℕ) (i : Fin N) => exists_rat_btwn (hstep l i)
  have hpos2 : ∀ l : ℕ, (0 : ℝ) < 1 / ((l : ℝ) + 2) := fun l => by positivity
  refine ⟨fun l i => max (r l i) 0, fun l i => le_max_right _ _, fun l i => ?_, fun l i => ?_, ?_⟩
  · apply max_le_max _ le_rfl
    have h1 : (r l i : ℝ) < q i - 1 / ((l : ℝ) + 2) := hr2 l i
    have h2 : q i - 1 / (((l + 1 : ℕ) : ℝ) + 1) < (r (l + 1) i : ℝ) := hr1 (l + 1) i
    have h3 : (((l + 1 : ℕ) : ℝ) + 1) = (l : ℝ) + 2 := by push_cast; ring
    rw [h3] at h2
    have h4 : (r l i : ℝ) < (r (l + 1) i : ℝ) := h1.trans h2
    exact_mod_cast h4.le
  · by_cases h0 : r l i ≤ 0
    · exact Or.inl (max_eq_right h0)
    · right
      change ((max (r l i) 0 : ℚ) : ℝ) < q i
      rw [max_eq_left (not_le.mp h0).le]
      have h1 : (r l i : ℝ) < q i - 1 / ((l : ℝ) + 2) := hr2 l i
      linarith [hpos2 l]
  · rw [tendsto_pi_nhds]
    intro i
    change Tendsto (fun l : ℕ => ((max (r l i) 0 : ℚ) : ℝ)) atTop (𝓝 (q i))
    have hlow : Tendsto (fun l : ℕ => q i - 1 / ((l : ℝ) + 1)) atTop (𝓝 (q i)) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using (tendsto_const_nhds (x := q i)).sub h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun l => ?_)
      (fun l => ?_)
    · change q i - 1 / ((l : ℝ) + 1) ≤ ((max (r l i) 0 : ℚ) : ℝ)
      have h1 : q i - 1 / ((l : ℝ) + 1) < (r l i : ℝ) := hr1 l i
      have h2 : (r l i : ℝ) ≤ ((max (r l i) 0 : ℚ) : ℝ) := by exact_mod_cast le_max_left _ _
      exact (h1.trans_le h2).le
    · change ((max (r l i) 0 : ℚ) : ℝ) ≤ q i
      have h1 : (r l i : ℝ) < q i - 1 / ((l : ℝ) + 2) := hr2 l i
      have h2 : (r l i : ℝ) ≤ q i := by linarith [hpos2 l]
      have h3 : ((max (r l i) 0 : ℚ) : ℝ) = max (r l i : ℝ) 0 := by push_cast; rfl
      rw [h3]
      exact max_le h2 (hq i)

end Approximation

section Attainment

variable {σ K : Type*} [Finite σ] [Field K]

/-- Attainment of the minimum over all bases (abstract form of section 3.2): see the file
header. -/
theorem exists_basis_profile_minimizer {N : ℕ} (hN : 0 < N) {t j : ℝ} (ht : 0 < t)
    (hj : 0 < j) (G : Set (σ → K)) (P : (σ → K) → Set (ℝ × (Fin N → ℝ)))
    (R : (σ → K) → (Fin N → ℝ) → Prop)
    (hclosed : ∀ α : Fin N → ℚ, (∀ i, 0 ≤ α i) →
      ∃ I : Ideal (MvPolynomial σ K), {c | R c (fun i => (α i : ℝ))} = polynomialZeroSet I)
    (hanti : ∀ (c : σ → K) (α α' : Fin N → ℝ), (∀ i, α i ≤ α' i) → R c α' → R c α)
    (hreal : ∀ c ∈ G, ∀ p ∈ P c, 0 < p.1 → ∀ α : Fin N → ℝ, (∀ i, 0 ≤ α i) →
      (∀ i, α i = 0 ∨ α i * p.1 < p.2 i) → R c α)
    (hlimit : ∀ c ∈ G, ∀ (α : ℕ → Fin N → ℝ) (q : Fin N → ℝ), (∀ l i, 0 ≤ α l i) →
      (∀ l, R c (α l)) → Tendsto α atTop (𝓝 q) → (∃ i, 0 < q i) →
      ∃ v : Fin N → ℝ, ((1 : ℝ), v) ∈ P c ∧ ∀ i, q i ≤ v i)
    (hscale : ∀ c ∈ G, ∀ p ∈ P c, ∀ lam : ℝ, 0 ≤ lam →
      (lam * p.1, fun i => lam * p.2 i) ∈ P c)
    {L aLow aHigh Cq : ℝ} (haLow : 0 < aLow)
    (hbd : ∀ c ∈ G, ∀ p ∈ P c, (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ L →
      aLow ≤ p.1 ∧ p.1 ≤ aHigh ∧ ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ Cq * p.1)
    (hint : ∃ c ∈ G, ∃ p ∈ P c, (∑ i, Real.exp (p.1 / t - p.2 i / j)) < L ∧
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N) :
    ∃ c ∈ G, ∃ p ∈ P c, ∀ c' ∈ G, ∀ p' ∈ P c',
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j) := by
  classical
  set Φ : ℝ × (Fin N → ℝ) → ℝ := fun p => ∑ i, Real.exp (p.1 / t - p.2 i / j) with hΦ
  set S : Set ℝ := {y | ∃ c ∈ G, ∃ p ∈ P c, Φ p = y} with hS
  obtain ⟨c₀, hc₀, p₀, hp₀, hp₀L, hp₀N⟩ := hint
  have hSne : S.Nonempty := ⟨Φ p₀, c₀, hc₀, p₀, hp₀, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by
    rintro y ⟨c, hc, p, hp, rfl⟩
    exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le⟩
  have hfle : sInf S ≤ Φ p₀ := csInf_le hSbdd ⟨c₀, hc₀, p₀, hp₀, rfl⟩
  have hfL : sInf S < L := lt_of_le_of_lt hfle hp₀L
  have hfN : sInf S < N := lt_of_le_of_lt hfle hp₀N
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf hSne hSbdd
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hfL))
  -- the data of the minimizing sequence
  have hdata : ∀ k, ∃ c ∈ G, ∃ p ∈ P c, Φ p = u (k + k₀) := fun k => huS (k + k₀)
  choose cs hcs ps hps hΦps using hdata
  have hbdk : ∀ k, aLow ≤ (ps k).1 ∧ (ps k).1 ≤ aHigh ∧
      ∀ i, 0 ≤ (ps k).2 i ∧ (ps k).2 i ≤ Cq * (ps k).1 := fun k =>
    hbd (cs k) (hcs k) (ps k) (hps k) (by
      change Φ (ps k) ≤ L
      rw [hΦps k]
      exact (hk₀ (k + k₀) (Nat.le_add_left _ _)).le)
  have hapos : ∀ k, 0 < (ps k).1 := fun k => haLow.trans_le (hbdk k).1
  -- the normalized values lie in a box
  have hqs : ∀ k i, (ps k).2 i / (ps k).1 ∈ Icc (0 : ℝ) Cq := fun k i =>
    ⟨div_nonneg ((hbdk k).2.2 i).1 (hapos k).le, by
      rw [div_le_iff₀ (hapos k)]
      exact ((hbdk k).2.2 i).2⟩
  have hbox : IsCompact (Icc aLow aHigh ×ˢ Set.pi univ (fun _ : Fin N => Icc (0 : ℝ) Cq)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨⟨a₀, q⟩, hmem, φ, hφ, hlim⟩ := hbox.tendsto_subseq
    (x := fun k => ((ps k).1, fun i => (ps k).2 i / (ps k).1))
    (fun k => ⟨⟨(hbdk k).1, (hbdk k).2.1⟩, fun i _ => hqs k i⟩)
  have ha₀pos : 0 < a₀ := haLow.trans_le hmem.1.1
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hmem.2 i (mem_univ i)).1
  have hlim_q : Tendsto (fun k => fun i => (ps (φ k)).2 i / (ps (φ k)).1) atTop (𝓝 q) :=
    (continuous_snd.tendsto _).comp hlim
  -- the objective at the limit is the infimum
  set Ψ : ℝ × (Fin N → ℝ) → ℝ := fun p => ∑ i, Real.exp (p.1 / t - p.1 * p.2 i / j) with hΨ
  have hΨcont : Continuous Ψ := by
    rw [hΨ]
    fun_prop
  have hΨk : ∀ k, Ψ ((ps k).1, fun i => (ps k).2 i / (ps k).1) = u (k + k₀) := by
    intro k
    rw [← hΦps k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (ps k).1 ≠ 0 := (hapos k).ne'
    have h : (ps k).1 * ((ps k).2 i / (ps k).1) = (ps k).2 i := by field_simp
    change Real.exp ((ps k).1 / t - (ps k).1 * ((ps k).2 i / (ps k).1) / j) = _
    rw [h]
  have hΨlim : Ψ (a₀, q) = sInf S := by
    have h1 : Tendsto (fun k => Ψ ((ps (φ k)).1, fun i => (ps (φ k)).2 i / (ps (φ k)).1)) atTop
        (𝓝 (Ψ (a₀, q))) := (hΨcont.tendsto (a₀, q)).comp hlim
    have h2 : Tendsto (fun k => u (φ k + k₀)) atTop (𝓝 (sInf S)) :=
      hu.comp ((tendsto_add_atTop_nat k₀).comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique (h1.congr fun k => hΨk (φ k)) h2
  -- some limit value is positive
  have hqpos : ∃ i, 0 < q i := by
    by_contra hno
    push Not at hno
    have hq0' : ∀ i, q i = 0 := fun i => le_antisymm (hno i) (hq0 i)
    have hval : Ψ (a₀, q) = N * Real.exp (a₀ / t) := by
      change (∑ i, Real.exp (a₀ / t - a₀ * q i / j)) = _
      simp only [hq0', mul_zero, zero_div, sub_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hexp : 1 < Real.exp (a₀ / t) := Real.one_lt_exp_iff.mpr (div_pos ha₀pos ht)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [hΨlim] at hval
    nlinarith
  -- rational profiles increasing to q and their realization sets
  obtain ⟨α, hα0, hαmono, hαlt, hαlim⟩ := exists_monotone_rational_lower_approximation q hq0
  choose I hI using fun l => hclosed (α l) (hα0 l)
  have hanti' : Antitone fun l => polynomialZeroSet (I l) := by
    refine antitone_nat_of_succ_le fun l => ?_
    rw [← hI l, ← hI (l + 1)]
    intro c hc
    exact hanti c _ _ (fun i => by exact_mod_cast hαmono l i) hc
  have hne : ∀ l, (polynomialZeroSet (I l) ∩ G).Nonempty := by
    intro l
    have hev : ∀ᶠ k in atTop, ∀ i, (α l i : ℝ) = 0 ∨
        (α l i : ℝ) < (ps (φ k)).2 i / (ps (φ k)).1 := by
      rw [eventually_all]
      intro i
      rcases hαlt l i with h0 | hlt
      · exact Eventually.of_forall fun k => Or.inl (by exact_mod_cast h0)
      · exact ((tendsto_pi_nhds.mp hlim_q i).eventually (lt_mem_nhds hlt)).mono
          fun k hk => Or.inr hk
    obtain ⟨k, hk⟩ := hev.exists
    refine ⟨cs (φ k), ?_, hcs (φ k)⟩
    rw [← hI l]
    refine hreal (cs (φ k)) (hcs (φ k)) (ps (φ k)) (hps (φ k)) (hapos (φ k)) _
      (fun i => by exact_mod_cast hα0 l i) fun i => ?_
    rcases hk i with h0 | hlt
    · exact Or.inl h0
    · exact Or.inr ((lt_div_iff₀ (hapos (φ k))).mp hlt)
  obtain ⟨cstar, hcI, hcG⟩ := polynomialZeroSet_nested_inter_nonempty I G hanti' hne
  have hRstar : ∀ l, R cstar (fun i => (α l i : ℝ)) := fun l => by
    have h := mem_iInter.mp hcI l
    rw [← hI l] at h
    exact h
  obtain ⟨v, hv, hvq⟩ := hlimit cstar hcG (fun l i => (α l i : ℝ)) q
    (fun l i => by exact_mod_cast hα0 l i) hRstar hαlim hqpos
  have hsc := hscale cstar hcG (1, v) hv a₀ ha₀pos.le
  refine ⟨cstar, hcG, (a₀ * 1, fun i => a₀ * v i), hsc, fun c' hc' p' hp' => ?_⟩
  have h1 : (∑ i, Real.exp ((a₀ * 1) / t - a₀ * v i / j)) ≤ Ψ (a₀, q) := by
    refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
    have h : a₀ * q i / j ≤ a₀ * v i / j :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hvq i) ha₀pos.le) hj.le
    rw [mul_one]
    linarith
  have h2 : sInf S ≤ Φ p' := csInf_le hSbdd ⟨c', hc', p', hp', rfl⟩
  rw [hΨlim] at h1
  exact h1.trans h2

end Attainment

end MixedFujita

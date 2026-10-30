/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityCaseCubeHit
public import MixedFujita.RationalSliceCertificates
public import MixedFujita.CartierExponentProducts
public import MixedFujita.MonomialChartMargin

/-!
The sections of Lemma 5 in the equality case (§8): from the equality branch of the dichotomy,
actual sections of h τ A with vanishing order n h at x whose initial exponents satisfy the strict
chart inequalities of (34).

In the equality branch the normalized counts of the initial exponent sets tend to (n + 1)^n/n!;
the means of |γ|/j are at least n - o(1) (the lattice bound) and frequently at most n + ε for
every ε > 0. So along a subsequence of degrees the counts and the means converge, the means to n.
The rational slice witnesses (`equality_mean_eventually_rational_slice_witnesses`) then give n + 1
initial exponents of one degree j around the point (b/a)·1, with τ = a/b ∈ (n/(n+1), 1), and
rational convex combinations hitting the slice targets (b/a)·1 + δ (e_k - e_v). The τ-normalized
products of actual sections with these initial exponents (`cartierExponentTauProduct_slice_data`)
are nonzero sections of h τ A, h = r j D b, with vanishing order n h at x. Their initial exponents
satisfy, in every chart k of the exceptional divisor, min_v ⟨w, β_(k,v)⟩ ≤ h (1 - a δ/(b n)) Σ w
for weights w ≥ 0 with w_k = 0 (`equality_scaled_exponent_chart_margin`): the input of the
monomial case of (34). The threshold on the exceptional divisor through Lemma 3, the vanishing and
the descent are not done here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

/-- The normalized lattice mean at an integer scale is the mean of |γ|/j. -/
theorem normalizedLatticeMean_natCast {n : ℕ} (E : Finset (Fin n → ℕ)) (j : ℕ) :
    normalizedLatticeMean E (j : ℝ) = (∑ γ ∈ E, ((∑ i, γ i : ℕ) : ℝ) / j) / E.card := by
  unfold normalizedLatticeMean latticeDegreeSum
  rw [← Finset.sum_div, div_div]
  push_cast
  rfl

/-- The equality branch of the dichotomy gives a subsequence of degrees along which the normalized
counts tend to (n + 1)^n/n! and the normalized means tend to n. -/
theorem equality_case_exists_mean_subsequence (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ))
    {c : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    (hvol : (n.factorial : ℝ) * c = ((n + 1 : ℕ) : ℝ) ^ n)
    (hmean : ∀ ε > 0, ∃ᶠ j : ℕ in atTop,
      (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card ≤ n + ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => normalizedLatticeCard (E (φ k)) (φ k)) atTop
        (𝓝 (((n : ℝ) + 1) ^ n / (n.factorial : ℝ))) ∧
      Tendsto (fun k => normalizedLatticeMean (E (φ k)) (φ k)) atTop
        (𝓝 ((n : ℝ) / (n + 1 : ℝ) * ((n : ℝ) + 1))) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hroot : (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ = n := by
    rw [hvol, Real.pow_rpow_inv_natCast (by positivity) hn.ne']
    push_cast
    field_simp
  have hlow : ∀ ε > 0, ∀ᶠ j : ℕ in atTop,
      (n : ℝ) - ε ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card := by
    intro ε hε
    have hσ : (n : ℝ) - ε < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ := by
      rw [hroot]
      linarith
    exact (eventually_average_degree_ge n hn E hc hN hσ).mono fun j h => h.2
  have hP : ∀ k : ℕ, ∃ᶠ j : ℕ in atTop,
      (n : ℝ) - 1 / ((k : ℝ) + 1) ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card ∧
        (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card ≤ n + 1 / ((k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    exact ((hmean _ hk).and_eventually (hlow _ hk)).mono fun j h => ⟨h.2, h.1⟩
  obtain ⟨φ, hφ, hφP⟩ := Filter.extraction_forall_of_frequently hP
  refine ⟨φ, hφ, ?_, ?_⟩
  · have h := hN.comp hφ.tendsto_atTop
    have hval : c = ((n : ℝ) + 1) ^ n / (n.factorial : ℝ) := by
      rw [eq_div_iff hf.ne', mul_comm, hvol]
      push_cast
      ring
    rw [← hval]
    exact h
  · have hval : (n : ℝ) / (n + 1 : ℝ) * ((n : ℝ) + 1) = n := by
      field_simp
    rw [hval]
    have h1 : Tendsto (fun k : ℕ => (n : ℝ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 n) := by
      simpa using (tendsto_const_nhds (x := (n : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun k : ℕ => (n : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 n) := by
      simpa using (tendsto_const_nhds (x := (n : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 (fun k => ?_) (fun k => ?_)
    · change _ ≤ normalizedLatticeMean (E (φ k)) ((φ k : ℕ) : ℝ)
      rw [normalizedLatticeMean_natCast]
      exact (hφP k).1
    · change normalizedLatticeMean (E (φ k)) ((φ k : ℕ) : ℝ) ≤ _
      rw [normalizedLatticeMean_natCast]
      exact (hφP k).2

section Sections

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

variable (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
  [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]

/-- The degree-lexicographic initial exponents of the sections of j A at x, as points of ℕ^n. -/
noncomputable def cartierInitialExponentPoints {n : ℕ}
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) : Finset (Fin n → ℕ) :=
  (cartierGradedInitialExponents A x f hf (MonomialOrder.degLex (σ := Fin n)) coordinates j).image
    (fun p : Fin n →₀ ℕ => ⇑p)

/-- The number of initial exponents is the dimension of the sections. -/
theorem cartierInitialExponentPoints_card {n : ℕ} [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) :
    (cartierInitialExponentPoints A x f hf coordinates j).card =
      Module.finrank K Γ((j • A).sheaf, ⊤) := by
  rw [cartierInitialExponentPoints,
    Finset.card_image_of_injective _ (DFunLike.coe_injective (F := Fin n →₀ ℕ)),
    cartierGradedInitialExponents_card]

/-- Lemma 5 in the equality case, the sections: if h⁰(j A)/j^n tends to c with n! c = (n + 1)^n
and the means of |γ|/j over the initial exponents are frequently at most n + ε for every ε > 0,
then for τ = a/b with n b < (n + 1) a and every r ≥ 1 there are actual nonzero sections s_(k,v) of
h τ A, h = r j D b, with vanishing order n h at x, initial exponents (r a) β_(k,v), and in every
chart k the strict inequality min_v ⟨w, (r a) β_(k,v)⟩ ≤ h (1 - a δ/(b n)) Σ w for w ≥ 0 with
w_k = 0. -/
theorem cartier_equality_case_slice_sections {n : ℕ} (hn : 0 < n)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    {c : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun j : ℕ => (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
      atTop (𝓝 c))
    (hvol : (n.factorial : ℝ) * c = ((n + 1 : ℕ) : ℝ) ^ n)
    (hmean : ∀ ε > 0, ∃ᶠ j : ℕ in atTop,
      (∑ γ ∈ cartierInitialExponentPoints A x f hf coordinates j, ((∑ i, γ i : ℕ) : ℝ) / j) /
        (cartierInitialExponentPoints A x f hf coordinates j).card ≤ n + ε)
    {r a b : ℕ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) (hab : n * b < (n + 1) * a) :
    ∃ (j D : ℕ) (δ : ℚ), 0 < j ∧ 0 < D ∧ 0 < δ ∧
      ∃ (β : Fin n × Fin n → Fin n →₀ ℕ)
        (s : Fin n × Fin n → Γ((equalitySectionDegree r j D a • A).sheaf, ⊤)),
        (∀ l, s l ≠ 0) ∧
        (∀ l, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n))
          (cartierTaylorCoordinates _ x (f ^ equalitySectionDegree r j D a)
            (cartierLocalEquation_pow A x f hf _) coordinates (s l)) ((r * a) • β l)) ∧
        (∀ l, cartierSectionVanishingOrder _ x (s l) = (n * equalityHeight r j D b : ℕ)) ∧
        ∀ (w : Fin n → ℝ) (k : Fin n), w k = 0 → ∃ i : Fin n,
          (∑ q, w q * (((r * a) • β (k, i)) q : ℝ)) ≤
            (equalityHeight r j D b : ℝ) * (1 - (((a : ℚ) / b * δ : ℚ) : ℝ) / n) *
              (∑ q, w q) := by
  classical
  -- the exponent sets and their counts
  have hcard : ∀ j, ((cartierInitialExponentPoints A x f hf coordinates j).card : ℝ) =
      Module.finrank K Γ((j • A).sheaf, ⊤) := fun j => by
    exact_mod_cast cartierInitialExponentPoints_card A x f hf coordinates j
  have hNE : Tendsto (fun j : ℕ =>
      ((cartierInitialExponentPoints A x f hf coordinates j).card : ℝ) / (j : ℝ) ^ n) atTop
      (𝓝 c) := by
    simpa only [hcard] using hN
  obtain ⟨φ, hφ, hcardφ, hmeanφ⟩ := equality_case_exists_mean_subsequence n hn
    (fun j => cartierInitialExponentPoints A x f hf coordinates j) hc hNE hvol hmean
  -- the centre (b/a)·1 of the slice
  have hc₀ : (fun _ : Fin n => (((b : ℚ) / a : ℚ) : ℝ)) ∈
      positiveSimplexInterior ((n : ℝ) + 1) := by
    refine ⟨fun i => by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hab' : (n : ℝ) * b < ((n : ℝ) + 1) * a := by exact_mod_cast hab
    push_cast
    rw [mul_div_assoc', div_lt_iff₀ ha']
    exact hab'
  have hev := equality_mean_eventually_rational_slice_witnesses
    (fun k => cartierInitialExponentPoints A x f hf coordinates (φ k)) φ
    (fun _ => (b : ℚ) / a) hφ.tendsto_atTop (by positivity) hc₀ hcardφ hmeanφ
  obtain ⟨k, hk, hk1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  obtain ⟨g, hg, δ, hδ, q, hq1, -, hqeq⟩ := hk
  have hj : 0 < φ k := lt_of_lt_of_le hk1 (hφ.id_le k)
  -- the initial exponents as finitely supported functions
  have hpre : ∀ t, ∃ p ∈ cartierGradedInitialExponents A x f hf
      (MonomialOrder.degLex (σ := Fin n)) coordinates (φ k), ⇑p = g t :=
    fun t => Finset.mem_image.mp (hg t)
  choose p hp hpg using hpre
  set Q : Fin n × Fin n → Fin (n + 1) → ℚ≥0 := fun l => q l.1 l.2 with hQ
  set D := sharedRationalDenominator (Finset.univ : Finset (Fin (n + 1))) Q with hD
  have hDpos : 0 < D := sharedRationalDenominator_pos _ _
  have hQ1 : ∀ l, (∑ t ∈ (Finset.univ : Finset (Fin (n + 1))), Q l t) = 1 :=
    fun l => hq1 l.1 l.2
  set β : Fin n × Fin n → Fin n →₀ ℕ := fun l =>
    ∑ t ∈ (Finset.univ : Finset (Fin (n + 1))), sharedRationalMultiplicity Finset.univ Q l t • p t
    with hβ
  -- the slice equations
  have hslice : ∀ l i, (β l i : ℚ) / ((D : ℚ) * (φ k : ℕ)) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ l.1 l.2 i := by
    intro l i
    have h1 := sharedRational_exponent_coordinate_rat Finset.univ Q p l i
    have h2 := congrFun (hqeq l.1 l.2) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    rw [← h2, hβ, h1]
    have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
    have hj0 : ((φ k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
    rw [mul_div_mul_left _ _ hD0, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hgt : (g t i : ℚ) = (p t i : ℚ) := by
      rw [← hpg t]
    rw [hgt, mul_div_assoc]
  refine ⟨φ k, D, δ, hj, hDpos, hδ, β, fun l => cartierExponentTauProduct A x f hf
    (MonomialOrder.degLex (σ := Fin n)) coordinates (φ k) Finset.univ p (fun t _ => hp t) Q r a l
    (hQ1 l), fun l => ?_, fun l => ?_, fun l => ?_, ?_⟩
  · exact cartierExponentTauProduct_ne_zero A x f hf _ coordinates (φ k) Finset.univ p
      (fun t _ => hp t) Q r a l (hQ1 l)
  · exact cartierExponentTauProduct_initialMonomial A x f hf _ coordinates (φ k) Finset.univ p
      (fun t _ => hp t) Q r a l (hQ1 l)
  · obtain ⟨-, -, hord, -⟩ := cartierExponentTauProduct_slice_data A x f hf coordinates
      (j := φ k) (r := r) (a := a) (b := b) Finset.univ p (fun t _ => hp t) Q l (hQ1 l) (β l)
      rfl l.1 l.2 hr hj ha hb (hslice l)
    exact hord
  · intro w k' hk'
    exact equality_scaled_exponent_chart_margin hn β hr hj hDpos ha hb hδ.le
      (fun k i q => hslice (k, i) q) w k' hk'

end Sections

end MixedFujita

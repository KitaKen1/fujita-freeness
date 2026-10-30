/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityCaseSections
public import MixedFujita.ProjectiveMultipleHilbert
public import MixedFujita.RealizationSetsPrincipalShift

/-!
The combinatorial half of Lemma 5 at a point (§8): if the bound (33) fails at x, the sections of
the equality case exist.

* Hilbert asymptotics for all multiples of A when k A is the hyperplane class up to a principal
  divisor: the sections of (k q) A and of q J have the same dimension, so the residue sandwich of
  `projectiveHyperplane_hilbert_of_multiple` applies unchanged.
* The degree-lexicographic initial basis of the sections of j A at x has as sum of vanishing orders
  the sum of the total degrees of the initial exponents: its vectors have the initial exponents as
  initial monomials, and for this order the initial monomial has the least total degree.
* So (33) in the coordinate-free form (some σ > n and, for all large j, a basis with
  Σ ord_x ≥ σ j N_j) follows from the bound on the averages of the initial exponents. If it fails
  and h⁰(j A)/j^n tends to c with n! c ≥ (n + 1)^n, the dichotomy leaves the equality branch, and
  `cartier_equality_case_slice_sections` gives the sections of h τ A with vanishing order n h and
  the chart inequalities of (34).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MixedFujita

universe u

section Hilbert

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Hilbert asymptotics for all multiples of A when k A is the hyperplane class up to a principal
divisor and m A has a nonzero section for every m ≥ e₀. -/
theorem projectiveHyperplane_hilbert_of_multiple_add_principal
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (A : CartierDivisor Y) {k : ℕ}
    (hk : 0 < k) (φ : Y.functionFieldˣ)
    (hkA : k • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (e₀ : ℕ) (hsec : ∀ m, e₀ ≤ m → ∃ σ : Γ((m • A).sheaf, ⊤), σ ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ _ : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K Γ((D • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d) atTop
        (𝓝 ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) := by
  obtain ⟨r, hr, hfinJ, hlimJ⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  set J := projectiveHyperplaneCartier e g hg hggen with hJ
  have hmul : ∀ q : ℕ, (k * q) • A = q • J + principalCartierDivisor Y (φ ^ q) := by
    intro q
    rw [mul_comm, ← smul_smul, hkA, smul_add, principalCartierDivisor_power]
  have hfinMul : ∀ q : ℕ, FiniteDimensional K Γ(((k * q) • A).sheaf, ⊤) := by
    intro q
    rw [hmul q]
    have := hfinJ q
    exact (cartierPrincipalShiftEquiv (K := K) (q • J) (φ ^ q)).symm.finiteDimensional
  -- every multiple is finite dimensional
  have hfin : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤) := by
    intro D
    set m := k * (D + e₀ + 1) - D with hm
    have hmD : m + D = k * (D + e₀ + 1) := by
      have : D + e₀ + 1 ≤ k * (D + e₀ + 1) := Nat.le_mul_of_pos_left _ hk
      omega
    have hme : e₀ ≤ m := by
      have : D + e₀ + 1 ≤ k * (D + e₀ + 1) := Nat.le_mul_of_pos_left _ hk
      omega
    obtain ⟨σ, hσ⟩ := hsec m hme
    have hcod : FiniteDimensional K Γ(((m + D) • A).sheaf, ⊤) := by
      rw [hmD]
      exact hfinMul _
    exact Module.Finite.of_injective (cartierNsmulProductLinear (K := K) A m D σ)
      (cartierNsmulProduct_injective A m D σ hσ)
  refine ⟨r, hr, hfin, ?_⟩
  set h : ℕ → ℝ := fun D => (Module.finrank K Γ((D • A).sheaf, ⊤) : ℝ) with hh
  have hmono : ∀ j m, e₀ ≤ m → h j ≤ h (j + m) := by
    intro j m hm
    obtain ⟨σ, hσ⟩ := hsec m hm
    have hle := LinearMap.finrank_le_finrank_of_injective
      (f := cartierNsmulProductLinear (K := K) A m j σ)
      (cartierNsmulProduct_injective A m j σ hσ)
    simp only [hh]
    rw [add_comm j m]
    exact_mod_cast hle
  have hlim : Tendsto (fun q : ℕ => h (k * q) / ((k * q : ℕ) : ℝ) ^ d) atTop
      (𝓝 ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hfun : ∀ q : ℕ, h (k * q) / ((k * q : ℕ) : ℝ) ^ d =
        (Module.finrank K Γ((q • J).sheaf, ⊤) : ℝ) / (q : ℝ) ^ d / (k : ℝ) ^ d := by
      intro q
      simp only [hh]
      rw [finrank_eq_of_eq_add_principal (K := K) (hmul q)]
      push_cast
      rw [mul_pow, div_div, mul_comm ((k : ℝ) ^ d)]
    simp only [hfun]
    exact hlimJ.div_const _
  exact tendsto_of_residue_sandwich hk e₀ hmono hlim

end Hilbert

section AtPoint

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

variable (A : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
  [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]

/-- The degree-lexicographic initial basis has as sum of vanishing orders at x the sum of the
total degrees of the initial exponents. -/
theorem exists_basis_vanishingOrder_sum_eq_initialExponents {n : ℕ}
    [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (j : ℕ) :
    ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
      ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ) =
        ∑ γ ∈ cartierInitialExponentPoints A x f hf coordinates j, ((∑ i, γ i : ℕ) : ℝ) := by
  classical
  set m := MonomialOrder.degLex (σ := Fin n) with hmdef
  set B₀ := cartierGradedInitialBasis A x f hf m coordinates j with hB₀
  let : Fintype (initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates j)) :=
    (initialIndexSet_finite _).fintype
  set F : initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates j) →
    (Fin n →₀ ℕ) := fun p => m.toSyn.symm p.val with hF
  have hFinj : Function.Injective F := fun p p' h =>
    Subtype.ext (m.toSyn.symm.injective h)
  have hspec : ∀ p, IsInitialMonomial m (cartierGradedTaylor A x f hf coordinates j (B₀ p))
      (F p) := fun p => cartierGradedInitialBasis_spec A x f hf m coordinates j p
  -- the vanishing orders of the basis vectors
  have hord : ∀ p, ((cartierSectionVanishingOrder (j • A) x (B₀ p)).toNat : ℝ) =
      ((F p).degree : ℝ) := by
    intro p
    have h1 := degreeLex_initial_order (hspec p)
    rw [cartierGradedTaylor_fin_eq,
      cartierTaylorCoordinates_order_eq_vanishingOrder] at h1
    rw [h1, ENat.toNat_natCast]
  -- the images of the indices are all the initial exponents
  have hsub : Finset.univ.image F ⊆
      cartierGradedInitialExponents A x f hf m coordinates j := by
    intro q hq
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hq
    exact (cartierGradedInitialExponents_mem A x f hf m coordinates j (F p)).mpr ⟨B₀ p, hspec p⟩
  have hcardι : Fintype.card (initialIndexSet (cartierGradedCoefficientMap A x f hf m coordinates
      j)) = Module.finrank K Γ((j • A).sheaf, ⊤) :=
    (Module.finrank_eq_card_basis B₀).symm
  have himage : Finset.univ.image F = cartierGradedInitialExponents A x f hf m coordinates j := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, hcardι,
      cartierGradedInitialExponents_card]
  -- reindex the basis by Fin N
  set eι := Fintype.equivFinOfCardEq hcardι with heι
  refine ⟨B₀.reindex eι, ?_⟩
  simp only [Module.Basis.reindex_apply]
  rw [Equiv.sum_comp eι.symm (fun p => ((cartierSectionVanishingOrder (j • A) x (B₀ p)).toNat :
    ℝ))]
  simp only [hord]
  rw [← Finset.sum_image (fun p _ p' _ h => hFinj h) (f := fun q : Fin n →₀ ℕ => (q.degree : ℝ)),
    himage, cartierInitialExponentPoints,
    Finset.sum_image (fun q _ q' _ h => DFunLike.coe_injective (F := Fin n →₀ ℕ) h)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finsupp.degree_eq_sum]

/-- The combinatorial half of Lemma 5 at x: if h⁰(j A)/j^n tends to c with n! c ≥ (n + 1)^n and
the bound (33) fails at x (no σ > n with, for all large j, a basis of the sections of j A with
Σ ord_x ≥ σ j N_j), then the sections of the equality case exist: for τ = a/b with
n b < (n + 1) a and every r ≥ 1, nonzero sections of h τ A, h = r j D b, of vanishing order n h at
x, whose initial exponents satisfy the strict chart inequalities of (34). -/
theorem cartier_equality_case_sections_of_not_orderAverage {n : ℕ} (hn : 0 < n)
    [IsNoetherianRing (X.presheaf.stalk x)]
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    {c : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun j : ℕ => (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n)
      atTop (𝓝 c))
    (hvol : ((n + 1 : ℕ) : ℝ) ^ n ≤ (n.factorial : ℝ) * c)
    (hnot : ¬ ∃ σ : ℝ, (n : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ))
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
  have hcard : ∀ j, ((cartierInitialExponentPoints A x f hf coordinates j).card : ℝ) =
      Module.finrank K Γ((j • A).sheaf, ⊤) := fun j => by
    exact_mod_cast cartierInitialExponentPoints_card A x f hf coordinates j
  have hNE : Tendsto (fun j : ℕ =>
      ((cartierInitialExponentPoints A x f hf coordinates j).card : ℝ) / (j : ℝ) ^ n) atTop
      (𝓝 c) := by
    simpa only [hcard] using hN
  rcases equality_case_dichotomy n hn (fun j => cartierInitialExponentPoints A x f hf coordinates j)
    hc hNE hvol with ⟨σ, hσ, hev⟩ | ⟨hvol', hmean⟩
  · -- the bound on the averages gives (33) through the initial basis
    exfalso
    apply hnot
    refine ⟨σ, hσ, ?_⟩
    filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
    obtain ⟨B, hB⟩ := exists_basis_vanishingOrder_sum_eq_initialExponents A x f hf coordinates j
    refine ⟨B, ?_⟩
    rw [hB]
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    by_cases hN0 : (cartierInitialExponentPoints A x f hf coordinates j).card = 0
    · have h0 : (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) = 0 := by
        rw [← hcard, hN0, Nat.cast_zero]
      rw [h0, mul_zero]
      exact Finset.sum_nonneg fun γ _ => Nat.cast_nonneg _
    · have hNpos : (0 : ℝ) < (cartierInitialExponentPoints A x f hf coordinates j).card := by
        exact_mod_cast Nat.pos_of_ne_zero hN0
      rw [← hcard]
      rw [le_div_iff₀ hNpos, ← Finset.sum_div, le_div_iff₀ hj0] at hj
      linarith
  · exact cartier_equality_case_slice_sections A x f hf hn coordinates hc hN hvol' hmean hr ha hb
      hab

end AtPoint

end MixedFujita

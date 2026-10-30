/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveThresholdDiagonal
public import MixedFujita.AmpleSumEqualityCase

/-!
The threshold condition (34) for the leading forms of the equality case, from the degeneration
form of Lemma 3, and the resulting split of the geometric half of Lemma 5 (§8).

Let f_ℓ be forms whose lexicographic initial exponents β_ℓ satisfy the natural chart inequalities.
One positive integer weight w makes each β_ℓ the unique w-minimal exponent of f_ℓ
(`exists_common_polynomial_initial_weights`), and the weighted family degenerates f_ℓ to its
initial monomial at t = 0 (`weightedPolynomialFamily_at_zero`). The special fibre satisfies (34)
(`projectiveThresholdCondition_monomial`). Lemma 3 in the form `ThresholdDegenerationStatement`
(openness of the locus where the threshold exceeds 1/h, and properness of the exceptional divisor,
over an algebraically closed field of characteristic zero) gives a nonzero fibre satisfying (34).
That fibre is, up to nonzero constants, the diagonal transform of the forms
(`weightedPolynomialFamily_scaled_parameter`), so the forms themselves satisfy (34)
(`projectiveThresholdCondition_of_polynomialDiagonalHom`).

For the sections of the equality case of Lemma 5, the leading forms of their Taylor series have
the degree-lexicographic initial exponents as lexicographic initial exponents
(`homogeneousTaylorForm_lexInitial`), and these satisfy the chart inequalities with a positive
margin; so with Lemma 3 in this form the leading forms satisfy (34)
(`leadingForms_projectiveThresholdCondition`).

The rest of the geometric half (the blow-up of the point, the positivity (35), Kawamata–Viehweg
vanishing, adjunction and descent) is stated as `ThresholdLiftingStatement`: sections of e A with
e < h, vanishing order n h at x and leading forms satisfying (34) force K_X + A + N to be generated
at x. It uses only (34), the vanishing order and τ = e/h < 1, not the initial exponents. The
statement `EqualityCaseLiftingStatement` follows from the two
(`equalityCaseLifting_of_thresholdLifting`), and so does F1 together with the sum form of the
Kawamata–Viehweg statement and the closedness of the realization sets.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

section Forms

open MvPowerSeries

/-- Lemma 3 in the form used for (34) (§8): in the degeneration of finitely many forms by an
integer weight for which given exponents are the unique minima of their supports, if the special
fibre (the initial monomials) satisfies the threshold condition (34) on the exceptional divisor,
so does some nonzero fibre. Over an algebraically closed field of characteristic zero it follows
from the openness of the locus where the threshold exceeds 1/h (Lemma 3) and the properness of the
exceptional divisor. -/
def ThresholdDegenerationStatement (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    [DecidableEq K] : Prop :=
  ∀ (n : ℕ) {ι : Type} [Fintype ι] (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (h : ℕ),
    (∀ ℓ, ∃ D, (f ℓ).IsHomogeneous D) → (∀ ℓ, p ℓ ∈ (f ℓ).support) →
    (∀ ℓ, ∀ q ∈ (f ℓ).support, q ≠ p ℓ →
      polynomialExponentWeight w (p ℓ) < polynomialExponentWeight w q) →
    ProjectiveThresholdCondition (fun ℓ => (weightedPolynomialFamily w (p ℓ) (f ℓ)).eval 0) h →
    ∃ t : K, t ≠ 0 ∧ ProjectiveThresholdCondition
      (fun ℓ => (weightedPolynomialFamily w (p ℓ) (f ℓ)).eval (MvPolynomial.C t)) h

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K] {n : ℕ}

/-- The threshold condition (34) for forms whose lexicographic initial exponents satisfy the
natural chart inequalities, from the degeneration form of Lemma 3. -/
theorem projectiveThresholdCondition_of_lexInitial (hdeg : ThresholdDegenerationStatement K)
    {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → MvPolynomial (Fin n) K)
    (hf : ∀ ℓ, ∃ D, (f ℓ).IsHomogeneous D) (β : ι → Fin n →₀ ℕ)
    (hβ : ∀ ℓ, IsPolynomialLexInitial (f ℓ) (β ℓ)) (h : ℕ) (hh : 1 ≤ h)
    (hmon : ∀ (k : Fin n) (u : {i : Fin n // i ≠ k} → ℕ), u ≠ 0 →
      ∃ ℓ, ∑ i, u i * β ℓ i < h * ∑ i, u i) :
    ProjectiveThresholdCondition f h := by
  classical
  obtain ⟨w, -, hw⟩ := exists_common_polynomial_initial_weights Finset.univ f β
    (fun ℓ _ => hβ ℓ)
  have hw' : ∀ ℓ, ∀ q ∈ (f ℓ).support, q ≠ β ℓ →
      polynomialExponentWeight w (β ℓ) < polynomialExponentWeight w q :=
    fun ℓ => hw ℓ (Finset.mem_univ ℓ)
  have hcoeff : ∀ ℓ, (f ℓ).coeff (β ℓ) ≠ 0 := fun ℓ => MvPolynomial.mem_support_iff.mp (hβ ℓ).1
  -- the special fibre consists of the initial monomials
  have hzero : ∀ ℓ, (weightedPolynomialFamily w (β ℓ) (f ℓ)).eval 0 =
      MvPolynomial.monomial (β ℓ) ((f ℓ).coeff (β ℓ)) :=
    fun ℓ => weightedPolynomialFamily_at_zero w (β ℓ) (f ℓ) (hβ ℓ).1 (hw' ℓ)
  have hspecial : ProjectiveThresholdCondition
      (fun ℓ => (weightedPolynomialFamily w (β ℓ) (f ℓ)).eval 0) h := by
    simp only [hzero]
    exact projectiveThresholdCondition_monomial β (fun ℓ => (f ℓ).coeff (β ℓ)) hcoeff h hh hmon
  obtain ⟨t, ht, hfib⟩ := hdeg n w β f h hf (fun ℓ => (hβ ℓ).1) hw' hspecial
  -- a nonzero fibre is the diagonal transform up to nonzero constants
  have hscaled : ∀ ℓ, MvPolynomial.C (t ^ polynomialExponentWeight w (β ℓ)) *
      (weightedPolynomialFamily w (β ℓ) (f ℓ)).eval (MvPolynomial.C t) =
        polynomialDiagonalHom w t (f ℓ) := fun ℓ =>
    weightedPolynomialFamily_scaled_parameter w (β ℓ) (f ℓ) t (fun q hq => by
      by_cases hqe : q = β ℓ
      · rw [hqe]
      · exact (hw' ℓ q hq hqe).le)
  have hdiag : ProjectiveThresholdCondition (fun ℓ => polynomialDiagonalHom w t (f ℓ)) h := by
    have h1 := (projectiveThresholdCondition_C_mul_iff
      (fun ℓ => (weightedPolynomialFamily w (β ℓ) (f ℓ)).eval (MvPolynomial.C t))
      (fun ℓ => t ^ polynomialExponentWeight w (β ℓ)) (fun ℓ => pow_ne_zero _ ht) h).mpr hfib
    simpa only [hscaled] using h1
  exact projectiveThresholdCondition_of_polynomialDiagonalHom f hf w ht h hdiag

/-- (34) for the leading forms of power series φ_l whose degree-lexicographic initial exponents
β_l satisfy the real chart inequalities with a positive margin (the sections of the equality case
of Lemma 5), from the degeneration form of Lemma 3. -/
theorem leadingForms_projectiveThresholdCondition (hn : 0 < n)
    (hdeg : ThresholdDegenerationStatement K)
    (φ : Fin n × Fin n → MvPowerSeries (Fin n) K) (β : Fin n × Fin n → Fin n →₀ ℕ)
    (hφ : ∀ l, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) (φ l) (β l))
    {H : ℕ} (hH : 1 ≤ H) {μ : ℝ} (hμ : 0 < μ)
    (hmargin : ∀ (w : Fin n → ℝ) (k : Fin n), w k = 0 → ∃ i : Fin n,
      (∑ q, w q * (β (k, i) q : ℝ)) ≤ (H : ℝ) * (1 - μ) * (∑ q, w q)) :
    ProjectiveThresholdCondition (fun l => homogeneousTaylorForm (β l).degree (φ l)) H := by
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  exact projectiveThresholdCondition_of_lexInitial hdeg _
    (fun l => ⟨_, homogeneousTaylorForm_isHomogeneous _ _⟩) β
    (fun l => homogeneousTaylorForm_lexInitial (hφ l)) H hH
    (fun k u hu => chart_inequalities_nat_of_margin β (fun k i => (k, i)) hH hμ hmargin k u hu)

end Forms

section Lifting

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The geometric half of Lemma 5 from (34) on (§8): on a smooth variety X of dimension n with an
ample sum A and a nef divisor N, finitely many sections of e A with e < h, vanishing order n h at a
closed point x, whose leading forms (the degree n h parts of their Taylor series, which generate
the restriction of the base ideal to the exceptional divisor of the blow-up of x) satisfy the
threshold condition (34) for h, force K_X + A + N to be generated at x. In the manuscript: the
positivity (35) with τ = e/h < 1, a log resolution, Kawamata–Viehweg vanishing, adjunction to the
strict transform of the exceptional divisor and descent. -/
def ThresholdLiftingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
      (c₀ : EtaleChart K X n) (A N : CartierDivisor X), CartierIsAmpleSum K A →
      CartierIsNef K N → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
        (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (e h : ℕ), 0 < h → e < h →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → Γ((e • A).sheaf, ⊤)),
          (∀ l, s l ≠ 0) →
          (∀ l, cartierSectionVanishingOrder _ x (s l) = (n * h : ℕ)) →
          ProjectiveThresholdCondition (fun l => homogeneousTaylorForm (n * h)
            (cartierTaylorCoordinates _ x (f ^ e) (cartierLocalEquation_pow A x f hf e)
              coordinates (s l))) h →
          ∃ (f' : X.functionFieldˣ)
            (hf' : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f')
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f' hf' t)

/-- The geometric half of Lemma 5 splits into Lemma 3 in its degeneration form and the lifting
from (34) on. -/
theorem equalityCaseLifting_of_thresholdLifting
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hlift : ThresholdLiftingStatement.{u}) : EqualityCaseLiftingStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN x hx f hf coordinates r a b j D δ hr ha hb hab
    hab' hj hD hδ β s hs hinit hord hmargin
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnoeth := smoothScheme_stalk_isNoetherianRing (K := K) x
  have hH : 0 < equalityHeight r j D b := equalityHeight_pos hr hj hD hb
  have hlt : equalitySectionDegree r j D a < equalityHeight r j D b := by
    unfold equalitySectionDegree equalityHeight
    exact Nat.mul_lt_mul_of_pos_left hab' (by positivity)
  -- the initial exponents have degree n h
  have hdegβ : ∀ l, ((r * a) • β l).degree = n * equalityHeight r j D b := by
    intro l
    have h1 := degreeLex_initial_order (hinit l)
    rw [cartierTaylorCoordinates_order_eq_vanishingOrder, hord l] at h1
    exact_mod_cast h1.symm
  have hμ : (0 : ℝ) < (((a : ℚ) / b * δ : ℚ) : ℝ) / n := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hq : (0 : ℚ) < (a : ℚ) / b * δ := by
      have : (0 : ℚ) < a := by exact_mod_cast ha
      have : (0 : ℚ) < b := by exact_mod_cast hb
      positivity
    have hq' : (0 : ℝ) < (((a : ℚ) / b * δ : ℚ) : ℝ) := by exact_mod_cast hq
    positivity
  have h34 := leadingForms_projectiveThresholdCondition (by omega) (hdeg K)
    (fun l => cartierTaylorCoordinates _ x (f ^ equalitySectionDegree r j D a)
      (cartierLocalEquation_pow A x f hf _) coordinates (s l))
    (fun l => (r * a) • β l) hinit (H := equalityHeight r j D b) (by omega) hμ hmargin
  simp only [hdegβ] at h34
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  exact hlift K X n hdim hn c₀ A N hA hN x hx f hf coordinates _ _ hH hlt s hs hord h34

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, Lemma 3 in its degeneration
form and the lifting from (34) on. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_thresholdLifting
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hlift : ThresholdLiftingStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_equalityCaseLifting hKV hcl
    (equalityCaseLifting_of_thresholdLifting hdeg hlift)

end Lifting

end MixedFujita

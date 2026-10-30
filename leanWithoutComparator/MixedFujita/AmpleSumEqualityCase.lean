/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityCaseAtPoint
public import MixedFujita.OrderAverageMinimizerData

/-!
Lemma 5 for an ample sum, up to its geometric half (§8; steps 13 and 14).

Let A be an ample sum on a smooth variety X of dimension n over an algebraically closed field,
satisfying the numerical hypothesis. Then:
* the volume satisfies n! c ≥ (n + 1)^n, where h⁰(j A)/j^n → c: the numerical hypothesis at the
  generic point bounds the dimension of the sections of j A from below;
* a positive multiple k A is the hyperplane class of a closed immersion up to a principal divisor,
  the multiples m A are globally generated for m large, so the Hilbert limit exists, and smooth
  closed points have Taylor coordinates; hence at every closed point x where (33) fails, the
  sections of the equality case exist (`ampleSum_equality_case_sections_of_not_orderAverage`).

The geometric half of Lemma 5 is stated as `EqualityCaseLiftingStatement`. Given such sections of
h τ A, it says that K_X + A + N is generated at x. In the manuscript this is the blow-up of the
point, the threshold on the exceptional divisor (34) through Lemma 3, the positivity (35),
Kawamata–Viehweg vanishing, adjunction and descent. With it, (33) holds at every closed point
where K_X + A + N is not generated, so the minimizer statement and F1 follow from the closedness
of the realization sets, this statement and the sum form of the Kawamata–Viehweg statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Volume

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The closure of the generic point has the dimension of the scheme. -/
theorem topologicalKrullDim_closure_genericPoint {m : ℕ} (hdimY : topologicalKrullDim Y = m) :
    topologicalKrullDim (closure ({genericPoint Y} : Set Y)) = m := by
  have hcl : closure ({genericPoint Y} : Set Y) = Set.univ := (genericPoint_spec Y).def
  rw [hcl, IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph, hdimY]

/-- The numerical hypothesis at the generic point bounds the volume: if h⁰(j A)/j^m tends to c,
then m! c ≥ (m + 1)^m. -/
theorem volume_ge_of_restrictedGrowth {m : ℕ} (hdimY : topologicalKrullDim Y = m) (hm : 1 ≤ m)
    (A : CartierDivisor Y) [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    {c : ℝ} (hN : Tendsto (fun j : ℕ => (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) /
      (j : ℝ) ^ m) atTop (𝓝 c)) :
    ((m + 1 : ℕ) : ℝ) ^ m ≤ (m.factorial : ℝ) * c := by
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hlow : ∀ ε : ℝ, 0 < ε → ((m + 1 : ℝ) ^ m - ε) / m.factorial ≤ c := by
    intro ε hε
    refine ge_of_tendsto hN ?_
    filter_upwards [hgrow (genericPoint Y) m (topologicalKrullDim_closure_genericPoint hdimY)
      hm ε hε, eventually_ge_atTop 1] with j hj hj1
    obtain ⟨V, hV, hle⟩ := hj
    have hj0 : (0 : ℝ) < (j : ℝ) ^ m := by
      have : (0 : ℝ) < j := by exact_mod_cast hj1
      positivity
    have h1 : (cartierRestrictedSubspaceDim K (j • A) (genericPoint Y) V : ℝ) ≤
        Module.finrank K Γ((j • A).sheaf, ⊤) := by
      unfold cartierRestrictedSubspaceDim
      exact_mod_cast (Submodule.finrank_map_le _ V).trans (Submodule.finrank_le V)
    rw [le_div_iff₀ hj0]
    have h2 := hle.trans h1
    rw [div_le_iff₀ hf] at h2
    rw [div_mul_eq_mul_div, div_le_iff₀ hf]
    exact h2
  have hc : (m + 1 : ℝ) ^ m / m.factorial ≤ c := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have h := hlow (ε * m.factorial / 2) (by positivity)
    have heq : ((m + 1 : ℝ) ^ m - ε * m.factorial / 2) / m.factorial =
        (m + 1 : ℝ) ^ m / m.factorial - ε / 2 := by
      field_simp
    rw [heq] at h
    linarith
  rw [div_le_iff₀ hf] at hc
  push_cast
  linarith

end Volume

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] {m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]

/-- The combinatorial half of Lemma 5 for an ample sum: at a closed point where (33) fails, the
sections of the equality case exist (for some local equation of A and Taylor coordinates at x). -/
theorem ampleSum_equality_case_sections_of_not_orderAverage (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (A : CartierDivisor Y) (hA : CartierIsAmpleSum K A)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hnot : ¬ ∃ σ : ℝ, (m : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ))
    {r a b : ℕ} (hr : 0 < r) (ha : 0 < a) (hb : 0 < b) (hab : m * b < (m + 1) * a) :
    ∃ (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
      (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
        (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin m) K)
      (j D : ℕ) (δ : ℚ), 0 < j ∧ 0 < D ∧ 0 < δ ∧
      ∃ (β : Fin m × Fin m → Fin m →₀ ℕ)
        (s : Fin m × Fin m → Γ((equalitySectionDegree r j D a • A).sheaf, ⊤)),
        (∀ l, s l ≠ 0) ∧
        (∀ l, IsInitialMonomial (MonomialOrder.degLex (σ := Fin m))
          (cartierTaylorCoordinates _ x (f ^ equalitySectionDegree r j D a)
            (cartierLocalEquation_pow A x f hf _) coordinates (s l)) ((r * a) • β l)) ∧
        (∀ l, cartierSectionVanishingOrder _ x (s l) = (m * equalityHeight r j D b : ℕ)) ∧
        ∀ (w : Fin m → ℝ) (k : Fin m), w k = 0 → ∃ i : Fin m,
          (∑ q, w q * (((r * a) • β (k, i)) q : ℝ)) ≤
            (equalityHeight r j D b : ℝ) * (1 - (((a : ℚ) / b * δ : ℚ) : ℝ) / m) *
              (∑ q, w q) := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  have hA' := cartierIsAmpleProj_of_isAmpleSum hA
  -- nonzero sections in all large degrees
  obtain ⟨e₀, he₀⟩ := cartierIsAmpleProj_eventually_globallyGenerated hA'
  have hsec : ∀ q, e₀ ≤ q → ∃ σ : Γ((q • A).sheaf, ⊤), σ ≠ 0 := by
    intro q hq
    obtain ⟨σ, hσ⟩ := he₀ q hq x
    refine ⟨σ, ?_⟩
    rintro rfl
    rw [map_zero] at hσ
    exact not_isUnit_zero hσ
  -- the Hilbert limit
  obtain ⟨k, hk, n, e, hci, he, g, hg, hggen, φ, hkA⟩ := hA'
  obtain ⟨rH, hrH, hfin, hlim⟩ := projectiveHyperplane_hilbert_of_multiple_add_principal e g hg
    hggen he hdimY hm A hk φ hkA e₀ hsec
  have := hfin
  have hc : (0 : ℝ) < (rH : ℝ) / m.factorial / (k : ℝ) ^ m := by
    have : (0 : ℝ) < rH := by exact_mod_cast hrH
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    positivity
  have hvol := volume_ge_of_restrictedGrowth hdimY hm A hgrow hlim
  -- Taylor coordinates at x
  have hnoeth := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨f, hf, coordinates, -, -⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData
    (K := K) m hdimY A x hxc
  exact ⟨f, hf, coordinates, cartier_equality_case_sections_of_not_orderAverage A x f hf
    (by omega) coordinates hc hlim hvol hnot hr ha hb hab⟩

end Assembly

/-- The geometric half of Lemma 5 (§8, from (34) on): on a smooth variety X of dimension n with an
ample sum A and a nef divisor N, sections of h τ A (τ = a/b with n/(n + 1) < τ < 1) with
vanishing order n h at a closed point x whose degree-lexicographic initial exponents satisfy the
strict chart inequalities of (34) force K_X + A + N to be generated at x. In the manuscript: the
blow-up of x, the threshold on the exceptional divisor through Lemma 3, the positivity (35),
Kawamata–Viehweg vanishing, adjunction and descent. The bound τ < 1 (a < b) is what makes
(1 − τ) A in (35) big; without it the statement fails already for a point A = p on a curve of
genus one with a = b = 1. -/
def EqualityCaseLiftingStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
      (c₀ : EtaleChart K X n) (A N : CartierDivisor X), CartierIsAmpleSum K A →
      CartierIsNef K N → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
        (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (r a b j D : ℕ) (δ : ℚ),
        0 < r → 0 < a → 0 < b → n * b < (n + 1) * a → a < b → 0 < j → 0 < D → 0 < δ →
        ∀ (β : Fin n × Fin n → Fin n →₀ ℕ)
          (s : Fin n × Fin n → Γ((equalitySectionDegree r j D a • A).sheaf, ⊤)),
          (∀ l, s l ≠ 0) →
          (∀ l, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n))
            (cartierTaylorCoordinates _ x (f ^ equalitySectionDegree r j D a)
              (cartierLocalEquation_pow A x f hf _) coordinates (s l)) ((r * a) • β l)) →
          (∀ l, cartierSectionVanishingOrder _ x (s l) = (n * equalityHeight r j D b : ℕ)) →
          (∀ (w : Fin n → ℝ) (k : Fin n), w k = 0 → ∃ i : Fin n,
            (∑ q, w q * (((r * a) • β (k, i)) q : ℝ)) ≤
              (equalityHeight r j D b : ℝ) * (1 - (((a : ℚ) / b * δ : ℚ) : ℝ) / n) *
                (∑ q, w q)) →
          ∃ (f' : X.functionFieldˣ)
            (hf' : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f')
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f' hf' t)

/-- Lemma 5 from its geometric half: at a closed point where K_X + A + N is not generated, the
bound (33) holds. -/
theorem orderAverage_of_equalityCaseLifting (hlift : EqualityCaseLiftingStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
    (c₀ : EtaleChart K X n) (A N : CartierDivisor X) (hA : CartierIsAmpleSum K A)
    (hN : CartierIsNef K N)
    (hnum : ∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hnf : ¬ ∃ (f : X.functionFieldˣ)
      (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
      (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
      IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) :
    ∃ σ : ℝ, (n : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ) := by
  by_contra hnot
  have hab : n * (2 * n + 2) < (n + 1) * (2 * n + 1) := by nlinarith
  obtain ⟨f, hf, coordinates, j, D, δ, hj, hD, hδ, β, s, hs, hinit, hord, hmargin⟩ :=
    ampleSum_equality_case_sections_of_not_orderAverage hn c₀ A hA hnum x hx hnot
      (r := 1) (a := 2 * n + 1) (b := 2 * n + 2) one_pos (by omega) (by omega) hab
  exact hnf (hlift K X n hdim hn c₀ A N hA hN x hx f hf coordinates 1 (2 * n + 1) (2 * n + 2) j D
    δ one_pos (by omega) (by omega) hab (by omega) hj hD hδ β s hs hinit hord hmargin)

/-- The minimizer statement used by S-NF for ample sums follows from the closedness of the
realization sets of ample sums at closed points and the geometric half of Lemma 5. -/
theorem smoothMinimizerDataStatement_of_closed_of_equalityCaseLifting
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
    (hlift : EqualityCaseLiftingStatement.{u}) :
    SmoothMinimizerDataStatement.{u} :=
  smoothMinimizerDataStatement_of_closed_of_orderAverage hcl
    (fun K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN hnum _ x hx hnf =>
      orderAverage_of_equalityCaseLifting hlift K X n hdim hn c₀ A N hA hN hnum x hx hnf)

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, and the geometric half of
Lemma 5. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_equalityCaseLifting
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
    (hlift : EqualityCaseLiftingStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_minimizerData hKV
    (smoothMinimizerDataStatement_of_closed_of_equalityCaseLifting hcl hlift)

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveUniformOrderBound
public import MixedFujita.MixedBrunnMinkowski
public import MixedFujita.WeightedTaylorOrder

/-!
The cube condition from actual forms. At a closed point x of an actual closed subscheme of
polynomial projective space, with completion coordinates in N variables, every power series is
the Taylor expansion of an actual form section of degree D ≥ N up to order N + 1: approximate it
by an element of the local ring and realize the jet by a pulled-back homogeneous equation. A
series that agrees with the monomial X^e beyond degree |e| has e as its initial monomial in every
monomial order that compares the total degree first. Hence for every S ⊆ {1, ..., N} some form
section of degree D has initial exponent 1_S, and the initial exponents of the Taylor image of
Γ(D J) contain the cube {0,1}^N: the input of the slice growth (17) and of the mixed
Brunn–Minkowski bound, supplied by the embedding itself.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

section PowerSeries

variable {K : Type*} [Field K] {σ : Type*}

/-- A series that agrees with X^e beyond degree |e| has e as its initial monomial in every
monomial order compatible with the total degree. -/
theorem isInitialMonomial_of_order_sub_gt (m : MonomialOrder σ) {φ : MvPowerSeries σ K}
    {e : σ →₀ ℕ} (hdeg : ∀ q, m.toSyn q < m.toSyn e → q.degree ≤ e.degree)
    (hφ : ((e.degree + 1 : ℕ) : ℕ∞) ≤ (φ - MvPowerSeries.monomial e 1).order) :
    IsInitialMonomial m φ e := by
  classical
  have hcoef : ∀ q : σ →₀ ℕ, q.degree ≤ e.degree →
      MvPowerSeries.coeff q (φ - MvPowerSeries.monomial e 1) = 0 := by
    intro q hq
    apply MvPowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hq) hφ
  have hsplit : ∀ q, MvPowerSeries.coeff q φ =
      MvPowerSeries.coeff q (φ - MvPowerSeries.monomial e 1) +
        MvPowerSeries.coeff q (MvPowerSeries.monomial e (1 : K)) := by
    intro q
    rw [map_sub]
    ring
  refine ⟨?_, fun q hq => ?_⟩
  · rw [hsplit, hcoef e le_rfl, zero_add, MvPowerSeries.coeff_monomial_same]
    exact one_ne_zero
  · have hqe : q ≠ e := fun h => by rw [h] at hq; exact lt_irrefl _ hq
    rw [hsplit, hcoef q (hdeg q hq), zero_add, MvPowerSeries.coeff_monomial,
      ite_eq_right_iff.mpr (fun h => absurd h hqe)]

theorem realExponentWeight_one_eq_degree [Fintype σ] (q : σ →₀ ℕ) :
    realExponentWeight (fun _ : σ => (1 : ℝ)) q = (q.degree : ℝ) := by
  change ∑ i, 1 * (q i : ℝ) = _
  rw [Finsupp.degree_eq_sum, Nat.cast_sum]
  simp only [one_mul]

/-- The weighted order with all weights 1 compares the total degree first. -/
theorem weightedMonomialOrder_one_degree_le [Fintype σ] (m₀ : MonomialOrder σ) (v : σ → ℕ)
    (hw : ∀ i, (0 : ℝ) ≤ (fun _ : σ => (1 : ℝ)) i) {q e : σ →₀ ℕ}
    (h : (weightedMonomialOrder m₀ (fun _ => 1) v hw).toSyn q <
      (weightedMonomialOrder m₀ (fun _ => 1) v hw).toSyn e) : q.degree ≤ e.degree := by
  rw [weightedMonomialOrder_lt_iff] at h
  have hle : realExponentWeight (fun _ : σ => (1 : ℝ)) q ≤
      realExponentWeight (fun _ : σ => (1 : ℝ)) e := by
    rcases h with h | ⟨h, -⟩
    · exact h.le
    · exact h.le
  rw [realExponentWeight_one_eq_degree, realExponentWeight_one_eq_degree] at hle
  exact_mod_cast hle

theorem degree_sum_single (S : Finset σ) :
    (∑ i ∈ S, Finsupp.single i (1 : ℕ)).degree = S.card := by
  classical
  rw [map_sum]
  simp only [Finsupp.degree_single, Finset.sum_const, smul_eq_mul, mul_one]

end PowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- For every S, some form section of degree D ≥ N has Taylor expansion with initial exponent 1_S
in every total-degree-compatible monomial order. -/
theorem projectiveFormSection_initial_cube
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (x : Y)
    (hx : x ∈ projectivePullbackCoordinateOpen e j.val) (hcl : IsClosed {x})
    [IsNoetherianRing (Y.presheaf.stalk x)] {N : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
      (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin N) K)
    (m : MonomialOrder (Fin N)) (hdeg : ∀ q p, m.toSyn q < m.toSyn p → q.degree ≤ p.degree)
    {D : ℕ} (hD : N ≤ D) (S : Finset (Fin N)) :
    ∃ (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D),
      IsInitialMonomial m (cartierTaylorCoordinates (D • projectiveHyperplaneCartier e g hg hggen) x
        (projectiveHyperplaneUnit e g hg hggen j ^ D)
        (cartierLocalEquation_pow _ x _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j x hx)
          D) coords (projectiveFormSection e g hg hggen j D F hF))
        (∑ i ∈ S, Finsupp.single i 1) := by
  set eS : Fin N →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1 with heS
  set P : MvPowerSeries (Fin N) K := MvPowerSeries.monomial eS 1 with hP
  obtain ⟨y, hy⟩ := completionCoordinates_exists_approx coords.toRingEquiv P (N + 1)
  obtain ⟨F, hF, hFy⟩ := polynomialProjective_closedImmersion_jet_realized e j.val x hx hcl
    (m := N) (D := D) hD y
  refine ⟨F, hF, ?_⟩
  apply isInitialMonomial_of_order_sub_gt m (fun q hq => hdeg q eS hq)
  have hT : cartierTaylorCoordinates (D • projectiveHyperplaneCartier e g hg hggen) x
      (projectiveHyperplaneUnit e g hg hggen j ^ D)
      (cartierLocalEquation_pow _ x _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j x hx)
        D) coords (projectiveFormSection e g hg hggen j D F hF) =
      coords (algebraMap (Y.presheaf.stalk x)
        (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x))
        (Y.presheaf.germ _ x hx (projectivePullbackHomogeneousEquation e j.val D F hF))) := by
    rw [cartierTaylorCoordinates_apply, projectiveFormSection_localCoefficient e g hg hggen j j x hx
      D F hF]
  rw [hT]
  have hmem : Y.presheaf.germ _ x hx (projectivePullbackHomogeneousEquation e j.val D F hF) - y ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ (N + 1) := by
    have h' := neg_mem hFy
    rwa [neg_sub] at h'
  have h1 := completionCoordinates_order_ge_of_mem_pow coords.toRingEquiv hmem
  rw [map_sub, map_sub] at h1
  have h2 : ((N + 1 : ℕ) : ℕ∞) ≤ (coords.toRingEquiv (algebraMap (Y.presheaf.stalk x)
      (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (Y.presheaf.stalk x)) y) -
        P).order := by
    rw [← MvPowerSeries.order_neg, neg_sub]
    exact hy
  have h3 := (le_min h1 h2).trans MvPowerSeries.min_order_le_add
  rw [sub_add_sub_cancel] at h3
  have hdegS : eS.degree ≤ N := by
    rw [heS, degree_sum_single]
    exact (Finset.card_le_univ S).trans (by simp)
  refine le_trans ?_ h3
  exact_mod_cast Nat.succ_le_succ hdegS

/-- The cube condition: the initial exponents of the Taylor image of Γ(D J) contain {0,1}^(d+1)
for D ≥ d + 1, in every total-degree-compatible monomial order. -/
theorem projectiveHyperplane_binaryVectors_subset
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) (x : Y)
    (hx : x ∈ projectivePullbackCoordinateOpen e j.val) (hcl : IsClosed {x})
    [IsNoetherianRing (Y.presheaf.stalk x)] {d : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
      (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin (d + 1)) K)
    (m : MonomialOrder (Fin (d + 1))) (hdeg : ∀ q p, m.toSyn q < m.toSyn p → q.degree ≤ p.degree)
    {D : ℕ} (hD : d + 1 ≤ D)
    [FiniteDimensional K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)] :
    binaryVectors (d + 1) ⊆ initialExponentSet m (LinearMap.range
      (cartierTaylorCoordinates (D • projectiveHyperplaneCartier e g hg hggen) x
        (projectiveHyperplaneUnit e g hg hggen j ^ D)
        (cartierLocalEquation_pow _ x _ (projectiveHyperplane_isLocalEquationAt e g hg hggen j x hx)
          D) coords)) := by
  classical
  intro γ hγ
  have hγ01 : ∀ i, γ i = 0 ∨ γ i = 1 := by
    intro i
    have h := Fintype.mem_piFinset.mp hγ i
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  obtain ⟨F, hF, hinit⟩ := projectiveFormSection_initial_cube e g hg hggen j x hx hcl coords m hdeg
    hD (Finset.univ.filter fun i => γ i = 1)
  rw [mem_initialExponentSet]
  refine ⟨∑ i ∈ Finset.univ.filter (fun i => γ i = 1), Finsupp.single i 1,
    (mem_initialMonomialFinset m _ _).mpr ⟨_, ⟨projectiveFormSection e g hg hggen j D F hF, rfl⟩,
      hinit⟩, ?_⟩
  funext i
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rcases hγ01 i with h | h <;> simp [h]

end MixedFujita

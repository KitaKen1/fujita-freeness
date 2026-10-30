/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorExponentObjective

/-!
The infimum of the objective over all bases and all weights (step 11; the quantity N f_{j,t}(x) of
the manuscript, (5)).

For a Cartier divisor D whose sections have bases of N elements, a point x and t, j, the infimum
is taken over the values Σ_i exp(a/t − v_i/j) of the objective at the profile data (a, v) at x of
all bases of the sections of D: all weights over the fibre of x on all proper simple normal
crossing models of all bases. It is a real number, nonnegative, at most every value, and at least
every common lower bound of the values when there is a value.

With it the statements of section 5 read:

* the specialization comparison (6) between two points is an inequality between two infima;
* (16) holds for a weight whose objective is at most the infimum at π(z) (that is, a weight
  minimizing at x together with (6) from x to π(z));
* the infimum for any Cartier divisor D' is at most the sum over the initial exponents at z of the
  sections of D' of exp(lam A/t − lam ℓ(p)/j), for every scale lam > 0 (the upper bound for the
  infimum in (21));
* (21): for a weight on a model of a basis of D whose objective is at most the infimum at x,
  inf(D') · Q ≤ inf(D) · Q' for every D' and every scale, with Q and Q' the sums over the initial
  exponents of D and of D'. With D' = j L and the scale j/m this is
  (N_j f_j / N_m f_m) exp((1 − j/m) A/t) ≤ Q_j / Q_m.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Infimum

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The values of the objective at the profile data at x of all bases of N elements of the
sections of D. -/
def sncWeightObjectiveValues (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ) : Set ℝ :=
  {val | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
    ∃ p ∈ sncWeightProfiles cY fY d D₀ D x B, val = ∑ i, Real.exp (p.1 / t - p.2 i / j)}

/-- The infimum of the objective over all bases of the sections of D and all weights over the
fibre of x on their proper simple normal crossing models. -/
noncomputable def sncWeightInfimum (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ) : ℝ :=
  sInf (sncWeightObjectiveValues cY fY d D₀ D x N t j)

theorem sncWeightObjectiveValues_nonneg (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ) :
    ∀ val ∈ sncWeightObjectiveValues cY fY d D₀ D x N t j, 0 ≤ val := by
  rintro val ⟨B, p, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

theorem sncWeightInfimum_nonneg (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ) :
    0 ≤ sncWeightInfimum cY fY d D₀ D x N t j :=
  Real.sInf_nonneg (sncWeightObjectiveValues_nonneg cY fY d D₀ D x N t j)

/-- The infimum is at most the objective of every profile datum of every basis. -/
theorem sncWeightInfimum_le (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (t j : ℝ)
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ sncWeightProfiles cY fY d D₀ D x B) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j) :=
  csInf_le ⟨0, sncWeightObjectiveValues_nonneg cY fY d D₀ D x N t j⟩ ⟨B, p, hp, rfl⟩

/-- A number which is at least every common lower bound of the objectives is at least the
infimum. -/
theorem sncWeightInfimum_le_of_forall_le (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ) {R : ℝ}
    (h : ∀ L : ℝ, (∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∀ p ∈ sncWeightProfiles cY fY d D₀ D x B, L ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j)) →
      L ≤ R) :
    sncWeightInfimum cY fY d D₀ D x N t j ≤ R :=
  h _ fun B _ hp => sncWeightInfimum_le cY fY d D₀ D x t j B hp

/-- A common lower bound of the objectives is at most the infimum, when there is a profile
datum. -/
theorem le_sncWeightInfimum (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) (N : ℕ) (t j : ℝ)
    (hne : (sncWeightObjectiveValues cY fY d D₀ D x N t j).Nonempty) {L : ℝ}
    (hL : ∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∀ p ∈ sncWeightProfiles cY fY d D₀ D x B, L ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j)) :
    L ≤ sncWeightInfimum cY fY d D₀ D x N t j := by
  refine le_csInf hne ?_
  rintro val ⟨B, p, hp, rfl⟩
  exact hL B p hp

end Infimum

section Geometry

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- The infimum for a Cartier divisor D' at x is at most the sum over the initial exponents at z
of the sections of D' for the weight scaled by lam > 0 (the upper bound for N_j f_j in (21)). -/
theorem sncWeightInfimum_le_sum_initialExponents {r N : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (y : X) (hy : y ∈ c.U) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X))
    (x : Y) (hx : π y ⤳ x) (z : X) (hz : z ∈ c.U) (hyz : y ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D' : CartierDivisor Y) [FiniteDimensional K Γ(D'.sheaf, ⊤)]
    (hN : Module.finrank K Γ(D'.sheaf, ⊤) = N)
    (v : Fin n → ℕ) (m : MonomialOrder (Fin n)) {lam t j : ℝ} (hlam : 0 < lam) (ht : 0 < t)
    (hj : 0 < j) :
    sncWeightInfimum cY fY d D₀ D' x N t j ≤
      ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
          (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)),
        Real.exp (lam * (∑ k, w k * (((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
          lam * realExponentWeight (sncChartCoordinateWeights σc w) p / j) :=
  sncWeightInfimum_le_of_forall_le cY fY d D₀ D' x N t j
    (fun _ hL => le_sum_initialExponents_of_le_sncWeightProfiles π hπ cY fY d hd D₀ cX ξ hinj hξ
      hsnc hBsupp c σc hc y hy w hw0 hwne hwy x hx z hz hyz ez hez D' hN v m hlam ht hj hL)

/-- The tangential moment bound (16) for a weight whose objective is at most the infimum at
π(z). -/
theorem sncWeight_tangential_moment_le_of_le_infimum {r N : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) [FiniteDimensional K Γ(D.sheaf, ⊤)] (hN : 0 < N)
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (t : X) = 0)
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0)
    (hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a)
    (v u : Fin n → ℕ) (hv : ∀ k a, σc k = some a → v a = 0)
    (hu : ∀ k a, σc k = some a → u a = 0) (m : MonomialOrder (Fin n)) {t j : ℝ} (ht : 0 < t)
    (hj : 0 < j)
    (hspec : (∑ i, Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j)) ≤
      sncWeightInfimum cY fY d D₀ D (π z) N t j) :
    sectionExponentialMoment
      (initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
          (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear D π z ez)))
      (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
      (fun p => (natExponentDegree v p : ℝ)) j ≤ (∑ a, (v a : ℝ)) / t :=
  sncWeight_tangential_moment_le π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc hBsupp c σc hc z hz ez hez
    D hN B hGsupp w hw0 hwne hwσ v u hv hu m ht hj
    (fun B' _ hp' => hspec.trans (sncWeightInfimum_le cY fY d D₀ D (π z) t j B' hp'))

/-- The comparison (21) for a weight minimizing the objective. Let w be a weight on a model of a
basis B of the sections of D whose objective is at most the infimum at x, with Taylor data at a
point z of its stratum. For every Cartier divisor D' and every scale lam > 0,
inf(D') · Q ≤ inf(D) · Q', where Q = Σ_{Γ(D)} exp(A/t − ℓ(p)/j) and
Q' = Σ_{Γ(D')} exp(lam A/t' − lam ℓ(p)/j'). -/
theorem sncWeightInfimum_mul_sum_initialExponents_le {r N N' : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (y : X) (hy : y ∈ c.U) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwne : w ≠ 0)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X))
    (x : Y) (hx : π y ⤳ x) (z : X) (hz : z ∈ c.U) (hyz : y ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) [FiniteDimensional K Γ(D.sheaf, ⊤)]
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (t : X) = 0)
    (D' : CartierDivisor Y) [FiniteDimensional K Γ(D'.sheaf, ⊤)]
    (hN' : Module.finrank K Γ(D'.sheaf, ⊤) = N')
    (v : Fin n → ℕ) (m : MonomialOrder (Fin n)) {lam t j t' j' : ℝ} (hlam : 0 < lam)
    (hj : 0 < j) (ht' : 0 < t') (hj' : 0 < j')
    (hmin : (∑ i, Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
        (∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j)) ≤
      sncWeightInfimum cY fY d D₀ D x N t j) :
    sncWeightInfimum cY fY d D₀ D' x N' t' j' *
        ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
            (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear D π z ez)),
          Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
            realExponentWeight (sncChartCoordinateWeights σc w) p / j) ≤
      sncWeightInfimum cY fY d D₀ D x N t j *
        ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
            (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)),
          Real.exp (lam * (∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t' -
            lam * realExponentWeight (sncChartCoordinateWeights σc w) p / j') := by
  have hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a := by
    intro k hk
    cases hσ : σc k with
    | none =>
      exfalso
      have hmem : y ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hwy k hk, hy⟩
      rw [hc.2 k, hσ] at hmem
      exact hmem
    | some a => exact ⟨a, rfl⟩
  have h1 := sum_initialExponents_le_sncWeight_objective π ξ hinj hξ hsnc c σc hc z hz ez hez D B
    hGsupp w hw0 hwσ v m (∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) t hj
  have h3 := sncWeightInfimum_le_sum_initialExponents π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc hBsupp
    c σc hc y hy w hw0 hwne hwy x hx z hz hyz ez hez D' hN' v m hlam ht' hj'
  rw [mul_comm (sncWeightInfimum cY fY d D₀ D x N t j)]
  exact mul_le_mul h3 (h1.trans hmin) (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)
    (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le)

end Geometry

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TangentialMomentBound

/-!
The sums Q over the initial exponents and the infima of the objective (step 11, section 5.3 of the
manuscript, the comparison (21)).

Let w be a weight on the members of a simple normal crossing family of a model π : X → Y of the
pair, z a point of a simple normal crossing chart with Taylor coordinates the coordinates of the
chart, ℓ(p) = Σ_a w_a p_a the weight of an exponent for the weights induced on the coordinates and
A(w) = Σ_k w_k a_k the log discrepancy of the weight. For a Cartier divisor D' of Y let Γ(D') be
the set of the initial exponents of the Taylor expansions at z of the pullbacks of the sections of
D', for the order comparing first ℓ, then the degree in the directions v, then a monomial order.

* Upper bound by the basis of the model. If the pulled back zero divisors of a basis B of the
  sections of D are supported on the family and all the members of positive weight pass through z,
  then Σ_{p ∈ Γ(D)} exp(A(w)/t − ℓ(p)/j) ≤ Σ_i exp(A(w)/t − v_i(w)/j): the basis adapted to the
  initial exponents does at least as well as B.
* Lower bound by the infimum, for every Cartier divisor D' and every scale. Let y be a point of the
  chart through all the members of positive weight, specializing to z, with π(y) specializing to
  x. If L is a lower bound for the objective Σ_i exp(a/t − v_i/j) over the profile data at x of
  all bases of the sections of D', then for every lam > 0
  L ≤ Σ_{p ∈ Γ(D')} exp(lam A(w)/t − lam ℓ(p)/j):
  the weight scaled by lam is a monomial Taylor test for the sections of D'.

With D' = D and lam = 1 the two bounds give, for a weight minimizing the objective over all bases
and weights, exp(A/t) Q_m = N_m f_m; with D' = j L and lam = j/m the second gives
N_j f_j ≤ exp((j/m) A/t) Q_j, where Q_j = Σ_{p ∈ Γ(jL)} exp(−ℓ(p)/m). Together this is (21).
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

section Algebra

variable {σ K : Type*} [Fintype σ] [Field K]

/-- The real weighted order of a member of the basis adapted to the initial exponents is the
weight of its initial exponent. -/
theorem realWeightedOrder_weightedSubspaceInitialBasis (m : MonomialOrder σ) (w : σ → ℝ)
    (v : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S]
    (q : initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) :
    realWeightedOrder w (weightedSubspaceInitialBasis m w v hw S q).val =
      realExponentWeight w ((weightedMonomialOrder m w v hw).toSyn.symm q.val) := by
  have hne : (weightedSubspaceInitialBasis m w v hw S q).val ≠ 0 :=
    initialMonomial_series_ne_zero _ (weightedSubspaceInitialBasis_spec m w v hw S q)
  have h := powerSeriesPerturbedValue_eq_realWeightedOrder m w v v hw hne (le_refl (0 : ℝ))
  have hfun : (fun i => w i + 0 * (v i : ℝ) + 0 ^ 2 * (v i : ℝ)) = w := by
    funext i
    simp
  rw [hfun] at h
  rw [← h]
  exact weightedSubspaceInitialBasis_value m w v v hw S q

/-- The sum of exp(−w(p)/j) over the initial exponents of a finite-dimensional space of power
series is at most the sum of exp(−v_w(φ_i)/j) over any basis. -/
theorem sum_initialMonomialFinset_exp_le (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S] {N : ℕ}
    (Bc : Module.Basis (Fin N) K S) {j : ℝ} (hj : 0 < j) :
    ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m w v hw) S,
        Real.exp (-realExponentWeight w p / j) ≤
      ∑ i, Real.exp (-realWeightedOrder w (Bc i).val / j) := by
  classical
  let : Fintype (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) :=
    (initialIndexSet_finite _).fintype
  have hcard : Fintype.card (initialIndexSet
      (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) = N := by
    rw [← Module.finrank_eq_card_basis (weightedSubspaceInitialBasis m w v hw S),
      Module.finrank_eq_card_basis Bc, Fintype.card_fin]
  obtain ⟨e⟩ : Nonempty (initialIndexSet
      (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S) ≃ Fin N) :=
    ⟨Fintype.equivFinOfCardEq hcard⟩
  have hfun : (fun i => w i + 0 * (v i : ℝ) + 0 ^ 2 * (v i : ℝ)) = w := by
    funext i
    simp
  have hPV : ∀ φ : S, φ.val ≠ 0 →
      powerSeriesPerturbedValue m w v v hw φ.val 0 = realWeightedOrder w φ.val := by
    intro φ hφ
    rw [powerSeriesPerturbedValue_eq_realWeightedOrder m w v v hw hφ (le_refl (0 : ℝ)), hfun]
  have h := weightedSubspaceInitialBasis_exponential_optimal m w v v hw S (Bc.reindex e.symm) hj
  have hre : ∀ q, (Bc.reindex e.symm) q = Bc (e q) := fun q => by
    rw [Module.Basis.reindex_apply]
    rfl
  simp only [hre, weightedSubspaceInitialBasis_value] at h
  rw [Equiv.sum_comp e (fun i => Real.exp (-powerSeriesPerturbedValue m w v v hw (Bc i).val 0 /
    j))] at h
  rw [← sum_initialMonomialFinset (weightedMonomialOrder m w v hw) S
    (fun p => Real.exp (-realExponentWeight w p / j))]
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [hPV (Bc i) (fun h0 => Bc.ne_zero i (Subtype.ext h0))]

end Algebra

section Values

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- The values of a weight on the members of the family are the real weighted orders, for the
weights induced on the coordinates, of the Taylor expansions of the sections whose pulled back zero
divisors are supported on the family. -/
theorem cartierPullbackTaylor_realWeightedOrder_coordinateWeights {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c : EtaleChart K X n) (σc : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σc) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (hsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (t : X) = 0)
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a) :
    realWeightedOrder (sncChartCoordinateWeights σc w) (cartierPullbackTaylor D π z ez s) =
      ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D s hs)) (ξ k) : ℝ) := by
  have h := cartierPullbackRealValuation_eq_sum_of_supported π ξ hinj hξ hsnc c σc hc z hz ez
    hez D s hs hsupp (sncChartCoordinateWeights σc w) (sncChartCoordinateWeights_nonneg σc hw0)
  unfold cartierPullbackRealValuation at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases hσ : σc k with
  | none =>
    have hk : w k = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := hwσ k hne
      rw [hσ] at ha
      cases ha
    simp [hk]
  | some a => rw [Option.elim_some, sncChartCoordinateWeights_of_some hc.1 w hσ, mul_comm]

/-- The sum over the initial exponents at z of the sections of D is at most the objective of the
weight for a basis whose pulled back zero divisors are supported on the family. -/
theorem sum_initialExponents_le_sncWeight_objective [π.IsOver (Spec (CommRingCat.of K))]
    {r N : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) [FiniteDimensional K Γ(D.sheaf, ⊤)]
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (t : X) = 0)
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a)
    (v : Fin n → ℕ) (m : MonomialOrder (Fin n)) (A t : ℝ) {j : ℝ} (hj : 0 < j) :
    ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
          (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear D π z ez)),
        Real.exp (A / t - realExponentWeight (sncChartCoordinateWeights σc w) p / j) ≤
      ∑ i, Real.exp (A / t - (∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnoeth : IsNoetherianRing (X.presheaf.stalk z) :=
    smoothScheme_stalk_isNoetherianRing (K := K) z
  have hTinj := cartierPullbackTaylorLinear_injective π z ez D
  have h := sum_initialMonomialFinset_exp_le m (sncChartCoordinateWeights σc w) v
    (sncChartCoordinateWeights_nonneg σc hw0)
    (LinearMap.range (cartierPullbackTaylorLinear D π z ez))
    (B.map (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D π z ez) hTinj)) hj
  have hsplit : ∀ x : ℝ, Real.exp (A / t - x / j) = Real.exp (A / t) * Real.exp (-x / j) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [hsplit]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
    (Real.exp_pos _).le
  have hTi : ((B.map (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D π z ez) hTinj))
      i).val = cartierPullbackTaylor D π z ez (B i) := rfl
  rw [hTi, cartierPullbackTaylor_realWeightedOrder_coordinateWeights π ξ hinj hξ hsnc c σc hc z hz
    ez hez D (B i) (B.ne_zero i) (hGsupp i) w hw0 hwσ]

end Values

section Infimum

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- A lower bound for the objective over the profile data at x of all bases of the sections of a
Cartier divisor D' is a lower bound for the sum over the initial exponents at z of the sections of
D', for the weight scaled by any lam > 0: the scaled weight is a monomial Taylor test for D'. -/
theorem le_sum_initialExponents_of_le_sncWeightProfiles {r N : ℕ} (cY : EtaleChart K Y n)
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
    (hj : 0 < j) {L : ℝ}
    (hL : ∀ B' : Module.Basis (Fin N) K Γ(D'.sheaf, ⊤),
      ∀ p' ∈ sncWeightProfiles cY fY d D₀ D' x B', L ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) :
    L ≤ ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
          (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)),
        Real.exp (lam * (∑ k, w k * (((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
          lam * realExponentWeight (sncChartCoordinateWeights σc w) p / j) := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnoeth : IsNoetherianRing (X.presheaf.stalk z) :=
    smoothScheme_stalk_isNoetherianRing (K := K) z
  have hwt0 := sncChartCoordinateWeights_nonneg σc hw0
  have hTinj := cartierPullbackTaylorLinear_injective π z ez D'
  obtain ⟨b, hb⟩ : ∃ b : Fin r → ℤ, (fun k => cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) = b := ⟨_, rfl⟩
  have hbk : ∀ k, cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k) = b k :=
    fun k => congrFun hb k
  simp only [hbk]
  -- every member of positive weight is cut out by a coordinate vanishing at y
  have hmemσ : ∀ k, y ∈ closure ({ξ k} : Set X) → ∃ a, σc k = some a := by
    intro k hyk
    cases hσ : σc k with
    | none =>
      exfalso
      have hmem : y ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hyk, hy⟩
      rw [hc.2 k, hσ] at hmem
      exact hmem
    | some a => exact ⟨a, rfl⟩
  have hwσ : ∀ k, w k ≠ 0 → ∃ a, σc k = some a := fun k hk => hmemσ k (hwy k hk)
  have hnu : ∀ a, (lam • sncChartCoordinateWeights σc w) a ≠ 0 →
      ¬ IsUnit (X.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a))) := by
    intro a ha hunit
    have hwa : sncChartCoordinateWeights σc w a ≠ 0 := by
      intro h0
      apply ha
      rw [Pi.smul_apply, h0, smul_zero]
    obtain ⟨k, hka, hk⟩ : ∃ k, σc k = some a ∧ w k ≠ 0 := by
      by_contra hno
      apply hwa
      unfold sncChartCoordinateWeights
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hka : σc k = some a
      · rw [ite_eq_left hka]
        by_contra h0
        exact hno ⟨k, hka, h0⟩
      · rw [ite_eq_right hka]
    have hmem : y ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hwy k hk, hy⟩
    rw [hc.2 k, hka, Option.elim_some, Scheme.zeroLocus_singleton] at hmem
    exact hmem.1 ((X.mem_basicOpen _ y hy).mpr hunit)
  obtain ⟨k₀, hk₀⟩ : ∃ k, w k ≠ 0 := by
    by_contra h
    push Not at h
    exact hwne (funext h)
  obtain ⟨a₀, ha₀⟩ := hwσ k₀ hk₀
  have hu0 : ∀ a, 0 ≤ (lam • sncChartCoordinateWeights σc w) a := fun a => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hlam.le (hwt0 a)
  have hune : lam • sncChartCoordinateWeights σc w ≠ 0 := by
    intro h
    have h1 := congrFun h a₀
    rw [Pi.smul_apply, smul_eq_mul, sncChartCoordinateWeights_of_some hc.1 w ha₀,
      Pi.zero_apply] at h1
    exact hk₀ ((mul_eq_zero.mp h1).resolve_left hlam.ne')
  -- the basis adapted to the initial exponents, as a basis of sections
  let : Fintype (initialIndexSet (subspaceCoefficientMap
      (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v hwt0)
      (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)))) :=
    (initialIndexSet_finite _).fintype
  have hcard : Fintype.card (initialIndexSet (subspaceCoefficientMap
      (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v hwt0)
      (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)))) = N := by
    rw [← Module.finrank_eq_card_basis (weightedSubspaceInitialBasis m
      (sncChartCoordinateWeights σc w) v hwt0
      (LinearMap.range (cartierPullbackTaylorLinear D' π z ez))), ← hN]
    exact (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D' π z ez) hTinj).finrank_eq.symm
  obtain ⟨e⟩ : Nonempty (initialIndexSet (subspaceCoefficientMap
      (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v hwt0)
      (LinearMap.range (cartierPullbackTaylorLinear D' π z ez))) ≃ Fin N) :=
    ⟨Fintype.equivFinOfCardEq hcard⟩
  obtain ⟨B'', hB''⟩ : ∃ B'' : Module.Basis (Fin N) K Γ(D'.sheaf, ⊤),
      ∀ i, cartierPullbackTaylor D' π z ez (B'' i) = (weightedSubspaceInitialBasis m
        (sncChartCoordinateWeights σc w) v hwt0
        (LinearMap.range (cartierPullbackTaylorLinear D' π z ez)) (e.symm i)).val := by
    refine ⟨((weightedSubspaceInitialBasis m (sncChartCoordinateWeights σc w) v hwt0
      (LinearMap.range (cartierPullbackTaylorLinear D' π z ez))).reindex e).map
      (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D' π z ez) hTinj).symm, fun i => ?_⟩
    rw [Module.Basis.map_apply, Module.Basis.reindex_apply]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective (cartierPullbackTaylorLinear D' π z ez)
      hTinj).apply_symm_apply ((weightedSubspaceInitialBasis m (sncChartCoordinateWeights σc w)
        v hwt0 (LinearMap.range (cartierPullbackTaylorLinear D' π z ez))) (e.symm i)))
  have hcmp := le_taylorTest_objective_of_le_sncWeightProfiles π hπ cY fY d hd D₀ cX ξ hinj hξ
    hsnc hBsupp c σc hc y hy (lam • sncChartCoordinateWeights σc w) hu0 hune hnu x hx z hz hyz
    ez hez D' (⇑B'') (fun i => B''.ne_zero i) ht hj (hL B'')
  rw [hb, chartWeightLogDiscrepancy_smul,
    chartWeightLogDiscrepancy_coordinateWeights hc.1 d hd b hwσ] at hcmp
  refine hcmp.trans (le_of_eq ?_)
  rw [← sum_initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
      hwt0) (LinearMap.range (cartierPullbackTaylorLinear D' π z ez))
    (fun p => Real.exp (lam * (∑ k, w k * (((d : ℝ) - b k) / d)) / t -
      lam * realExponentWeight (sncChartCoordinateWeights σc w) p / j)),
    ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold cartierPullbackRealValuation
  rw [hB'' i, realWeightedOrder_smul hlam.le, realWeightedOrder_weightedSubspaceInitialBasis]

end Infimum

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightTaylorValues
public import MixedFujita.FirstVariation
public import MixedFujita.BasisOptimality

/-!
The tangential moment bound (16) of section 5.1 of the manuscript for a weight on a simple normal
crossing model (step 11).

Let π : X → Y be a model of the pair with a simple normal crossing family ξ supporting the crepant
boundary and the pulled back zero divisors of a basis B of the sections of D, w ≥ 0, w ≠ 0 a weight
on the members of the family, z a point of X through all the members of positive weight, with a
simple normal crossing chart and Taylor coordinates the coordinates of the chart. Let v and u be
natural weights on the coordinates of the chart which do not cut out members of the family (the
directions along the stratum: v the tangent directions of the image, u the fibre directions).

Hypothesis (the specialization comparison (6) combined with the minimality of the weight): the
objective Σ_i exp(A(w)/t − v_i(w)/j) of the weight for the basis B is at most the objective of
every profile datum at π(z) of every basis.

Conclusion: let Γ be the set of the initial exponents of the Taylor expansions at z of the
sections of D, for the order which compares first the old weight ℓ(p) = Σ_a w_a p_a, then the
degree |p|_v = Σ_a v_a p_a, then a fixed monomial order. Then

  Σ_{p ∈ Γ} |p|_v exp(−ℓ(p)/j) ≤ (j Σ_a v_a / t) Σ_{p ∈ Γ} exp(−ℓ(p)/j).

Proof: the valuation v_ε with weights w + ε v + ε² u on the coordinates is a monomial Taylor test
at z, so its objective for every basis is at least the infimum at π(z), hence at least the
objective of the weight; at ε = 0 the basis adapted to the initial exponents has objective at most
that of B, which is the objective of the weight because a weight is a Taylor test on its own
basis; the first variation at ε = 0 gives the inequality.

* Algebra: the perturbed value of a power series is the real weighted order for the perturbed
  weights; for a finite-dimensional space S of power series, a lower bound L for the perturbed
  objectives of all bases which is attained at ε = 0 by one basis gives the moment bound on the
  initial exponents of S.
* The weights on the coordinates induced by a weight on the members have the log discrepancy
  Σ_k w_k a_k of the weight; adding ε v + ε² u adds ε Σ v + ε² Σ u.
* The Taylor expansion at a point of a model of the pullback of a nonzero section is nonzero.
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

/-- For ε ≥ 0 the perturbed value of a nonzero power series is its real weighted order for the
weights w + ε v + ε² u. -/
theorem powerSeriesPerturbedValue_eq_realWeightedOrder (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) {φ : MvPowerSeries σ K} (hφ : φ ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) :
    powerSeriesPerturbedValue m w v u hw φ ε =
      realWeightedOrder (fun i => w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ)) φ := by
  obtain ⟨q, hq, hval, hmin⟩ := powerSeriesPerturbedValue_spec m w v u hw hφ hε
  have hW : ∀ i, 0 ≤ w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ) := fun i => by
    have := hw i
    positivity
  have hcost : ∀ a : σ →₀ ℕ, perturbedExponentCost w v u ε a =
      ∑ i, (w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ)) * (a i : ℝ) := fun a => by
    rw [perturbedExponentCost_eq_realWeight]
    rfl
  rw [hval, hcost]
  apply le_antisymm
  · obtain ⟨β, hβ, heq⟩ := exists_coeff_realWeightedOrder
      (fun i => w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ)) hφ
    have h := hmin β hβ
    rw [hcost q, hcost β] at h
    exact h.trans heq.le
  · exact realWeightedOrder_le hW hφ hq

omit [Fintype σ] in
/-- A sum over the initial exponents of a finite-dimensional space of power series as a sum over
its initial indices. -/
theorem sum_initialMonomialFinset (m : MonomialOrder σ) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S] [Fintype (initialIndexSet (subspaceCoefficientMap m S))]
    (g : (σ →₀ ℕ) → ℝ) :
    ∑ q : initialIndexSet (subspaceCoefficientMap m S), g (m.toSyn.symm q.val) =
      ∑ p ∈ initialMonomialFinset m S, g p := by
  refine Finset.sum_bij (fun q _ => m.toSyn.symm q.val) (fun q _ => ?_) (fun q _ q' _ h => ?_)
    (fun p hp => ?_) (fun q _ => rfl)
  · obtain ⟨φ, hφ⟩ := q.property
    exact (mem_initialMonomialFinset m S _).mpr ⟨φ.val, φ.property,
      (initialMonomial_iff_initialCoefficient m φ.val _).mpr (by
        rw [m.toSyn.apply_symm_apply]
        exact hφ)⟩
  · exact Subtype.ext (m.toSyn.symm.injective h)
  · obtain ⟨φ, hφ, hp'⟩ := (mem_initialMonomialFinset m S p).mp hp
    exact ⟨⟨m.toSyn p, ⟨⟨φ, hφ⟩, (initialMonomial_iff_initialCoefficient m φ p).mp hp'⟩⟩,
      Finset.mem_univ _, m.toSyn.symm_apply_apply p⟩

/-- The moment bound from a lower bound for the perturbed objectives of all bases. Let S be a
finite-dimensional space of power series with a basis of N elements and L a number such that the
objective at ε = 0 of one basis is at most L and the objective at every ε > 0 of every basis is at
least L. Then the initial exponents of S, for the order comparing first the weight w, then the
degree v, satisfy Σ |p|_v exp(−w(p)/j) ≤ (j d / t) Σ exp(−w(p)/j), where d is the linear
coefficient of the log discrepancy. -/
theorem tangential_moment_le_of_basis_lower_bound (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S] {N : ℕ} (hN : 0 < N) (Bc : Module.Basis (Fin N) K S)
    (A d c t j : ℝ) (hj : 0 < j) {L : ℝ}
    (hL0 : ∑ i, Real.exp (A / t - powerSeriesPerturbedValue m w v u hw (Bc i).val 0 / j) ≤ L)
    (hLε : ∀ ε : ℝ, 0 < ε → ∀ B' : Module.Basis (Fin N) K S,
      L ≤ ∑ i, Real.exp ((A + d * ε + c * ε ^ 2) / t -
        powerSeriesPerturbedValue m w v u hw (B' i).val ε / j)) :
    sectionExponentialMoment (initialMonomialFinset (weightedMonomialOrder m w v hw) S)
      (fun p => realExponentWeight w p) (fun p => (natExponentDegree v p : ℝ)) j ≤ d / t := by
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
  have hne : (Finset.univ : Finset (initialIndexSet
      (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S))).Nonempty :=
    ⟨e.symm ⟨0, hN⟩, Finset.mem_univ _⟩
  have hmom := powerSeries_tangential_moment_upper_bound Finset.univ hne m w v u hw
    (fun p => (weightedSubspaceInitialBasis m w v hw S p).val)
    (fun p => (weightedMonomialOrder m w v hw).toSyn.symm p.val)
    (fun p _ => weightedSubspaceInitialBasis_spec m w v hw S p) A d c t j hj ?_
  · have e1 := sum_initialMonomialFinset (weightedMonomialOrder m w v hw) S
      (fun p => (natExponentDegree v p : ℝ) * Real.exp (-realExponentWeight w p / j))
    have e2 := sum_initialMonomialFinset (weightedMonomialOrder m w v hw) S
      (fun p => Real.exp (-realExponentWeight w p / j))
    unfold sectionExponentialMoment sectionExponentialWeightSum at hmom ⊢
    beta_reduce at hmom ⊢
    rw [← e1, ← e2]
    exact hmom
  · refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    have hε' : (0 : ℝ) < ε := hε
    have hcardpos : (0 : ℝ) < ((Finset.univ : Finset (initialIndexSet
        (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S))).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    -- at ε = 0 the adapted basis is optimal
    refine (weightedSubspaceInitialBasis_objective_optimal m w v u hw S (Bc.reindex e.symm)
      (fun η => A + d * η + c * η ^ 2) t hj).trans ?_
    unfold sectionExponentialObjective
    refine div_le_div_of_nonneg_right ?_ hcardpos.le
    have h1 : ∑ q : initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S),
        Real.exp ((A + d * 0 + c * 0 ^ 2) / t -
          powerSeriesPerturbedValue m w v u hw ((Bc.reindex e.symm) q).val 0 / j) ≤ L := by
      have hre : ∀ q, (Bc.reindex e.symm) q = Bc (e q) := fun q => by
        rw [Module.Basis.reindex_apply]
        rfl
      simp only [hre, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero]
      rw [Equiv.sum_comp e (fun i => Real.exp (A / t -
        powerSeriesPerturbedValue m w v u hw (Bc i).val 0 / j))]
      exact hL0
    have h2 : L ≤ ∑ q : initialIndexSet
        (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S),
        Real.exp ((A + d * ε + c * ε ^ 2) / t - powerSeriesPerturbedValue m w v u hw
          (weightedSubspaceInitialBasis m w v hw S q).val ε / j) := by
      have h := hLε ε hε' ((weightedSubspaceInitialBasis m w v hw S).reindex e)
      simp only [Module.Basis.reindex_apply] at h
      rw [Equiv.sum_comp e.symm (fun q => Real.exp ((A + d * ε + c * ε ^ 2) / t -
        powerSeriesPerturbedValue m w v u hw
          (weightedSubspaceInitialBasis m w v hw S q).val ε / j))] at h
      exact h
    exact h1.trans h2

end Algebra

section Weights

variable {n r : ℕ}

/-- The weights on the coordinates of a simple normal crossing chart induced by weights on the
members of the family: the coordinate cutting out a member carries the weight of the member, the
other coordinates the weight zero. -/
noncomputable def sncChartCoordinateWeights (σc : Fin r → Option (Fin n)) (w : Fin r → ℝ) :
    Fin n → ℝ := fun a => ∑ k, if σc k = some a then w k else 0

theorem sncChartCoordinateWeights_nonneg (σc : Fin r → Option (Fin n)) {w : Fin r → ℝ}
    (hw : ∀ k, 0 ≤ w k) (a : Fin n) : 0 ≤ sncChartCoordinateWeights σc w a :=
  Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact hw k
    · exact le_rfl

theorem sncChartCoordinateWeights_of_some {σc : Fin r → Option (Fin n)}
    (hinj : ∀ i j a, σc i = some a → σc j = some a → i = j) (w : Fin r → ℝ) {k : Fin r}
    {a : Fin n} (h : σc k = some a) : sncChartCoordinateWeights σc w a = w k := by
  unfold sncChartCoordinateWeights
  rw [Finset.sum_eq_single k (fun k' _ hne => ite_eq_right fun h' => hne (hinj k' k a h' h))
    (fun hk => absurd (Finset.mem_univ k) hk), ite_eq_left h]

theorem sum_sncChartCoordinateWeights {σc : Fin r → Option (Fin n)} {w : Fin r → ℝ}
    (hw : ∀ k, w k ≠ 0 → ∃ a, σc k = some a) :
    ∑ a, sncChartCoordinateWeights σc w a = ∑ k, w k := by
  unfold sncChartCoordinateWeights
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases hσ : σc k with
  | none =>
    have hk : w k = 0 := by
      by_contra h
      obtain ⟨a, ha⟩ := hw k h
      rw [hσ] at ha
      cases ha
    simp [hk]
  | some a₀ =>
    rw [Finset.sum_eq_single a₀
      (fun a _ hne => ite_eq_right fun h' => hne (Option.some.inj h').symm)
      (fun h => absurd (Finset.mem_univ a₀) h), ite_eq_left rfl]

/-- The log discrepancy of the weights induced on the coordinates is the log discrepancy
Σ_k w_k (d − b_k)/d of the weight on the members, when every member of positive weight is cut out
by a coordinate of the chart. -/
theorem chartWeightLogDiscrepancy_coordinateWeights {σc : Fin r → Option (Fin n)}
    (hinj : ∀ i j a, σc i = some a → σc j = some a → i = j) (d : ℕ) (hd : 1 ≤ d)
    (b : Fin r → ℤ) {w : Fin r → ℝ} (hw : ∀ k, w k ≠ 0 → ∃ a, σc k = some a) :
    chartWeightLogDiscrepancy σc d b (sncChartCoordinateWeights σc w) =
      ∑ k, w k * (((d : ℝ) - b k) / d) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have helim : ∀ k, (σc k).elim 0 (sncChartCoordinateWeights σc w) = w k := by
    intro k
    cases hσ : σc k with
    | none =>
      have hk : w k = 0 := by
        by_contra h
        obtain ⟨a, ha⟩ := hw k h
        rw [hσ] at ha
        cases ha
      simp [hk]
    | some a => simpa using sncChartCoordinateWeights_of_some hinj w hσ
  unfold chartWeightLogDiscrepancy
  rw [sum_sncChartCoordinateWeights hw, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [helim k]
  field_simp

/-- Adding weights ε v + ε² u on coordinates which do not cut out members of the family adds
ε Σ v + ε² Σ u to the log discrepancy. -/
theorem chartWeightLogDiscrepancy_perturbed (σc : Fin r → Option (Fin n)) (d : ℕ)
    (b : Fin r → ℤ) (w : Fin n → ℝ) (v u : Fin n → ℕ) (hv : ∀ k a, σc k = some a → v a = 0)
    (hu : ∀ k a, σc k = some a → u a = 0) (ε : ℝ) :
    chartWeightLogDiscrepancy σc d b (fun a => w a + ε * (v a : ℝ) + ε ^ 2 * (u a : ℝ)) =
      chartWeightLogDiscrepancy σc d b w + (∑ a, (v a : ℝ)) * ε + (∑ a, (u a : ℝ)) * ε ^ 2 := by
  have helim : ∀ k, (σc k).elim 0 (fun a => w a + ε * (v a : ℝ) + ε ^ 2 * (u a : ℝ)) =
      (σc k).elim 0 w := by
    intro k
    cases hσ : σc k with
    | none => rfl
    | some a => simp [hv k a hσ, hu k a hσ]
  unfold chartWeightLogDiscrepancy
  simp only [helim, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Weights

section Taylor

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- The Taylor expansion at a point of a model of the pullback of a nonzero section is nonzero. -/
theorem cartierPullbackTaylor_ne_zero (z : X) [IsNoetherianRing (X.presheaf.stalk z)]
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (D : CartierDivisor Y) {s : Γ(D.sheaf, ⊤)} (hs : s ≠ 0) :
    cartierPullbackTaylor D π z ez s ≠ 0 := by
  obtain ⟨f, hf, hfdef⟩ : ∃ (f : Y.functionFieldˣ) (hf : D.IsLocalEquationAt (π z) f),
      cartierPullbackTaylor D π z ez s =
        stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient D π z f hf s) :=
    ⟨Classical.choose (D.exists_isLocalEquationAt (π z)),
      Classical.choose_spec (D.exists_isLocalEquationAt (π z)), rfl⟩
  have himg : algebraMap (Y.presheaf.stalk (π z)) Y.functionField
      (cartierLocalCoefficient D (π z) f hf s) =
      ((f * cartierSectionUnit D s hs : Y.functionFieldˣ) : Y.functionField) := by
    simpa only [Units.val_mul, cartierSectionUnit_val] using
      cartierLocalCoefficient_image D (π z) f hf s
  have hgimg : algebraMap (X.presheaf.stalk z) X.functionField
      (cartierStalkPullbackCoefficient D π z f hf s) =
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom
        (f * cartierSectionUnit D s hs) : X.functionFieldˣ) : X.functionField) := by
    rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap, himg]
    rfl
  have hne : cartierStalkPullbackCoefficient D π z f hf s ≠ 0 := by
    intro h0
    have h1 : algebraMap (X.presheaf.stalk z) X.functionField
        (cartierStalkPullbackCoefficient D π z f hf s) ≠ 0 := by
      rw [hgimg]
      exact Units.ne_zero _
    exact h1 (by rw [h0, map_zero])
  intro h0
  rw [hfdef] at h0
  apply hne
  have hall : ∀ k : ℕ, cartierStalkPullbackCoefficient D π z f hf s ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ k := by
    intro k
    refine (completionCoordinates_mem_maximalIdeal_pow_iff ez.toRingEquiv _ k).mp ?_
    change (k : ℕ∞) ≤ (stalkTaylorExpansion z ez
      (cartierStalkPullbackCoefficient D π z f hf s)).order
    rw [h0, MvPowerSeries.order_zero]
    exact le_top
  have hbot : (⨅ k : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ k) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hmem : cartierStalkPullbackCoefficient D π z f hf s ∈
      (⨅ k : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ k) := Ideal.mem_iInf.mpr hall
  rw [hbot] at hmem
  exact hmem

/-- The Taylor expansion at a point of a model of the pullbacks of the sections is injective. -/
theorem cartierPullbackTaylorLinear_injective [π.IsOver (Spec (CommRingCat.of K))] (z : X)
    [IsNoetherianRing (X.presheaf.stalk z)]
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (D : CartierDivisor Y) : Function.Injective (cartierPullbackTaylorLinear D π z ez) := by
  refine (injective_iff_map_eq_zero _).mpr fun s hs => ?_
  by_contra hne
  exact cartierPullbackTaylor_ne_zero π z ez D hne hs

end Taylor

section Moment

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- The tangential moment bound (16) for a weight on a simple normal crossing model: if the
objective of the weight w for the basis B is at most the objective of every profile datum at π(z)
of every basis, then the initial exponents at z of the sections, for the order comparing first the
weight of w, then the degree in the directions v, satisfy
Σ |p|_v exp(−ℓ(p)/j) ≤ (j Σ v / t) Σ exp(−ℓ(p)/j). -/
theorem sncWeight_tangential_moment_le {r N : ℕ} (cY : EtaleChart K Y n)
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
    (hspec : ∀ B' : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∀ p' ∈ sncWeightProfiles cY fY d D₀ D (π z) B',
        (∑ i, Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) / t -
          (∑ k, w k * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j)) ≤
          ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) :
    sectionExponentialMoment
      (initialMonomialFinset (weightedMonomialOrder m (sncChartCoordinateWeights σc w) v
          (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierPullbackTaylorLinear D π z ez)))
      (fun p => realExponentWeight (sncChartCoordinateWeights σc w) p)
      (fun p => (natExponentDegree v p : ℝ)) j ≤ (∑ a, (v a : ℝ)) / t := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnoeth : IsNoetherianRing (X.presheaf.stalk z) :=
    smoothScheme_stalk_isNoetherianRing (K := K) z
  have hwt0 := sncChartCoordinateWeights_nonneg σc hw0
  have hTinj := cartierPullbackTaylorLinear_injective π z ez D
  obtain ⟨b, hb⟩ : ∃ b : Fin r → ℤ, (fun k => cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) = b := ⟨_, rfl⟩
  have hbk : ∀ k, cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k) = b k :=
    fun k => congrFun hb k
  simp only [hbk] at hspec
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = ∑ i, Real.exp ((∑ k, w k * (((d : ℝ) - b k) / d)) / t -
      (∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j) := ⟨_, rfl⟩
  have hA := chartWeightLogDiscrepancy_coordinateWeights hc.1 d hd b hwσ
  have hwzero : ∀ k, σc k = none → w k = 0 := by
    intro k hσ
    by_contra h
    obtain ⟨a, ha⟩ := hwσ k h
    rw [hσ] at ha
    cases ha
  -- the values of the weight on its basis are Taylor values
  have hvalB : ∀ i, realWeightedOrder (sncChartCoordinateWeights σc w)
      (cartierPullbackTaylor D π z ez (B i)) =
      ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ) := by
    intro i
    have h := cartierPullbackRealValuation_eq_sum_of_supported π ξ hinj hξ hsnc c σc hc z hz ez
      hez D (B i) (B.ne_zero i) (hGsupp i) (sncChartCoordinateWeights σc w) hwt0
    unfold cartierPullbackRealValuation at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    cases hσ : σc k with
    | none => simp [hwzero k hσ]
    | some a => rw [Option.elim_some, sncChartCoordinateWeights_of_some hc.1 w hσ, mul_comm]
  -- the coordinates of the chart vanish at z
  have hnu : ∀ a, ¬ IsUnit (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a))) := by
    intro a hunit
    have h1 := hunit.map (stalkTaylorExpansion z ez)
    have h2 : stalkTaylorExpansion z ez
        (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a))) = MvPowerSeries.X a := hez a
    rw [h2] at h1
    have h3 := MvPowerSeries.isUnit_iff_constantCoeff.mp h1
    rw [MvPowerSeries.constantCoeff_X] at h3
    exact not_isUnit_zero h3
  obtain ⟨k₀, hk₀⟩ : ∃ k, w k ≠ 0 := by
    by_contra h
    push Not at h
    exact hwne (funext h)
  obtain ⟨a₀, ha₀⟩ := hwσ k₀ hk₀
  have hwta₀ : 0 < sncChartCoordinateWeights σc w a₀ := by
    rw [sncChartCoordinateWeights_of_some hc.1 w ha₀]
    exact lt_of_le_of_ne (hw0 k₀) (Ne.symm hk₀)
  refine tangential_moment_le_of_basis_lower_bound m (sncChartCoordinateWeights σc w) v u hwt0
    (LinearMap.range (cartierPullbackTaylorLinear D π z ez)) hN
    (B.map (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D π z ez) hTinj))
    (chartWeightLogDiscrepancy σc d b (sncChartCoordinateWeights σc w)) (∑ a, (v a : ℝ))
    (∑ a, (u a : ℝ)) t j hj (L := L) ?_ ?_
  · -- at ε = 0 the basis B has the objective of the weight
    rw [hL, hA]
    refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    have hTi : ((B.map (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D π z ez) hTinj))
        i).val = cartierPullbackTaylor D π z ez (B i) := rfl
    have hfun : (fun a => sncChartCoordinateWeights σc w a + 0 * (v a : ℝ) +
        0 ^ 2 * (u a : ℝ)) = sncChartCoordinateWeights σc w := by
      funext a
      simp
    rw [hTi, powerSeriesPerturbedValue_eq_realWeightedOrder m _ v u hwt0
      (cartierPullbackTaylor_ne_zero π z ez D (B.ne_zero i)) le_rfl, hfun, hvalB i]
  · -- for ε > 0 every basis is bounded below by the infimum at π(z)
    intro ε hε B'
    obtain ⟨B'', hB''⟩ : ∃ B'' : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        ∀ i, cartierPullbackTaylor D π z ez (B'' i) = (B' i).val := by
      refine ⟨B'.map (LinearEquiv.ofInjective (cartierPullbackTaylorLinear D π z ez)
        hTinj).symm, fun i => ?_⟩
      exact congrArg Subtype.val ((LinearEquiv.ofInjective
        (cartierPullbackTaylorLinear D π z ez) hTinj).apply_symm_apply (B' i))
    have huε0 : ∀ a, 0 ≤ sncChartCoordinateWeights σc w a + ε * (v a : ℝ) +
        ε ^ 2 * (u a : ℝ) := fun a => by
      have := hwt0 a
      positivity
    have huεne : (fun a => sncChartCoordinateWeights σc w a + ε * (v a : ℝ) +
        ε ^ 2 * (u a : ℝ)) ≠ 0 := by
      intro h
      have h1 := congrFun h a₀
      have h3 : 0 ≤ ε * (v a₀ : ℝ) + ε ^ 2 * (u a₀ : ℝ) := by positivity
      simp only [Pi.zero_apply] at h1
      linarith
    have hcmp := le_taylorTest_objective_of_le_sncWeightProfiles π hπ cY fY d hd D₀ cX ξ hinj hξ
      hsnc hBsupp c σc hc z hz _ huε0 huεne (fun a _ => hnu a) (π z) specializes_rfl z hz
      specializes_rfl ez hez D (⇑B'') (fun i => B''.ne_zero i) ht hj (L := L) (by
        intro p' hp'
        rw [hL]
        exact hspec B'' p' hp')
    rw [hb, chartWeightLogDiscrepancy_perturbed σc d b (sncChartCoordinateWeights σc w) v u hv hu
      ε] at hcmp
    refine hcmp.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    unfold cartierPullbackRealValuation
    rw [hB'' i, powerSeriesPerturbedValue_eq_realWeightedOrder m _ v u hwt0
      (fun h0 => B'.ne_zero i (Subtype.ext h0)) hε.le]

end Moment

end MixedFujita

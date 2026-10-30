/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightLowSubspace
public import MixedFujita.BasisAttainmentAbstract
public import MixedFujita.RealWeightedMinimization

/-!
Realized profiles and profile data of the weights (step 11, sections 2.2 and 3.2 of the
manuscript, in the form of tuples of sections instead of flags).

Fix a pair on Y (chart, form, denominator d, divisor D₀), a Cartier divisor D of Y and a point x.

* A tuple s_1, …, s_N of sections of D realizes the normalized profile α at x when some prime
  divisor e of a smooth birational test model of Y whose centre contains x has positive log
  discrepancy A(e) and ord_e(σ* div s_i) ≥ α_i A(e) for the nonzero s_i (condition (4) of the
  manuscript; a zero section has value ∞). Realization is decreasing in α.
* The profile data of a tuple of nonzero sections: the pairs (A(w), (v_i(w))_i) of the weights
  w ≥ 0 over the fibre of x on the proper simple normal crossing models of the pair and of the
  zero divisors of the sections. They are stable under scaling.
* The closedness statement (the content of Lemma 3 of the manuscript for these families, at the
  fixed point x): for every finite family b of sections and every nonnegative rational profile α,
  the coefficient matrices c for which the tuple (Σ_k c_ik b_k)_i realizes α form the zero set of
  an ideal of polynomials. It is a definition, used as a hypothesis; it is not proved here.
* Retraction in the form of data: on a proper simple normal crossing model, a prime divisor of a
  test model whose centre contains x gives a weight over the fibre of x with the same values on
  the divisors supported on the family and with log discrepancy at most that of the prime divisor.
* From weights to realization: a profile datum (a, v) with a > 0 realizes every profile α ≥ 0
  with α_i = 0 or α_i a < v_i (a nearby rational weight with the same support is a multiple of a
  prime divisor).
* From realization to weights: on a klt pair, if the tuple realizes profiles α_l ≥ 0 converging to
  q with some q_i > 0, then some weight over the fibre of x on any given proper simple normal
  crossing model has A = 1 and v_i ≥ q_i (normalized retractions lie in a compact set).
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

section Definitions

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The tuple s realizes the normalized profile α at x: some prime divisor e of a smooth birational
test model whose centre contains x has positive log discrepancy and ord_e(σ* div s_i) ≥ α_i A(e)
for the nonzero s_i. -/
def IsRealizedProfile (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (α : Fin N → ℝ) :
    Prop :=
  ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
    (_ : U.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
    (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
    x ∈ closure ({σ (e : U)} : Set Y) ∧
    0 < ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d ∧
    ∀ i (hs : s i ≠ 0), α i * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) ≤
      (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) hs)) (e : U) : ℝ)

/-- The profile data (A(w), (v_i(w))_i) of the weights over the fibre of x on the proper simple
normal crossing models of the pair and of the zero divisors of a tuple of nonzero sections. -/
def sncWeightProfiles (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) :
    Set (ℝ × (Fin N → ℝ)) :=
  {p | ∃ (hs : ∀ i, s i ≠ 0) (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsLocallyNoetherian X)
      (_ : X.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K)))
      (π : X ⟶ Y) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K))) (_ : IsProper π)
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
      (r : ℕ) (ξ : Fin r → X) (w : Fin r → ℝ),
      Function.Injective ξ ∧ (∀ k, Order.coheight (ξ k) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
          (z : X) = 0) ∧
      (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
          (z : X) = 0) ∧
      (∀ k, 0 ≤ w k) ∧
      (∃ y ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) ∧
      p.1 = ∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) ∧
      ∀ i, p.2 i = ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)}

/-- The closedness statement for the realization sets at the point x (Lemma 3 of the manuscript
for the families of tuples of sections of D): for every finite family b of sections and every
nonnegative rational profile α, the coefficient matrices of the tuples in the span of b which
realize α form the zero set of an ideal of polynomials. -/
def RealizationSetsZariskiClosed (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) : Prop :=
  ∀ (N m : ℕ) (b : Fin m → Γ(D.sheaf, ⊤)) (α : Fin N → ℚ), (∀ i, 0 ≤ α i) →
    ∃ I : Ideal (MvPolynomial (Fin N × Fin m) K),
      {c : Fin N × Fin m → K | IsRealizedProfile cY fY d D₀ D x
        (fun i => ∑ k, c (i, k) • b k) (fun i => (α i : ℝ))} = polynomialZeroSet I

/-- Realization is decreasing in the profile. -/
theorem isRealizedProfile_antitone (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) {α α' : Fin N → ℝ}
    (hα : ∀ i, α i ≤ α' i) (h : IsRealizedProfile cY fY d D₀ D x s α') :
    IsRealizedProfile cY fY d D₀ D x s α := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, hval⟩ := h
  exact ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, fun i hs =>
    (mul_le_mul_of_nonneg_right (hα i) hpos.le).trans (hval i hs)⟩

/-- The profile data are stable under scaling. -/
theorem sncWeightProfiles_smul (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D x s) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    (lam * p.1, fun i => lam * p.2 i) ∈ sncWeightProfiles cY fY d D₀ D x s := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y, hy, hwy⟩, hA, hv⟩ := hp
  refine ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, fun k => lam * w k, hinj, hξ,
    hsnc, hBsupp, hGsupp, fun k => mul_nonneg hlam (hw0 k), ⟨y, hy, fun k hk => hwy k ?_⟩, ?_,
    fun i => ?_⟩
  · intro h0
    exact hk (by change lam * w k = 0; rw [h0, mul_zero])
  · change lam * p.1 = _
    rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  · change lam * p.2 i = _
    rw [hv i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

end Definitions

section Retraction

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Retraction in the form of data: a prime divisor of a smooth birational test model of the base
whose centre contains x gives a weight over π⁻¹(x) on the simple normal crossing family with the
same values on the divisors whose pullbacks are supported on the family and with log discrepancy
at most that of the prime divisor. -/
theorem exists_sncWeight_data_of_test_prime {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (G : Fin N → CartierDivisor Y)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (G i)) (z : X) = 0)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (x : Y)
    (hx : x ∈ closure ({σ (e : U)} : Set Y)) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      (∀ i, ∑ k, w k * (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) =
        (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ)) ∧
      ∑ k, w k * (((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) ≤
        ((d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d := by
  obtain ⟨o, t₀, ht₀, ho, hosupp, hpull, -, hdisc⟩ := exists_snc_orders_at_test_prime π hπ cY fY d
    D₀ cX ξ hinj hξ hsnc hBsupp (fun _ : PUnit.{1} => (0 : CartierDivisor Y))
    (fun _ => CartierDivisor.isEffective_zero) (cartierPullback π 0)
    (cartierPullback_isEffective π 0 CartierDivisor.isEffective_zero)
    (fun t _ => by rw [cartierPullback_zero, cartierCoefficient_zero])
    (by
      rw [effectiveCartierIdealSheaf_cartierPullback π 0 CartierDivisor.isEffective_zero]
      exact congrArg (fun I : Y.IdealSheafData => I.comap π) (iSup_const (ι := PUnit.{1})).symm)
    σ hσ cU e
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hclosed : IsClosed (π '' closure ({t₀} : Set X)) :=
    (Scheme.Hom.isClosedMap π) _ isClosed_closure
  have hxim : x ∈ π '' closure ({t₀} : Set X) := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hclosed hx
    exact ⟨t₀, subset_closure rfl, ht₀⟩
  obtain ⟨p, hpcl, hpx⟩ := hxim
  refine ⟨fun k => (o k : ℝ), fun k => ?_, ⟨p, hpx, fun k hk => ?_⟩, fun i => ?_, ?_⟩
  · change (0 : ℝ) ≤ ((o k : ℤ) : ℝ)
    exact_mod_cast ho k
  · have hok : o k ≠ 0 := fun h => hk (by
      change ((o k : ℤ) : ℝ) = 0
      rw [h, Int.cast_zero])
    exact closure_minimal (Set.singleton_subset_iff.mpr (hosupp k hok)) isClosed_closure hpcl
  · change ∑ k, ((o k : ℤ) : ℝ) * (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) = _
    rw [hpull (G i) (hGsupp i)]
    push_cast
    exact Finset.sum_congr rfl fun k _ => by ring
  · change ∑ k, ((o k : ℤ) : ℝ) * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) ≤ _
    have hR : (d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k) : ℝ) * (o k : ℝ) ≤
        (d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U) := by
      exact_mod_cast hdisc
    have hA : ∑ k, (o k : ℝ) * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) =
        ((d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k) : ℝ) *
            (o k : ℝ)) / d := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hA]
    exact div_le_div_of_nonneg_right hR hdpos.le

omit [IsProper π] in
/-- From weights to realization: on a simple normal crossing model of the pair and of the zero
divisors of nonzero sections, a weight w ≥ 0 over π⁻¹(x) with A(w) > 0 realizes every profile α
such that α_i = 0 or α_i A(w) < v_i(w) for every i. -/
theorem isRealizedProfile_of_sncWeight {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0)
    (x : Y) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hwΦ : ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    (hApos : 0 < ∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d))
    {α : Fin N → ℝ}
    (hα : ∀ i, α i = 0 ∨ α i * (∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) <
      ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) :
    IsRealizedProfile cY fY d D₀ D x s α := by
  classical
  obtain ⟨p, hpx, hwp⟩ := hwΦ
  set a : Fin r → ℝ := fun k => ((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d with ha
  set ev : Fin N → Fin r → ℝ := fun i k => (cartierCoefficient (cartierPullback π
    (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) with hev
  -- the conditions are open in the weight
  have hopen : IsOpen ({w' : Fin r → ℝ | 0 < ∑ k, w' k * a k} ∩
      ⋂ i, {w' : Fin r → ℝ | α i = 0 ∨ α i * (∑ k, w' k * a k) < ∑ k, w' k * ev i k}) := by
    refine (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_iInter_of_finite fun i => ?_)
    by_cases hi : α i = 0
    · simp only [hi, true_or, Set.ofPred_true]
      exact isOpen_univ
    · simp only [hi, false_or]
      exact isOpen_lt (by fun_prop) (by fun_prop)
  have hwmem : w ∈ ({w' : Fin r → ℝ | 0 < ∑ k, w' k * a k} ∩
      ⋂ i, {w' : Fin r → ℝ | α i = 0 ∨ α i * (∑ k, w' k * a k) < ∑ k, w' k * ev i k}) :=
    ⟨hApos, Set.mem_iInter.mpr hα⟩
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen w hwmem
  obtain ⟨M, W, hM, hdist, hsupp⟩ := exists_natural_weight_approximation w hw0 hη
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨hWA, hWα⟩ := hball (Metric.mem_ball.mpr hdist)
  have hWα' := Set.mem_iInter.mp hWα
  -- sums for the rational weight
  have e1 : ∀ c : Fin r → ℝ, ∑ k, (W k : ℝ) / M * c k = (∑ k, c k * (W k : ℝ)) / M := by
    intro c
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hWA' : 0 < ∑ k, a k * (W k : ℝ) := by
    have h : 0 < (∑ k, a k * (W k : ℝ)) / M := by
      rw [← e1 a]
      exact hWA
    exact (div_pos_iff_of_pos_right hMpos).mp h
  have hW : W ≠ 0 := by
    rintro rfl
    simp at hWA'
  have hWy : ∀ k, W k ≠ 0 → p ∈ closure ({ξ k} : Set X) := fun k hk =>
    hwp k fun h0 => hk ((hsupp k).mpr h0)
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, hg, hcl, hpull, hdisc⟩ :=
    exists_base_test_prime_of_natural_weights π hπ cY fY d D₀ cX ξ hinj hξ hsnc hBsupp p W hW hWy
  have hpx' : π p = x := hpx
  rw [hpx'] at hcl
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hA : (g : ℝ) * (((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) =
      ∑ k, a k * (W k : ℝ) := by
    have h : (g : ℝ) * ((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) =
        ∑ k, ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) * (W k : ℝ) := by
      exact_mod_cast hdisc
    rw [mul_div_assoc', h, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha]
    field_simp
  have hv : ∀ i, (g : ℝ) * (cartierCoefficient (cartierPullback σ
      (cartierSectionZeroDivisor D (s i) (hs i))) (e : U) : ℝ) = ∑ k, ev i k * (W k : ℝ) := by
    intro i
    have h : (g : ℝ) * (cartierCoefficient (cartierPullback σ
        (cartierSectionZeroDivisor D (s i) (hs i))) (e : U) : ℝ) =
        ∑ k, (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) * (W k : ℝ) := by
      exact_mod_cast hpull _ (hGsupp i)
    exact h
  have hAe : 0 < ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d := by
    have h : 0 < (g : ℝ) * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) := by
      rw [hA]
      exact hWA'
    exact (pos_iff_pos_of_mul_pos h).mp hgpos
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hAe, fun i hsi => ?_⟩
  -- multiply by g
  refine le_of_mul_le_mul_left ?_ hgpos
  have hvi : (g : ℝ) * (cartierCoefficient (cartierPullback σ
      (cartierSectionZeroDivisor D (s i) hsi)) (e : U) : ℝ) = ∑ k, ev i k * (W k : ℝ) := hv i
  rw [hvi]
  calc (g : ℝ) * (α i * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d))
      = α i * ((g : ℝ) * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d)) := by ring
    _ = α i * ∑ k, a k * (W k : ℝ) := by rw [hA]
    _ ≤ ∑ k, ev i k * (W k : ℝ) := by
        rcases hWα' i with h0 | hlt
        · rw [h0, zero_mul]
          rw [← hvi]
          have hnn : (0 : ℝ) ≤ (cartierCoefficient (cartierPullback σ
              (cartierSectionZeroDivisor D (s i) hsi)) (e : U) : ℝ) := by
            exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
              (cartierPullback_isEffective σ _ (cartierSectionZeroDivisor_isEffective D (s i) hsi)) _
          exact mul_nonneg hgpos.le hnn
        · rw [e1 a, e1 (ev i), ← mul_div_assoc, div_lt_div_iff_of_pos_right hMpos] at hlt
          exact hlt.le

/-- From realization to a normalized weight: on a klt pair, a prime divisor realizing a profile
α ≥ 0 with some α_i > 0 retracts to a weight u ≥ 0 over π⁻¹(x) with A(u) = 1 and v_i(u) ≥ α_i. -/
theorem exists_normalized_sncWeight_of_isRealizedProfile {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0)
    (x : Y) {α : Fin N → ℝ} (hα0 : ∀ i, 0 ≤ α i) (hαpos : ∃ i, 0 < α i)
    (hreal : IsRealizedProfile cY fY d D₀ D x s α) :
    ∃ u : Fin r → ℝ, (∀ k, 0 ≤ u k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, u k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      ∑ k, u k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) = 1 ∧
      ∀ i, α i ≤ ∑ k, u k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hAe, hval⟩ := hreal
  obtain ⟨w, hw0, ⟨p, hpx, hwp⟩, hv, hA⟩ := exists_sncWeight_data_of_test_prime π hπ cY fY d hd D₀
    cX ξ hinj hξ hsnc hBsupp (fun i => cartierSectionZeroDivisor D (s i) (hs i)) hGsupp σ hσ cU e
    x hcl
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hapos : ∀ k, 0 < ((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d := fun k => by
    have hb : cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (ξ k) < (d : ℤ) :=
      logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
    have hb' : (cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (ξ k) : ℝ) < (d : ℝ) := by exact_mod_cast hb
    exact div_pos (by linarith) hdpos
  obtain ⟨i₁, hi₁⟩ := hαpos
  -- the weight is not zero
  have hvpos : 0 < ∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i₁) (hs i₁))) (ξ k) : ℝ) := by
    rw [hv i₁]
    exact lt_of_lt_of_le (mul_pos hi₁ hAe) (hval i₁ (hs i₁))
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hall
    push Not at hall
    simp [hall] at hvpos
  obtain ⟨k₁, hk₁⟩ := hwne
  have hAw : 0 < ∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) := by
    refine Finset.sum_pos' (fun k _ => mul_nonneg (hw0 k) (hapos k).le) ⟨k₁, Finset.mem_univ _, ?_⟩
    exact mul_pos (lt_of_le_of_ne (hw0 k₁) (Ne.symm hk₁)) (hapos k₁)
  set Aw : ℝ := ∑ k, w k * (((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) with hAwdef
  refine ⟨fun k => w k / Aw, fun k => div_nonneg (hw0 k) hAw.le, ⟨p, hpx, fun k hk => hwp k ?_⟩,
    ?_, fun i => ?_⟩
  · intro h0
    exact hk (by change w k / Aw = 0; rw [h0, zero_div])
  · change ∑ k, w k / Aw * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) = 1
    have h : ∑ k, w k / Aw * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) = Aw / Aw := by
      rw [hAwdef, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, div_self hAw.ne']
  · change α i ≤ ∑ k, w k / Aw * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)
    have h : ∑ k, w k / Aw * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) =
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i)))
          (e : U) : ℝ) / Aw := by
      rw [← hv i, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h, le_div_iff₀ hAw]
    calc α i * Aw ≤ α i * (((d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) :=
          mul_le_mul_of_nonneg_left hA (hα0 i)
      _ ≤ _ := hval i (hs i)

/-- From realization to weights, in the limit: on a klt pair, if the tuple realizes profiles
α_l ≥ 0 converging to q with some q_i > 0, some weight u ≥ 0 over π⁻¹(x) on the model has A(u) = 1
and v_i(u) ≥ q_i for all i. -/
theorem exists_normalized_sncWeight_of_tendsto_isRealizedProfile {N r : ℕ}
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0)
    (x : Y) (α : ℕ → Fin N → ℝ) (q : Fin N → ℝ) (hα0 : ∀ l i, 0 ≤ α l i)
    (hreal : ∀ l, IsRealizedProfile cY fY d D₀ D x s (α l)) (hlim : Tendsto α atTop (𝓝 q))
    (hqpos : ∃ i, 0 < q i) :
    ∃ u : Fin r → ℝ, (∀ k, 0 ≤ u k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, u k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      ∑ k, u k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) = 1 ∧
      ∀ i, q i ≤ ∑ k, u k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set a : Fin r → ℝ := fun k => ((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d with ha
  have hapos : ∀ k, 0 < a k := fun k => by
    have hb : cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (ξ k) < (d : ℤ) :=
      logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
    have hb' : (cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (ξ k) : ℝ) < (d : ℝ) := by exact_mod_cast hb
    exact div_pos (by linarith) hdpos
  obtain ⟨i₁, hi₁⟩ := hqpos
  -- eventually the profiles are positive at i₁
  obtain ⟨l₀, hl₀⟩ := eventually_atTop.mp
    ((tendsto_pi_nhds.mp hlim i₁).eventually (lt_mem_nhds hi₁))
  choose u hu0 huΦ huA huv using fun l => exists_normalized_sncWeight_of_isRealizedProfile π hπ
    cY fY d hd D₀ hklt cX ξ hinj hξ hsnc hBsupp D s hs hGsupp x (hα0 (l + l₀))
    ⟨i₁, hl₀ (l + l₀) (Nat.le_add_left _ _)⟩ (hreal (l + l₀))
  -- the normalized weights over the fibre form a compact set
  have hcompact : IsCompact ({w : Fin r → ℝ | (∀ k, 0 ≤ w k) ∧
      ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} ∩
      normalizedWeights a) :=
    (isCompact_normalizedWeights hapos).inter_left (isClosed_sncWeights ξ (π ⁻¹' ({x} : Set Y)))
  have hmem : ∀ l, u l ∈ ({w : Fin r → ℝ | (∀ k, 0 ≤ w k) ∧
      ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} ∩
      normalizedWeights a) := fun l =>
    ⟨⟨hu0 l, huΦ l⟩, hu0 l, by
      rw [← huA l]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _⟩
  obtain ⟨u₀, ⟨⟨hu₀0, hu₀Φ⟩, -, hu₀A⟩, φ, hφ, hφlim⟩ := hcompact.tendsto_subseq hmem
  refine ⟨u₀, hu₀0, hu₀Φ, ?_, fun i => ?_⟩
  · rw [← hu₀A]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · have hcont : Continuous fun w : Fin r → ℝ => ∑ k, w k * (cartierCoefficient
        (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ) := by fun_prop
    have h1 : Tendsto (fun l => ∑ k, u (φ l) k * (cartierCoefficient
        (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) atTop
        (𝓝 (∑ k, u₀ k * (cartierCoefficient
          (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ))) :=
      (hcont.tendsto u₀).comp hφlim
    have h2 : Tendsto (fun l => α (φ l + l₀) i) atTop (𝓝 (q i)) :=
      (tendsto_pi_nhds.mp hlim i).comp ((tendsto_add_atTop_nat l₀).comp hφ.tendsto_atTop)
    exact le_of_tendsto_of_tendsto' h2 h1 fun l => huv (φ l) i

end Retraction

end MixedFujita

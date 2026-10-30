/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightTestPrimes
public import MixedFujita.ProjectiveMinimizationInterval
public import MixedFujita.SmoothProperCurveSections
public import MixedFujita.LogPairDenominatorScaling

/-!
The bound (8) of section 3.1 of the manuscript for the weights of a simple normal crossing model
(step 11): a subspace on which every divisorial valuation with centre through x is small forces
many small values of every weight, for every basis.

* Along a prime divisor t of the source of a dominant morphism ρ, the coefficient of the pullback
  of the zero divisor of a nonzero section s is the order at t of the pulled back local
  coefficient of s; the sections of order at least k form a subspace (the order is a valuation on
  sections: it does not drop under sums and scalars).
* Counting. Let π : X → Y be a simple normal crossing model of a pair and of the zero divisors of a
  basis B_1, …, B_N of the sections of a Cartier divisor D of Y, and let U be a subspace of
  sections such that for every prime divisor e of a smooth birational test model σ of Y whose
  centre contains x and every nonzero s in U, ord_e(σ* div s) ≤ θ A(e) (A the log discrepancy for
  the pair). Then for every weight w ≥ 0 over the fibre of x at least dim U of the values satisfy
  v_i(w) ≤ θ A(w). For natural weights this is linear algebra on the prime divisor extracting the
  weight: U meets the subspace of sections of order > θ A(e) only in 0. Real weights follow from
  nearby rational weights with the same support, since the failing strict inequalities are open.
* Consequently F(w) ≥ dim U · exp(A(w) (1/t − θ/j)) for t, j > 0. With θ = j/(2t) and
  dim U ≥ κ N this is the bound (8): F ≥ κ N exp(A/(2t)).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
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

section Order

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  (ρ : T ⟶ X)

/-- The sections whose pulled back local coefficient has order at least k at a point form a
subspace. -/
noncomputable def cartierStalkPullbackOrderAtLeast [ρ.IsOver (Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (t : T) (k : ℕ) : Submodule K Γ(D.sheaf, ⊤) where
  carrier := {s | (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t s}
  add_mem' := fun {s s'} hs hs' => by
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
    change (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t (s + s')
    have h1 : (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t s := hs
    have h2 : (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t s' := hs'
    rw [cartierStalkPullbackOrder_nat_le_iff D ρ t f hf] at h1 h2 ⊢
    rw [map_add]
    exact Ideal.add_mem _ h1 h2
  zero_mem' := by
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
    change (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t 0
    rw [cartierStalkPullbackOrder_nat_le_iff D ρ t f hf, map_zero]
    exact Ideal.zero_mem _
  smul_mem' := fun a s hs => by
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
    change (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t (a • s)
    have h1 : (k : ℕ∞) ≤ cartierStalkPullbackOrder D ρ t s := hs
    rw [cartierStalkPullbackOrder_nat_le_iff D ρ t f hf] at h1 ⊢
    rw [cartierStalkPullbackCoefficient_smul]
    exact Ideal.mul_mem_left _ _ h1

omit [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))] in
/-- Along a prime divisor of the source of a dominant morphism, the coefficient of the pullback of
the zero divisor of a nonzero section is the order of its pulled back local coefficient. -/
theorem cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder [IsDominant ρ]
    [IsLocallyNoetherian T] (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (t : CodimensionOnePoint T) [IsDiscreteValuationRing (T.presheaf.stalk (t : T))] :
    ∃ k : ℕ, cartierStalkPullbackOrder D ρ (t : T) s = (k : ℕ∞) ∧
      cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor D s hs)) (t : T) =
        (k : ℤ) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ (t : T))
  have himg : algebraMap (X.presheaf.stalk (ρ (t : T))) X.functionField
      (cartierLocalCoefficient D (ρ (t : T)) f hf s) =
      ((f * cartierSectionUnit D s hs : X.functionFieldˣ) : X.functionField) := by
    simpa only [Units.val_mul, cartierSectionUnit_val] using
      cartierLocalCoefficient_image D (ρ (t : T)) f hf s
  have heq : (cartierSectionZeroDivisor D s hs).IsLocalEquationAt (ρ (t : T))
      (f * cartierSectionUnit D s hs) :=
    cartierSectionZeroDivisor_localEquation D s hs (ρ (t : T)) f hf
  have hgimg : algebraMap (T.presheaf.stalk (t : T)) T.functionField
      (cartierStalkPullbackCoefficient D ρ (t : T) f hf s) =
      ((Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (f * cartierSectionUnit D s hs) : T.functionFieldˣ) : T.functionField) := by
    rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap, himg]
    rfl
  have hne : cartierStalkPullbackCoefficient D ρ (t : T) f hf s ≠ 0 := by
    intro h0
    have h1 : algebraMap (T.presheaf.stalk (t : T)) T.functionField
        (cartierStalkPullbackCoefficient D ρ (t : T) f hf s) ≠ 0 := by
      rw [hgimg]
      exact Units.ne_zero _
    exact h1 (by rw [h0, map_zero])
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
    (fun h => hne ((localAdicOrder_eq_top_iff _).mp h))
  refine ⟨k, by rw [cartierStalkPullbackOrder_eq_localCoefficient D ρ (t : T) f hf, hk], ?_⟩
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ _ (t : T) heq), ← hgimg]
  exact scheme_ord_regular_eq_localAdicOrder_nat t _ hne k hk.symm

end Order

section Approximation

/-- A weight is approximated by rational weights with the same support. -/
theorem exists_natural_weight_approximation {r : ℕ} (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) {η : ℝ}
    (hη : 0 < η) :
    ∃ (M : ℕ) (W : Fin r → ℕ), 1 ≤ M ∧ dist (fun k => (W k : ℝ) / M) w < η ∧
      ∀ k, W k = 0 ↔ w k = 0 := by
  have hq : ∀ k, ∃ q : ℚ, 0 ≤ q ∧ dist (q : ℝ) (w k) < η ∧ (q = 0 ↔ w k = 0) := by
    intro k
    by_cases hk : w k = 0
    · refine ⟨0, le_rfl, ?_, ⟨fun _ => hk, fun _ => rfl⟩⟩
      rw [hk, Rat.cast_zero, dist_self]
      exact hη
    · have hpos : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hk)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show w k < w k + η by linarith)
      have hqpos : (0 : ℝ) < (q : ℝ) := hpos.trans hq1
      refine ⟨q, by exact_mod_cast hqpos.le, ?_, ⟨fun h => ?_, fun h => absurd h hk⟩⟩
      · rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      · rw [h, Rat.cast_zero] at hqpos
        exact absurd hqpos (lt_irrefl 0)
  choose q hq0 hqd hqz using hq
  obtain ⟨M, W, hM, hWq⟩ := exists_common_denominator_nat q hq0
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hwq : (fun k => (W k : ℝ) / M) = fun k => (q k : ℝ) := by
    funext k
    have h : (W k : ℝ) = (M : ℝ) * (q k : ℝ) := by exact_mod_cast hWq k
    rw [h]
    field_simp
  refine ⟨M, W, hM, ?_, fun k => ?_⟩
  · rw [hwq, dist_pi_lt_iff hη]
    exact hqd
  · rw [← hqz k]
    have h := hWq k
    constructor
    · intro h0
      rw [h0, Nat.cast_zero] at h
      have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hM)
      exact (mul_eq_zero.mp h.symm).resolve_left hM'
    · intro h0
      rw [h0, mul_zero] at h
      exact_mod_cast h

end Approximation

section Counting

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Counting for natural weights: if every prime divisor of a smooth birational test model whose
centre contains x has ord_e(σ* div s) ≤ θ A(e) on the nonzero elements of a subspace U, then for
natural weights W ≠ 0 on the members through a point over x at least dim U of the basis elements
have Σ_k e_ik W_k ≤ θ Σ_k a_k W_k. -/
theorem exists_card_weight_values_le_of_natural_weights {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (z : X) = 0)
    (x : Y) (U : Submodule K Γ(D.sheaf, ⊤)) {θ : ℝ}
    (hU : ∀ (U' : Scheme.{u}) [IsIntegral U'] [IsLocallyNoetherian U']
      [U'.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U' ↘ Spec (CommRingCat.of K))]
      (σ : U' ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U' n)
      (e : CodimensionOnePoint U'), x ∈ closure ({σ (e : U')} : Set Y) →
      ∀ s ∈ U, ∀ hs : s ≠ 0,
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U') : ℝ) ≤
          θ * (((d : ℝ) + cartierCoefficient
            (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U')) / d))
    (y : X) (hy : π y = x) (W : Fin r → ℕ) (hW : W ≠ 0)
    (hWy : ∀ k, W k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ S : Finset (Fin N), Module.finrank K U ≤ S.card ∧ ∀ i ∈ S,
      ∑ k, (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ) * (W k : ℝ) ≤
      θ * ∑ k, (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) * (W k : ℝ) := by
  classical
  have : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis B
  obtain ⟨U', hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, hg, hcl, hpull, hdisc⟩ :=
    exists_base_test_prime_of_natural_weights π hπ cY fY d D₀ cX ξ hinj hξ hsnc hBsupp y W hW hWy
  rw [hy] at hcl
  have hsm : Smooth (U' ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdvr := smoothOverField_codimensionOne_stalk_DVR (K := K) e
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  set Ae : ℝ := ((d : ℝ) + cartierCoefficient
    (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U')) / d with hAe
  -- g times the log discrepancy and the values of the prime divisor are those of the weight
  have hA : (g : ℝ) * Ae = ∑ k, (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) * (W k : ℝ) := by
    have h : (g : ℝ) * ((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U')) =
        ∑ k, ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) * (W k : ℝ) := by
      exact_mod_cast hdisc
    rw [hAe, mul_div_assoc', h, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  have hv : ∀ i, (g : ℝ) * (cartierCoefficient (cartierPullback σ
      (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (e : U') : ℝ) =
      ∑ k, (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ) * (W k : ℝ) := by
    intro i
    exact_mod_cast hpull _ (hGsupp i)
  by_cases hneg : θ * Ae < 0
  · -- then U is trivial
    have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro s hsU
      by_contra hs0
      have hs0' : s ≠ 0 := hs0
      have h1 := hU U' σ hσ cU e hcl s hsU hs0'
      have h2 : (0 : ℝ) ≤ (cartierCoefficient (cartierPullback σ
          (cartierSectionZeroDivisor D s hs0')) (e : U') : ℝ) := by
        exact_mod_cast cartierCoefficient_nonneg_of_isEffective _
          (cartierPullback_isEffective σ _ (cartierSectionZeroDivisor_isEffective D s hs0')) _
      linarith
    exact ⟨∅, by rw [hbot, finrank_bot]; exact Nat.zero_le _, fun i hi => absurd hi (by simp)⟩
  · have hnn : 0 ≤ θ * Ae := not_lt.mp hneg
    -- the subspace of sections of order larger than θ A(e)
    obtain ⟨S, hScard, hS⟩ := basis_exists_card_not_mem B U
      (cartierStalkPullbackOrderAtLeast (K := K) σ D (e : U') (⌊θ * Ae⌋₊ + 1)) (by
        rw [eq_bot_iff]
        rintro s ⟨hsU, hsW⟩
        by_contra hs0
        have hs0' : s ≠ 0 := hs0
        obtain ⟨k, hk, hcoef⟩ :=
          cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder σ D s hs0' e
        have h1 := hU U' σ hσ cU e hcl s hsU hs0'
        rw [hcoef] at h1
        have h2 : ((⌊θ * Ae⌋₊ + 1 : ℕ) : ℕ∞) ≤ cartierStalkPullbackOrder D σ (e : U') s := hsW
        rw [hk] at h2
        have h3 : ⌊θ * Ae⌋₊ + 1 ≤ k := by exact_mod_cast h2
        have h4 : (k : ℝ) < ⌊θ * Ae⌋₊ + 1 := by
          have h5 : ((k : ℤ) : ℝ) ≤ θ * Ae := h1
          have h6 : θ * Ae < ⌊θ * Ae⌋₊ + 1 := Nat.lt_floor_add_one _
          have h7 : ((k : ℤ) : ℝ) = (k : ℝ) := by norm_cast
          linarith
        have h8 : k < ⌊θ * Ae⌋₊ + 1 := by exact_mod_cast h4
        omega)
    refine ⟨S, hScard, fun i hi => ?_⟩
    obtain ⟨k, hk, hcoef⟩ :=
      cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder σ D (B i) (B.ne_zero i) e
    have hnot : ¬ ((⌊θ * Ae⌋₊ + 1 : ℕ) : ℕ∞) ≤ cartierStalkPullbackOrder D σ (e : U') (B i) :=
      hS i hi
    rw [hk] at hnot
    have hk' : k ≤ ⌊θ * Ae⌋₊ := by
      have h : ¬ (⌊θ * Ae⌋₊ + 1 ≤ k) := fun h => hnot (by exact_mod_cast h)
      omega
    have hkθ : (k : ℝ) ≤ θ * Ae := (Nat.le_floor_iff hnn).mp hk'
    rw [← hv i, hcoef, ← hA]
    have h7 : ((k : ℤ) : ℝ) = (k : ℝ) := by norm_cast
    rw [h7]
    calc (g : ℝ) * (k : ℝ) ≤ (g : ℝ) * (θ * Ae) := mul_le_mul_of_nonneg_left hkθ hgpos.le
      _ = θ * ((g : ℝ) * Ae) := by ring

/-- Counting for all weights: under the same hypothesis on U, for every weight w ≥ 0 over the fibre
of x at least dim U of the values satisfy v_i(w) ≤ θ A(w). -/
theorem exists_card_weight_values_le {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (z : X) = 0)
    (x : Y) (U : Submodule K Γ(D.sheaf, ⊤)) {θ : ℝ}
    (hU : ∀ (U' : Scheme.{u}) [IsIntegral U'] [IsLocallyNoetherian U']
      [U'.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U' ↘ Spec (CommRingCat.of K))]
      (σ : U' ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U' n)
      (e : CodimensionOnePoint U'), x ∈ closure ({σ (e : U')} : Set Y) →
      ∀ s ∈ U, ∀ hs : s ≠ 0,
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U') : ℝ) ≤
          θ * (((d : ℝ) + cartierCoefficient
            (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U')) / d))
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hwΦ : ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) :
    ∃ S : Finset (Fin N), Module.finrank K U ≤ S.card ∧ ∀ i ∈ S,
      ∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ) ≤
      θ * ∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) := by
  classical
  have : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis B
  obtain ⟨p, hpx, hwp⟩ := hwΦ
  set a : Fin r → ℝ := fun k => ((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d with ha
  set ev : Fin N → Fin r → ℝ := fun i k => (cartierCoefficient (cartierPullback π
    (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ) with hev
  -- the indices with a small value
  set I : Finset (Fin N) := Finset.univ.filter
    (fun i => ∑ k, w k * ev i k ≤ θ * ∑ k, w k * a k) with hI
  refine ⟨I, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  by_contra hcard
  have hcard' : I.card < Module.finrank K U := not_le.mp hcard
  -- the failing strict inequalities are open in the weight
  have hopen : IsOpen {w' : Fin r → ℝ | ∀ i ∈ Iᶜ, θ * ∑ k, w' k * a k < ∑ k, w' k * ev i k} := by
    have hset : {w' : Fin r → ℝ | ∀ i ∈ Iᶜ, θ * ∑ k, w' k * a k < ∑ k, w' k * ev i k} =
        ⋂ i ∈ Iᶜ, {w' : Fin r → ℝ | θ * ∑ k, w' k * a k < ∑ k, w' k * ev i k} := by
      ext w'
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [hset]
    exact isOpen_biInter_finset fun i _ => isOpen_lt (by fun_prop) (by fun_prop)
  have hwmem : w ∈ {w' : Fin r → ℝ | ∀ i ∈ Iᶜ, θ * ∑ k, w' k * a k < ∑ k, w' k * ev i k} := by
    intro i hi
    have hni : i ∉ I := Finset.mem_compl.mp hi
    exact not_le.mp fun hle => hni (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hle⟩)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen w hwmem
  obtain ⟨M, W, hM, hdist, hsupp⟩ := exists_natural_weight_approximation w hw0 hη
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hWmem := hball (Metric.mem_ball.mpr hdist)
  by_cases hW : W = 0
  · -- the weight is zero: every index is small
    have hw : w = 0 := by
      funext k
      exact (hsupp k).mp (by rw [hW]; rfl)
    have hall : I = Finset.univ := by
      rw [hI, Finset.filter_eq_self]
      intro i _
      rw [hw]
      simp
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard'
    have hle : Module.finrank K U ≤ N := by
      have h := Submodule.finrank_le U
      rwa [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    omega
  · have hWy : ∀ k, W k ≠ 0 → p ∈ closure ({ξ k} : Set X) := fun k hk =>
      hwp k fun h0 => hk ((hsupp k).mpr h0)
    obtain ⟨S, hScard, hS⟩ := exists_card_weight_values_le_of_natural_weights π hπ cY fY d hd D₀
      cX ξ hinj hξ hsnc hBsupp D B hGsupp x U hU p hpx W hW hWy
    have hsub : S ⊆ I := by
      intro i hi
      by_contra hni
      have h1 := hWmem i (Finset.mem_compl.mpr hni)
      have h2 := hS i hi
      have e1 : ∑ k, (W k : ℝ) / M * ev i k =
          (∑ k, ev i k * (W k : ℝ)) / M := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
      have e2 : ∑ k, (W k : ℝ) / M * a k = (∑ k, a k * (W k : ℝ)) / M := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e1, e2, ← mul_div_assoc, div_lt_div_iff_of_pos_right hMpos] at h1
      exact absurd h2 (not_le.mpr h1)
    have := Finset.card_le_card hsub
    omega

/-- The bound (8): under the same hypothesis on U, for t, j > 0 and every weight w ≥ 0 over the
fibre of x, F(w) ≥ dim U · exp(A(w) (1/t − θ/j)). -/
theorem weightExponentialObjective_ge_of_low_subspace {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (z : X) = 0)
    (x : Y) (U : Submodule K Γ(D.sheaf, ⊤)) {θ : ℝ}
    (hU : ∀ (U' : Scheme.{u}) [IsIntegral U'] [IsLocallyNoetherian U']
      [U'.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (U' ↘ Spec (CommRingCat.of K))]
      (σ : U' ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U' n)
      (e : CodimensionOnePoint U'), x ∈ closure ({σ (e : U')} : Set Y) →
      ∀ s ∈ U, ∀ hs : s ≠ 0,
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U') : ℝ) ≤
          θ * (((d : ℝ) + cartierCoefficient
            (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U')) / d))
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hwΦ : ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    {t j : ℝ} (hj : 0 < j) :
    (Module.finrank K U : ℝ) * Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) *
        (1 / t - θ / j)) ≤
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) t j w := by
  obtain ⟨S, hScard, hS⟩ := exists_card_weight_values_le π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc
    hBsupp D B hGsupp x U hU w hw0 hwΦ
  unfold weightExponentialObjective
  set A : ℝ := ∑ k, w k * (((d : ℝ) - cartierCoefficient
    (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) with hA
  have hterm : ∀ i ∈ S, Real.exp (A * (1 / t - θ / j)) ≤
      Real.exp (A / t - (∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j) := by
    intro i hi
    apply Real.exp_le_exp.mpr
    have h1 := hS i hi
    have h2 : (∑ k, w k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j ≤ θ * A / j :=
      div_le_div_of_nonneg_right h1 hj.le
    have h3 : A * (1 / t - θ / j) = A / t - θ * A / j := by ring
    rw [h3]
    linarith
  calc (Module.finrank K U : ℝ) * Real.exp (A * (1 / t - θ / j))
      ≤ (S.card : ℝ) * Real.exp (A * (1 / t - θ / j)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hScard) (Real.exp_pos _).le
    _ = ∑ _i ∈ S, Real.exp (A * (1 / t - θ / j)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ S, Real.exp (A / t - (∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ i, Real.exp (A / t - (∑ k, w k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (B i) (B.ne_zero i))) (ξ k) : ℝ)) / j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          fun i _ _ => (Real.exp_pos _).le

end Counting

end MixedFujita

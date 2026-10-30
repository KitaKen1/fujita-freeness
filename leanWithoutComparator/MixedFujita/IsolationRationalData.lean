/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationDivisorStructure
public import MixedFujita.ProfilePolytopeRationalChoice
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.LogPairDenominatorScaling

/-!
The rational isolation of sections 6.1 and 6.2 of the manuscript, from the data of the minimizer
(step 12).

Let (X, B) be a simple normal crossing pair with family ξ_j, D_i effective Cartier divisors
supported on the family, Φ a closed subset of X and y a point of Φ. The real data of the
minimizer are a positive vector c and a profile q with c · q = 1 such that

* q lies in the polytope of y;
* (24): c · z_j ≤ 1 for the members through every point of Φ whose polytope contains q;
* point centres: a point specializing into Φ whose polytope contains q lies in Φ;
* m Σ_i c_i < b.

Then there are a positive rational vector c⁰ and a rational profile q⁰, a rational convex
combination of the profiles of the members through y, with c⁰ · q⁰ = 1 and m Σ_i c⁰_i < b, for
which the same three properties hold: q⁰ lies in a polytope only if q does. For a natural number
M with all M/q⁰_i natural there is a projective simple normal crossing model T principalizing the
sum of the ideal sheaves of the divisors (M/q⁰_i) D_i, q⁰_i > 0, by an effective divisor G, with
M_L' − G globally generated and nef on T whenever all M_L − (M/q⁰_i) D_i are globally generated on
X, and for every 0 < η < 1 the divisor Ψ = (1 − η) Σ_i c⁰_i ρ*D_i + (η/M) G has a nonempty set S of
members of the family of T over Φ on which Ψ is the log discrepancy, while every other prime
divisor meeting S has Ψ smaller than its log discrepancy: the output of sections 6.1 and 6.2,
with the data of the minimizer as the only hypotheses.
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

/-- A natural number M such that all M/q_i with q_i > 0 are natural numbers. -/
theorem exists_nat_multiple_div {ι : Type*} [Fintype ι] (q : ι → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ (M : ℕ) (nn : ι → ℕ), 1 ≤ M ∧ ∀ i, 0 < q i → (nn i : ℚ) = M / q i := by
  obtain ⟨D, W, hD, hW⟩ := exists_common_denominator_nat (fun i => (q i)⁻¹)
    (fun i => inv_nonneg.mpr (hq i))
  exact ⟨D, W, hD, fun i _ => by rw [hW i, div_eq_mul_inv]⟩

section Effective

variable {X : Scheme.{u}} [IsIntegral X]

/-- A natural multiple of an effective Cartier divisor is effective. -/
theorem cartier_nsmul_isEffective (D : CartierDivisor X) (hD : D.IsEffective) (m : ℕ) :
    (m • D).IsEffective := by
  induction m with
  | zero =>
    rw [zero_nsmul]
    exact CartierDivisor.isEffective_zero
  | succ m ih =>
    rw [succ_nsmul]
    exact ih.add hD

end Effective

section Data

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The rational support data on a simple normal crossing pair: from a real vector c and a real
profile q in the polytope of y satisfying (24) and the point-centre property on Φ, a positive
rational vector c⁰ and a rational convex combination q⁰ of the profiles of the members through y
with c⁰ · q⁰ = 1, the same budget, and the same two properties. -/
theorem exists_rational_isolation_data {N r : ℕ} (ξ : Fin r → X) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ))
    (Dv : Fin N → CartierDivisor X) (hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j))
    (Φ : Set X) (y : X) (hy : y ∈ Φ) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i)
    (hcq : ∑ i, c i * q i = 1) (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv q p → ∀ j, p ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ Φ).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ Φ)
    {m b : ℝ} (hm : 0 ≤ m) (hbm : m * ∑ i, c i < b) :
    ∃ (c₁ : Fin N → ℝ) (lam₀ : Fin r → ℚ) (q₀ : Fin N → ℝ),
      (∀ i, 0 < c₁ i) ∧ (∀ i, ∃ x : ℚ, c₁ i = (x : ℝ)) ∧ (∀ j, 0 ≤ lam₀ j) ∧
      ∑ j, lam₀ j = 1 ∧ (∀ j, lam₀ j ≠ 0 → y ∈ closure ({ξ j} : Set X)) ∧
      (∀ i, q₀ i = ∑ j, (lam₀ j : ℝ) * ((cartierCoefficient (Dv i) (ξ j) : ℝ) /
        (((d : ℝ) - cartierCoefficient B (ξ j)) / d))) ∧
      (∀ i, 0 ≤ q₀ i) ∧ (∀ i, ∃ x : ℚ, q₀ i = (x : ℝ)) ∧
      ∑ i, c₁ i * q₀ i = 1 ∧ m * ∑ i, c₁ i < b ∧
      (∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv q₀ p → ∀ j, p ∈ closure ({ξ j} : Set X) →
        ∑ i, c₁ i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d) ∧
      ∀ p : X, (closure ({p} : Set X) ∩ Φ).Nonempty →
        InSNCProfilePolytope ξ d B Dv q₀ p → p ∈ Φ := by
  classical
  have hdpos : (0 : ℚ) < d := by exact_mod_cast hd
  -- rational coefficients and log discrepancies
  obtain ⟨e, he⟩ : ∃ e : Fin N → Fin r → ℚ, ∀ i j, e i j = (cartierCoefficient (Dv i) (ξ j) : ℚ) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Aj, hAjdef⟩ : ∃ Aj : Fin r → ℚ,
      ∀ j, Aj j = ((d : ℚ) - cartierCoefficient B (ξ j)) / d := ⟨_, fun _ => rfl⟩
  have hAj : ∀ j, 0 < Aj j := fun j => by
    rw [hAjdef j]
    have h' : ((cartierCoefficient B (ξ j) : ℤ) : ℚ) < (d : ℚ) := by exact_mod_cast hb j
    exact div_pos (by linarith) hdpos
  have hE : ∀ i j, ((e i j : ℚ) : ℝ) = (cartierCoefficient (Dv i) (ξ j) : ℝ) := fun i j => by
    rw [he i j]
    exact Rat.cast_intCast _
  have hA : ∀ j, ((Aj j : ℚ) : ℝ) = ((d : ℝ) - cartierCoefficient B (ξ j)) / d := fun j => by
    rw [hAjdef j]
    push_cast
    rfl
  -- polytopes in the two notations
  have hiff : ∀ (q' : Fin N → ℝ) (p : X), InSNCProfilePolytope ξ d B Dv q' p ↔
      q' ∈ profilePolytope (fun i j => ((e i j : ℚ) : ℝ) / ((Aj j : ℚ) : ℝ))
        {j | p ∈ closure ({ξ j} : Set X)} := by
    intro q' p
    constructor
    · rintro ⟨μ, h0, h1, hs, hq'⟩
      exact ⟨μ, h0, h1, hs, fun i => by
        rw [hq' i]
        exact Finset.sum_congr rfl fun j _ => by simp only [hE, hA]⟩
    · rintro ⟨μ, h0, h1, hs, hq'⟩
      exact ⟨μ, h0, h1, hs, fun i => by
        rw [hq' i]
        exact Finset.sum_congr rfl fun j _ => by simp only [hE, hA]⟩
  obtain ⟨lam, hlam0, hlam1, hlamsupp, hqlam⟩ := hqy
  have hqy' : InSNCProfilePolytope ξ d B Dv q y := ⟨lam, hlam0, hlam1, hlamsupp, hqlam⟩
  have hpoly : ∀ j, lam j ≠ 0 → ∑ i, c i * ((e i j : ℚ) : ℝ) ≤ ((Aj j : ℚ) : ℝ) := by
    intro j hj
    simp only [hE, hA]
    exact hpolyΦ y hy hqy' j (hlamsupp j hj)
  have hcq' : ∑ i, c i * ∑ j, lam j * (((e i j : ℚ) : ℝ) / ((Aj j : ℚ) : ℝ)) = 1 := by
    simp only [hE, hA]
    rw [← hcq]
    exact Finset.sum_congr rfl fun i _ => by rw [hqlam i]
  obtain ⟨c₀, lam₀, hc₀pos, hlam₀nn, hlam₀sum, hsupp₀, hc₀le, hc₀q₀, hbudget, havoid⟩ :=
    exists_rational_support_data e Aj hAj c hc lam hlam0 hlam1 hpoly hcq' hm hbm
  simp only [hE, hA] at hc₀le hc₀q₀
  -- the two profiles as functions
  have hqfun : (fun i => ∑ j, lam j * (((e i j : ℚ) : ℝ) / ((Aj j : ℚ) : ℝ))) = q := by
    funext i
    rw [hqlam i]
    exact Finset.sum_congr rfl fun j _ => by simp only [hE, hA]
  obtain ⟨q₀, hq₀⟩ : ∃ q₀ : Fin N → ℝ, ∀ i, q₀ i =
      ∑ j, (lam₀ j : ℝ) * ((cartierCoefficient (Dv i) (ξ j) : ℝ) /
        (((d : ℝ) - cartierCoefficient B (ξ j)) / d)) := ⟨_, fun _ => rfl⟩
  have hq₀fun : (fun i => ∑ j, (lam₀ j : ℝ) * (((e i j : ℚ) : ℝ) / ((Aj j : ℚ) : ℝ))) = q₀ := by
    funext i
    rw [hq₀ i]
    exact Finset.sum_congr rfl fun j _ => by simp only [hE, hA]
  have htr : ∀ p : X, InSNCProfilePolytope ξ d B Dv q₀ p → InSNCProfilePolytope ξ d B Dv q p := by
    intro p hp
    have h1 := (hiff q₀ p).mp hp
    rw [← hq₀fun] at h1
    have h2 := havoid _ h1
    rw [hqfun] at h2
    exact (hiff q p).mpr h2
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : Fin N → ℝ, ∀ i, c₁ i = (c₀ i : ℝ) := ⟨_, fun _ => rfl⟩
  simp only [← hc₁] at hc₀le hc₀q₀ hbudget
  refine ⟨c₁, lam₀, q₀, fun i => by rw [hc₁ i]; exact_mod_cast hc₀pos i, fun i => ⟨c₀ i, hc₁ i⟩,
    hlam₀nn, hlam₀sum, fun j hj => hlamsupp j (hsupp₀ j hj), hq₀, fun i => ?_, fun i => ?_, ?_,
    hbudget, fun p hp hq₀p j hj => hc₀le j (hpolyΦ p hp (htr p hq₀p) j hj),
    fun p hne hq₀p => hcentre p hne (htr p hq₀p)⟩
  · -- q⁰ ≥ 0
    rw [hq₀ i]
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by exact_mod_cast hlam₀nn j) ?_
    rw [← hA j]
    exact div_nonneg (by exact_mod_cast hDnn i j) (by exact_mod_cast (hAj j).le)
  · -- q⁰ is rational
    refine ⟨∑ j, lam₀ j * (e i j / Aj j), ?_⟩
    rw [hq₀ i]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [hE, hA]
  · -- c⁰ · q⁰ = 1
    rw [← hc₀q₀]
    exact Finset.sum_congr rfl fun i _ => by rw [hq₀ i]

end Data

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- The rational isolation of sections 6.1 and 6.2 on a simple normal crossing pair, from the
data of the minimizer: rational c⁰ and q⁰, a natural number M with all M/q⁰_i natural, a proper
simple normal crossing model T principalizing the sum of the ideal sheaves of the (M/q⁰_i) D_i by
an effective divisor G with M_L' − G globally generated and nef, and for every 0 < η < 1 a
nonempty set S of members of the family of T over Φ on which
Ψ = (1 − η) Σ_i c⁰_i ρ*D_i + (η/M) G equals the log discrepancy, every other prime divisor meeting
S having Ψ smaller than its log discrepancy. -/
theorem exists_isolation_model {N r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ)) (Dv : Fin N → CartierDivisor X)
    (hDeff : ∀ i, (Dv i).IsEffective)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (Φ : Set X) (hΦ : IsClosed Φ) (y : X) (hy : y ∈ Φ) {c q : Fin N → ℝ} (hc : ∀ i, 0 < c i)
    (hcq : ∑ i, c i * q i = 1) (hqy : InSNCProfilePolytope ξ d B Dv q y)
    (hpolyΦ : ∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv q p → ∀ j, p ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ Φ).Nonempty →
      InSNCProfilePolytope ξ d B Dv q p → p ∈ Φ)
    {m b : ℝ} (hm : 0 ≤ m) (hbm : m * ∑ i, c i < b) :
    ∃ (c₁ q₀ : Fin N → ℝ) (Mn : ℕ) (nn : Fin N → ℕ),
      (∀ i, 0 < c₁ i) ∧ (∀ i, ∃ x : ℚ, c₁ i = (x : ℝ)) ∧ (∀ i, 0 ≤ q₀ i) ∧
      (∀ i, ∃ x : ℚ, q₀ i = (x : ℝ)) ∧ ∑ i, c₁ i * q₀ i = 1 ∧ m * ∑ i, c₁ i < b ∧ 1 ≤ Mn ∧
      (profileSupport q₀).Nonempty ∧ (∀ i ∈ profileSupport q₀, (nn i : ℝ) = (Mn : ℝ) / q₀ i) ∧
      ∃ (hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective)
        (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
        (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
        (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
        (cT : EtaleChart K T n) (r' : ℕ) (ξT : Fin r' → T) (Gc : CartierDivisor T)
        (hGc : Gc.IsEffective),
        Function.Injective ξT ∧ (∀ s, Order.coheight (ξT s) = 1) ∧ IsSNCFamily K n ξT ∧
        (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
          cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (t : T) = 0) ∧
        (∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
          cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0) ∧
        (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
          cartierCoefficient Gc (t : T) = 0) ∧
        effectiveCartierIdealSheaf Gc hGc =
          (⨆ k : {i // i ∈ profileSupport q₀},
            effectiveCartierIdealSheaf (nn k.1 • Dv k.1) (hAeff k)).comap ρ ∧
        (∀ ML : CartierDivisor X,
          (∀ k : {i // i ∈ profileSupport q₀},
            CartierIsGloballyGenerated (ML - nn k.1 • Dv k.1)) →
          CartierIsGloballyGenerated (cartierPullback ρ ML - Gc) ∧
            CartierIsNef K (cartierPullback ρ ML - Gc)) ∧
        ∀ η : ℝ, 0 < η → η < 1 → ∃ S : Set (Fin r'), S.Nonempty ∧
          (∀ k ∈ S, ρ (ξT k) ∈ Φ ∧
            (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
                η / (Mn : ℝ) * (cartierCoefficient Gc (ξT k) : ℝ) =
              ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
                (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
                cT etaleCharts_cover) (ξT k)) / d) ∧
          ∀ t : CodimensionOnePoint T,
            (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
            (1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
                η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) ≤
              ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
                (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
                cT etaleCharts_cover) (t : T)) / d ∧
            ((1 - η) * ∑ i, c₁ i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
                η / (Mn : ℝ) * (cartierCoefficient Gc (t : T) : ℝ) =
              ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
                (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
                cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k') := by
  classical
  have hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j) := fun i j =>
    cartierCoefficient_nonneg_of_isEffective (Dv i) (hDeff i) (ξ j)
  obtain ⟨c₁, lam₀, q₀, hc₁, hc₁rat, hlam₀nn, hlam₀sum, hlam₀y, hq₀lam, hq₀, hq₀rat, hc₁q₀,
    hbudget, hpolyΦ₀, hcentre₀⟩ := exists_rational_isolation_data ξ d hd B hb Dv hDnn Φ y hy hc
      hcq hqy hpolyΦ hcentre hm hbm
  -- the natural number M
  choose xq hxq using hq₀rat
  have hxq0 : ∀ i, 0 ≤ xq i := fun i => by
    have h := hq₀ i
    rw [hxq i] at h
    exact_mod_cast h
  obtain ⟨Mn, nn, hMn, hnnQ⟩ := exists_nat_multiple_div xq hxq0
  have hI : (profileSupport q₀).Nonempty := by
    by_contra hempty
    have hall : ∀ i, q₀ i = 0 := fun i => by
      by_contra hne
      exact hempty ⟨i, mem_profileSupport.mpr (lt_of_le_of_ne (hq₀ i) (Ne.symm hne))⟩
    have h0 : ∑ i, c₁ i * q₀ i = 0 := Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
    rw [hc₁q₀] at h0
    exact one_ne_zero h0
  have hnn : ∀ i ∈ profileSupport q₀, (nn i : ℝ) = (Mn : ℝ) / q₀ i := by
    intro i hi
    have hpos : (0 : ℝ) < q₀ i := mem_profileSupport.mp hi
    have hposQ : 0 < xq i := by
      rw [hxq i] at hpos
      exact_mod_cast hpos
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hnnQ i hposQ)
    simp only [Rat.cast_natCast, Rat.cast_div] at h
    rw [hxq i]
    exact h
  have hMnpos : (0 : ℝ) < (Mn : ℝ) := by exact_mod_cast hMn
  have hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective := fun k =>
    cartier_nsmul_isEffective (Dv k.1) (hDeff k.1) (nn k.1)
  have : Nonempty {i // i ∈ profileSupport q₀} := by
    obtain ⟨i, hi⟩ := hI
    exact ⟨⟨i, hi⟩⟩
  -- the principalizing model
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r', ξT, hinjT, hξT, hsncT,
    hTB, hTD, -, -, -, -, Gc, hGc, hGcI, hTG, -, hgg⟩ :=
    exists_projective_snc_model_principalizing_sum c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) Dv
      (fun k : {i // i ∈ profileSupport q₀} => nn k.1 • Dv k.1) hAeff
      (fun k : PEmpty.{1} => k.elim) (fun k => k.elim)
  refine ⟨c₁, q₀, Mn, nn, hc₁, hc₁rat, hq₀, fun i => ⟨xq i, hxq i⟩, hc₁q₀, hbudget, hMn, hI,
    hnn, hAeff, T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r', ξT, Gc, hGc, hinjT,
    hξT, hsncT, hTB, hTD, hTG, hGcI, hgg, fun η hη0 hη1 => ?_⟩
  exact isolation_divisor_structure ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hD hDnn hc₁ hq₀
    hc₁q₀ hI hMnpos hη0 hη1 nn hnn hAeff Φ hΦ y hy hpolyΦ₀ hcentre₀ cT ξT hinjT hξT hsncT hTB
    hTD Gc hGc hTG hGcI lam₀ hlam₀nn hlam₀sum hlam₀y hq₀lam

end Model

end MixedFujita

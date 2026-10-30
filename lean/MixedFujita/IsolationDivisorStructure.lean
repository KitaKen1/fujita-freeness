/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricExtractionPrime

/-!
The structure of the divisor S of section 6.2 of the manuscript (step 12).

Let (X, B) be a simple normal crossing pair with family ξ_j, D_i divisors supported on the family,
z_j = (e_ij / A_j)_i the profile of ξ_j, with A_j its log discrepancy, and T a proper smooth model
with a simple normal crossing family ξT_s supporting the crepant boundary, the pullbacks of the
D_i and the divisor G of the principalized ideal. Put
Ψ = (1 − η) Σ_i c_i ρ*D_i + (η/M) G and let A_t be the log discrepancy of a prime t of T.

A profile q lies in the polytope of a point p of X when it is a convex combination of the
profiles of the members through p. Let Φ be a closed subset of X (the fibre over the point of the
original variety at which sections are to be produced) and y a point of Φ such that

* (24) on Φ: for every point p of Φ whose polytope contains q⁰, c · z_j ≤ 1 for all members
  through p;
* point centres: a point p of X specializing to a point of Φ whose polytope contains q⁰ lies in Φ;
* q⁰ is a rational convex combination of the profiles of the members through y.

Let S be the set of members ξT_s of T with profile q⁰, with image in Φ and with q⁰ in the polytope
of the image. Then S is not empty, Ψ = A on S, and every prime divisor t of T meeting a member of
S satisfies Ψ_t ≤ A_t, with equality only if t is itself a member of S: the inequality (29).
This is the input of the lifting argument of section 6.3: with Γ = (crepant boundary) + Ψ the
members of S are exactly the primes near S with Γ = 1, and they lie over Φ.
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

section Arithmetic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A prime with profile q⁰ has retraction equal to its log discrepancy, and q⁰ is the convex
combination of the profiles e_j / A_j with weights A_j o_j / A: here v = e · o are the
coefficients computed from orders o_j ≥ 0, c · e_j ≤ A_j for every j with o_j ≠ 0, c · q⁰ = 1,
Σ_j A_j o_j ≤ A and v = A q⁰. -/
theorem isolation_polytope_of_profile_of_orders {c q₀ v : ι → ℝ} {e : ι → κ → ℝ} {Aj o : κ → ℝ}
    (hcq₀ : ∑ i, c i * q₀ i = 1) (ho : ∀ j, 0 ≤ o j) (hAj : ∀ j, 0 < Aj j)
    (hv : ∀ i, v i = ∑ j, e i j * o j) (hpoly : ∀ j, o j ≠ 0 → ∑ i, c i * e i j ≤ Aj j)
    {A : ℝ} (hA : 0 < A) (hRA : ∑ j, Aj j * o j ≤ A) (hprof : ∀ i, v i = A * q₀ i) :
    ∑ j, Aj j * o j / A = 1 ∧ ∀ i, q₀ i = ∑ j, Aj j * o j / A * (e i j / Aj j) := by
  have hcv : ∑ i, c i * v i = A := by
    have h : ∑ i, c i * v i = A * ∑ i, c i * q₀ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hprof i]; ring
    rw [h, hcq₀, mul_one]
  have hcv' : ∑ i, c i * v i ≤ ∑ j, Aj j * o j := by
    have h1 : ∑ i, c i * v i = ∑ j, (∑ i, c i * e i j) * o j := by
      simp_rw [hv, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hj : o j = 0
    · rw [hj, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right (hpoly j hj) (ho j)
  have hsum : ∑ j, Aj j * o j = A := le_antisymm hRA (by rw [← hcv]; exact hcv')
  refine ⟨by rw [← Finset.sum_div, hsum, div_self hA.ne'], fun i => ?_⟩
  have hqi : q₀ i = v i / A := by
    rw [hprof i]
    field_simp
  rw [hqi, hv i, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := (hAj j).ne'
  field_simp

end Arithmetic

section Polytope

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The profile q lies in the polytope of the members of the family through the point p: it is a
convex combination of the profiles z_j = (e_ij / A_j)_i of the members whose closure contains p,
where e_ij is the coefficient of D_i at ξ_j and A_j = (d − b_j)/d the log discrepancy of ξ_j. -/
def InSNCProfilePolytope {ι : Type*} {r : ℕ} (ξ : Fin r → X) (d : ℕ) (B : CartierDivisor X)
    (Dv : ι → CartierDivisor X) (q : ι → ℝ) (p : X) : Prop :=
  ∃ μ : Fin r → ℝ, (∀ j, 0 ≤ μ j) ∧ ∑ j, μ j = 1 ∧
    (∀ j, μ j ≠ 0 → p ∈ closure ({ξ j} : Set X)) ∧
    ∀ i, q i = ∑ j, μ j * ((cartierCoefficient (Dv i) (ξ j) : ℝ) /
      (((d : ℝ) - cartierCoefficient B (ξ j)) / d))

/-- The polytope of a point is contained in the polytope of each of its specializations. -/
theorem inSNCProfilePolytope_of_mem_closure {ι : Type*} {r : ℕ} {ξ : Fin r → X} {d : ℕ}
    {B : CartierDivisor X} {Dv : ι → CartierDivisor X} {q : ι → ℝ} {p p' : X}
    (h : InSNCProfilePolytope ξ d B Dv q p) (hp : p' ∈ closure ({p} : Set X)) :
    InSNCProfilePolytope ξ d B Dv q p' := by
  obtain ⟨μ, h0, h1, hsupp, hq⟩ := h
  exact ⟨μ, h0, h1, fun j hj =>
    closure_minimal (Set.singleton_subset_iff.mpr (hsupp j hj)) isClosed_closure hp, hq⟩

end Polytope

section Model

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- A prime divisor of a smooth birational model with profile q⁰, at whose image the polytope
condition holds, has q⁰ in the polytope of its image: its retraction is its log discrepancy. -/
theorem inSNCProfilePolytope_of_profile {ι : Type*} [Fintype ι] {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ)) (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (c'₀ : EtaleChart K T n) (t : CodimensionOnePoint T) {c q₀ : ι → ℝ}
    (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hpoly : ∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hprof : ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) =
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T)) / d * q₀ i) :
    InSNCProfilePolytope ξ d B Dv q₀ (ρ (t : T)) := by
  obtain ⟨o, ho, hosupp, hpull, hRA⟩ :=
    exists_real_snc_orders_at_prime ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB Dv hD c'₀ t
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hAj : ∀ j, (0 : ℝ) < ((d : ℝ) - cartierCoefficient B (ξ j)) / d := fun j => by
    have h' : ((cartierCoefficient B (ξ j) : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast hb j
    exact div_pos (by linarith) hdpos
  have hA : (0 : ℝ) < ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      c'₀ etaleCharts_cover) (t : T)) / d := by
    have h := isSNCFamily_actual_discrepancy_bound ρ hρ c₀ f₀ d hd B ξ hinj hξ hsnc hB hb c'₀ t
    have h' : -(d : ℝ) < (cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        c'₀ etaleCharts_cover) (t : T) : ℝ) := by exact_mod_cast h
    exact div_pos (by linarith) hdpos
  obtain ⟨h1, h2⟩ := isolation_polytope_of_profile_of_orders
    (e := fun i j => (cartierCoefficient (Dv i) (ξ j) : ℝ))
    (Aj := fun j => ((d : ℝ) - cartierCoefficient B (ξ j)) / d) hcq₀ ho hAj hpull
    (fun j hj => hpoly j (hosupp j hj)) hA hRA hprof
  exact ⟨_, fun j => div_nonneg (mul_nonneg (hAj j).le (ho j)) hA.le, h1,
    fun j hj => hosupp j fun h0 => hj (by rw [h0, mul_zero, zero_div]), h2⟩

variable [IsProper ρ]

/-- The structure of the divisor S of section 6.2. Let Φ be a closed subset of X and y a point of
Φ such that the polytope condition c · z_j ≤ 1 holds at the points of Φ whose polytope contains
q⁰, points specializing into Φ whose polytope contains q⁰ lie in Φ, and q⁰ is a rational convex
combination of the profiles of the members through y. Then the set S of members of the family of
the principalizing model T with profile q⁰, image in Φ and q⁰ in the polytope of the image is not
empty, Ψ equals the log discrepancy on S, and every prime divisor of T meeting a member of S has
Ψ at most its log discrepancy, with equality only for the members of S. -/
theorem isolation_divisor_structure {ι : Type*} [Fintype ι] {r : ℕ}
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ j, cartierCoefficient B (ξ j) < (d : ℤ)) (Dv : ι → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (hDnn : ∀ i j, 0 ≤ cartierCoefficient (Dv i) (ξ j))
    {c q₀ : ι → ℝ} (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i) (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hI : (profileSupport q₀).Nonempty) {M η : ℝ} (hM : 0 < M) (hη0 : 0 < η) (hη1 : η < 1)
    (nn : ι → ℕ) (hnn : ∀ i ∈ profileSupport q₀, (nn i : ℝ) = M / q₀ i)
    (hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective)
    (Φ : Set X) (hΦ : IsClosed Φ) (y : X) (hy : y ∈ Φ)
    (hpolyΦ : ∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv q₀ p → ∀ j, p ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ Φ).Nonempty →
      InSNCProfilePolytope ξ d B Dv q₀ p → p ∈ Φ)
    (cT : EtaleChart K T n) {r' : ℕ} (ξT : Fin r' → T) (hinjT : Function.Injective ξT)
    (hξT : ∀ s, Order.coheight (ξT s) = 1) (hsncT : IsSNCFamily K n ξT)
    (hTB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) = 0)
    (hTD : ∀ i, ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) = 0)
    (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hTG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
      cartierCoefficient Gc (t : T) = 0)
    (hGcI : effectiveCartierIdealSheaf Gc hGc =
      (⨆ k : {i // i ∈ profileSupport q₀},
        effectiveCartierIdealSheaf (nn k.1 • Dv k.1) (hAeff k)).comap ρ)
    (lam : Fin r → ℚ) (hlam : ∀ j, 0 ≤ lam j) (hlam1 : ∑ j, lam j = 1)
    (hlamy : ∀ j, lam j ≠ 0 → y ∈ closure ({ξ j} : Set X))
    (hq₀lam : ∀ i, q₀ i = ∑ j, (lam j : ℝ) * ((cartierCoefficient (Dv i) (ξ j) : ℝ) /
      (((d : ℝ) - cartierCoefficient B (ξ j)) / d))) :
    ∃ S : Set (Fin r'), S.Nonempty ∧
      (∀ k ∈ S, ρ (ξT k) ∈ Φ ∧
        (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) +
            η / M * (cartierCoefficient Gc (ξT k) : ℝ) =
          ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (ξT k)) / d) ∧
      ∀ t : CodimensionOnePoint T,
        (∃ k ∈ S, (closure ({(t : T)} : Set T) ∩ closure ({ξT k} : Set T)).Nonempty) →
        (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
            η / M * (cartierCoefficient Gc (t : T) : ℝ) ≤
          ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (t : T)) / d ∧
        ((1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
            η / M * (cartierCoefficient Gc (t : T) : ℝ) =
          ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (t : T)) / d → ∃ k' ∈ S, (t : T) = ξT k') := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- the profile of a prime of T
  obtain ⟨P, hP⟩ : ∃ P : T → Prop, ∀ t : T, P t ↔
      ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) t : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) t) / d * q₀ i := ⟨_, fun _ => Iff.rfl⟩
  -- the comparison (28), (29) at a prime where the polytope condition holds
  have hcmp : ∀ t : CodimensionOnePoint T,
      (∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d) →
      (1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / M * (cartierCoefficient Gc (t : T) : ℝ) ≤
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ∧
      ((1 - η) * ∑ i, c i * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / M * (cartierCoefficient Gc (t : T) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d ↔ P (t : T)) := by
    intro t hpoly
    have h := isolation_coefficient_on_principalized_model ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB
      Dv hD hDnn cT t hc hq₀ hcq₀ hI hpoly hM hη0.le hη1.le nn hnn hAeff Gc hGc hGcI
    exact ⟨h.1, (h.2 hη0 hη1).trans (hP (t : T)).symm⟩
  -- a prime with profile q⁰ at whose image the polytope condition holds
  have hpolytope : ∀ t : CodimensionOnePoint T,
      (∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d) →
      P (t : T) → InSNCProfilePolytope ξ d B Dv q₀ (ρ (t : T)) := fun t hpoly hPt =>
    inSNCProfilePolytope_of_profile ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hD cT t hcq₀ hpoly
      ((hP (t : T)).mp hPt)
  -- q⁰ lies in the polytope of y
  have hqy : InSNCProfilePolytope ξ d B Dv q₀ y := by
    refine ⟨fun j => (lam j : ℝ), fun j => ?_, ?_, fun j hj => ?_, hq₀lam⟩
    · change (0 : ℝ) ≤ (lam j : ℝ)
      exact_mod_cast hlam j
    · change ∑ j, (lam j : ℝ) = 1
      exact_mod_cast hlam1
    · apply hlamy j
      intro h0
      apply hj
      change ((lam j : ℚ) : ℝ) = 0
      rw [h0, Rat.cast_zero]
  have hpolyy := hpolyΦ y hy hqy
  refine ⟨{k | ρ (ξT k) ∈ Φ ∧ P (ξT k) ∧ InSNCProfilePolytope ξ d B Dv q₀ (ρ (ξT k))}, ?_, ?_, ?_⟩
  · -- S is not empty
    obtain ⟨k, hyk, hprofk⟩ := exists_snc_member_with_profile_of_convex_combination ρ hρ ξ hinj hξ
      hsnc c₀ f₀ d hd B hB hb Dv hD hDnn hc hq₀ hcq₀ hI hM hη0 hη1 nn hnn hAeff y hpolyy cT ξT
      hinjT hξT hsncT hTB hTD Gc hGc hTG hGcI lam hlam hlam1 hlamy hq₀lam
    have hPk : P (ξT k) := (hP (ξT k)).mpr hprofk
    have hpolyk : ∀ j, ρ (ξT k) ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d := fun j hj =>
      hpolyy j (closure_minimal (Set.singleton_subset_iff.mpr hj) isClosed_closure hyk)
    have hqk := hpolytope ⟨ξT k, hξT k⟩ hpolyk hPk
    exact ⟨k, hcentre (ρ (ξT k)) ⟨y, hyk, hy⟩ hqk, hPk, hqk⟩
  · -- Ψ = A on S
    rintro k ⟨hΦk, hPk, hqk⟩
    exact ⟨hΦk, ((hcmp ⟨ξT k, hξT k⟩ (hpolyΦ (ρ (ξT k)) hΦk hqk)).2).mpr hPk⟩
  · -- the primes meeting S
    rintro t ⟨k, ⟨hΦk, hPk, hqk⟩, p', hp't, hp'k⟩
    have hspeck : ρ (ξT k) ⤳ ρ p' :=
      (specializes_iff_mem_closure.mpr hp'k).map ρ.continuous
    have hspect : ρ (t : T) ⤳ ρ p' :=
      (specializes_iff_mem_closure.mpr hp't).map ρ.continuous
    have hΦp' : ρ p' ∈ Φ := hspeck.mem_closed hΦ hΦk
    have hqp' : InSNCProfilePolytope ξ d B Dv q₀ (ρ p') :=
      inSNCProfilePolytope_of_mem_closure hqk hspeck.mem_closure
    have hpolyt : ∀ j, ρ (t : T) ∈ closure ({ξ j} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ j)) / d := fun j hj =>
      hpolyΦ (ρ p') hΦp' hqp' j
        (closure_minimal (Set.singleton_subset_iff.mpr hj) isClosed_closure hspect.mem_closure)
    obtain ⟨hle, hiff⟩ := hcmp t hpolyt
    refine ⟨hle, fun heq => ?_⟩
    have hPt : P (t : T) := hiff.mp heq
    have hqt := hpolytope t hpolyt hPt
    have hΦt : ρ (t : T) ∈ Φ := hcentre (ρ (t : T)) ⟨ρ p', hspect.mem_closure, hΦp'⟩ hqt
    -- a prime outside the family has Ψ = 0 < A
    by_contra hnot
    have hrange : (t : T) ∉ Set.range ξT := by
      rintro ⟨k', hk'⟩
      refine hnot ⟨k', ?_, hk'.symm⟩
      change ρ (ξT k') ∈ Φ ∧ P (ξT k') ∧ InSNCProfilePolytope ξ d B Dv q₀ (ρ (ξT k'))
      rw [hk']
      exact ⟨hΦt, hPt, hqt⟩
    have hA : (0 : ℝ) < ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T)) / d := by
      have h := isSNCFamily_actual_discrepancy_bound ρ hρ c₀ f₀ d hd B ξ hinj hξ hsnc hB hb cT t
      have h' : -(d : ℝ) < (cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T) : ℝ) := by exact_mod_cast h
      exact div_pos (by linarith) hdpos
    have hzero : (1 - η) * ∑ i, c i *
        (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) +
          η / M * (cartierCoefficient Gc (t : T) : ℝ) = 0 := by
      rw [hTG t hrange, Finset.sum_eq_zero fun i _ => by
        rw [hTD i t hrange, Int.cast_zero, mul_zero]]
      simp
    rw [hzero] at heq
    exact hA.ne heq

end Model

end MixedFujita

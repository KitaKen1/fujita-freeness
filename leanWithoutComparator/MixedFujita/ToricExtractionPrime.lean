/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricChartModel
public import MixedFujita.SNCModelPrimeOrders
public import MixedFujita.IsolationExtractionPrime

/-!
Existence of the extraction prime (step 12, section 6.1 of the manuscript).

Let X be smooth over a field with a simple normal crossing family ξ_1, …, ξ_r, y a point of X and
W ≠ 0 natural weights on the members of the family, zero on the members whose closure does not
contain y. On a simple normal crossing chart at y the weights are weights on the coordinates
cutting out the members through y, and the toric chart extracting the monomial valuation with
these weights is a smooth affine birational model U of X with a prime divisor e whose image
specializes to y, such that, with W = g W',

* the coefficient at e of the pullback of a Cartier divisor B supported on the family is
  Σ_j (coefficient of B at ξ_j) W'_j;
* d times the log discrepancy of e for a boundary B supported on the family with denominator d is
  Σ_j (d - coefficient of B at ξ_j) W'_j: the Jacobian inequality is an equality for e.

Consequence: the divisor S of section 6.2 is not empty. If the profile q⁰ is the profile of the
monomial valuation with weights W, that is Σ_j e_ij W_j = (Σ_j A_j W_j) q⁰_i with A_j the log
discrepancy of ξ_j, then a member of the family of the principalizing model has profile q⁰ and
its image specializes to y. No extraction prime is assumed any more.
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

/-- A sum over distinct selected indices is the whole sum when the terms outside the selection
vanish. -/
theorem option_selected_sum_eq {ι α : Type*} [Fintype ι] [Fintype α]
    (σ : ι → Option α) (hσ : ∀ i j a, σ i = some a → σ j = some a → i = j)
    (v : α → ℤ) (hv : ∀ a, v a ≠ 0 → ∃ i, σ i = some a) :
    ∑ i, (σ i).elim 0 v = ∑ a, v a := by
  classical
  have hi (i : ι) : (σ i).elim 0 v = ∑ a, if σ i = some a then v a else 0 := by
    cases h : σ i with
    | none => simp
    | some a => simp
  simp_rw [hi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : v a = 0
  · rw [ha]
    exact Finset.sum_eq_zero fun i _ => ite_self 0
  · obtain ⟨i₀, hi₀⟩ := hv a ha
    rw [Finset.sum_eq_single i₀
      (fun i _ hne => ite_eq_right (fun h => hne (hσ i i₀ a h hi₀)))
      (fun h => absurd (Finset.mem_univ i₀) h), ite_eq_left hi₀]

/-- Finitely many nonnegative rationals are natural multiples of 1/D for a common positive
natural number D. -/
theorem exists_common_denominator_nat {ι : Type*} [Fintype ι] (ω : ι → ℚ) (hω : ∀ j, 0 ≤ ω j) :
    ∃ (D : ℕ) (W : ι → ℕ), 1 ≤ D ∧ ∀ j, (W j : ℚ) = D * ω j := by
  classical
  refine ⟨∏ j, (ω j).den, fun j => ((∏ j', (ω j').den) / (ω j).den) * (ω j).num.toNat,
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun j _ => (ω j).den_nz),
    fun j => ?_⟩
  obtain ⟨m, hm⟩ : (ω j).den ∣ ∏ j', (ω j').den := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hnum : (((ω j).num.toNat : ℕ) : ℚ) = ((ω j).num : ℚ) := by
    have h : (((ω j).num.toNat : ℕ) : ℤ) = (ω j).num :=
      Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hω j))
    exact_mod_cast h
  change ((((∏ j', (ω j').den) / (ω j).den * (ω j).num.toNat : ℕ) : ℕ) : ℚ) =
    ((∏ j', (ω j').den : ℕ) : ℚ) * ω j
  rw [hm, Nat.mul_div_cancel_left m (ω j).den_pos, Nat.cast_mul, Nat.cast_mul, hnum,
    ← Rat.den_mul_eq_num (ω j)]
  ring

section Extraction

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- The extraction prime of a monomial valuation on a simple normal crossing family: for natural
weights W ≠ 0 on the members of the family, supported on the members through y, a smooth
birational model with a prime divisor e whose image specializes to y, along which the members
have orders W' with W = g W' and whose log discrepancy for every boundary supported on the family
is given by the weights. -/
theorem exists_snc_extraction_prime {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ) (y : X)
    (W : Fin r → ℕ) (hW : W ≠ 0) (hWy : ∀ j, W j ≠ 0 → y ∈ closure ({ξ j} : Set X)) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (g : ℕ) (W' : Fin r → ℕ),
      1 ≤ g ∧ (∀ j, W j = g * W' j) ∧ y ∈ closure ({σ (e : U)} : Set X) ∧
      (∀ B : CartierDivisor X, (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient B (z : X) = 0) →
        cartierCoefficient (cartierPullback σ B) (e : U) =
          ∑ j, cartierCoefficient B (ξ j) * (W' j : ℤ)) ∧
      ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X),
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient B (z : X) = 0) →
        (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n σ hσ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cU etaleCharts_cover) (e : U) =
          (d : ℤ) * ∑ j, (W' j : ℤ) - ∑ j, cartierCoefficient B (ξ j) * (W' j : ℤ) := by
  classical
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ z : CodimensionOnePoint X, IsRegularLocalRing (X.presheaf.stalk (z : X)) :=
    fun z => isSNCFamily_stalk_regular hsnc (z : X)
  have : ∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    fun z => inferInstance
  obtain ⟨c, σc, hyc, hcsnc⟩ := hsnc y
  -- the weights on the coordinates of the chart
  obtain ⟨w, hwdef⟩ : ∃ w : Fin n → ℕ, ∀ a, w a = ∑ j, if σc j = some a then W j else 0 :=
    ⟨_, fun _ => rfl⟩
  have hWnone : ∀ j, σc j = none → W j = 0 := by
    intro j hj
    by_contra h0
    have hmem : y ∈ closure ({ξ j} : Set X) ∩ c.U := ⟨hWy j h0, hyc⟩
    rw [hcsnc.2 j, hj] at hmem
    exact hmem
  have hwsome : ∀ j a, σc j = some a → w a = W j := by
    intro j a hja
    rw [hwdef a, Finset.sum_eq_single j
      (fun j' _ hne => ite_eq_right (fun h => hne (hcsnc.1 j' j a h hja)))
      (fun h => absurd (Finset.mem_univ j) h), ite_eq_left hja]
  have hwex : ∀ a, w a ≠ 0 → ∃ j, σc j = some a ∧ W j ≠ 0 := by
    intro a ha
    by_contra hno
    apply ha
    rw [hwdef a]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hja : σc j = some a
    · rw [ite_eq_left hja]
      by_contra h0
      exact hno ⟨j, hja, h0⟩
    · rw [ite_eq_right hja]
  have hw0 : w ≠ 0 := by
    obtain ⟨j₀, hj₀⟩ : ∃ j, W j ≠ 0 := by
      by_contra h
      push Not at h
      exact hW (funext h)
    cases hσ : σc j₀ with
    | none => exact absurd (hWnone j₀ hσ) hj₀
    | some a =>
      intro h
      apply hj₀
      rw [← hwsome j₀ a hσ, h]
      rfl
  have hwy : ∀ a, w a ≠ 0 →
      ¬ IsUnit (X.presheaf.germ c.U y hyc (c.coords (MvPolynomial.X a))) := by
    intro a ha hu
    obtain ⟨j, hja, hj⟩ := hwex a ha
    have hmem : y ∈ closure ({ξ j} : Set X) ∩ c.U := ⟨hWy j hj, hyc⟩
    rw [hcsnc.2 j, hja, Option.elim_some, Scheme.zeroLocus_singleton] at hmem
    exact hmem.1 ((X.mem_basicOpen _ y hyc).mpr hu)
  obtain ⟨U, hUint, hUnoeth, hUover, hUsm, σ, hσdom, hσover, hσbij, cU, e, g, w', hg, hww',
    hcoh, he, hclos, hord, hjac⟩ := exists_toric_extraction_model c y hyc w hw0 hwy
  -- the orders of the members of the family
  have hσe : σ e ∈ c.U := (specializes_iff_mem_closure.mpr hclos).mem_open c.U.isOpen hyc
  have hW' : ∀ j, W j = g * (σc j).elim 0 w' := by
    intro j
    cases hσ : σc j with
    | none => rw [hWnone j hσ, Option.elim_none, mul_zero]
    | some a => rw [← hwsome j a hσ, hww' a, Option.elim_some]
  have hcomp : ∀ j, U.ord ((dominantFunctionFieldMap σ).hom
      (sncChartComponentEquation c σc j : X.functionField)) e =
        (((σc j).elim 0 w' : ℕ) : ℤ) := by
    intro j
    cases hσ : σc j with
    | none =>
      simp only [sncChartComponentEquation, hσ, Option.elim_none, Units.val_one, map_one,
        TauCeti.AlgebraicGeometry.Scheme.ord_one, Nat.cast_zero]
    | some a =>
      simp only [sncChartComponentEquation, hσ, Option.elim_some]
      exact hord a
  have hcoef : ∀ B : CartierDivisor X, (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient B (z : X) = 0) →
      cartierCoefficient (cartierPullback σ B) e =
        ∑ j, cartierCoefficient B (ξ j) * (((σc j).elim 0 w' : ℕ) : ℤ) := by
    intro B hsupport
    obtain ⟨f, hf, u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm B c ξ hinj hξ σc
      hcsnc hsupport (σ e) hσe
    rw [cartierPullback_coefficient_of_local_product σ B ⟨e, hcoh⟩ f hf u _ _ hu]
    exact Finset.sum_congr rfl fun j _ => by rw [hcomp j]
  have hsum : ∑ a, (w' a : ℤ) = ∑ j, (((σc j).elim 0 w' : ℕ) : ℤ) := by
    have hcast : ∀ j, (((σc j).elim 0 w' : ℕ) : ℤ) = (σc j).elim 0 (fun a => (w' a : ℤ)) := by
      intro j
      cases σc j <;> simp
    rw [Finset.sum_congr rfl fun j _ => hcast j]
    refine (option_selected_sum_eq σc hcsnc.1 (fun a => (w' a : ℤ)) fun a ha => ?_).symm
    have hw'a : w' a ≠ 0 := fun h => ha (by rw [h, Nat.cast_zero])
    have hwa : w a ≠ 0 := by
      rw [hww' a]
      exact Nat.mul_ne_zero (by omega) hw'a
    obtain ⟨j, hja, -⟩ := hwex a hwa
    exact ⟨j, hja⟩
  refine ⟨U, hUint, hUnoeth, hUover, hUsm, σ, hσdom, hσover, hσbij, cU, ⟨e, hcoh⟩, g,
    fun j => (σc j).elim 0 w', hg, hW', hclos, hcoef, ?_⟩
  intro c₀ f₀ d B hsupport
  rw [logDiscrepancyDivisor_boundary_add, cartierCoefficient_sub, cartierCoefficient_nsmul,
    hcoef B hsupport]
  have hloc := relativeCanonicalDivisor_isLocalEquationAt σ c₀ etaleCharts_cover cU
    etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective σ hσbij c₀ cU) e c hσe cU he
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord hloc, IsUnit.unit_spec, hjac, hsum]
  ring

end Extraction

section Nonempty

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The divisor S is not empty, without an assumed extraction. Let (X, B) be a simple normal
crossing pair, D_i divisors supported on its family, and T a proper smooth model with a simple
normal crossing family supporting the crepant boundary, the pullbacks of the D_i and the divisor
G whose ideal sheaf is the inverse image of the sum of the ideal sheaves of the (M/q⁰_i) D_i. Let
y be a point of X such that c · z_j ≤ 1 for every member ξ_j of the family of X whose closure
contains y. If q⁰ is the profile of the monomial valuation with natural weights W ≠ 0 on the
members through y, that is Σ_j e_ij W_j = (Σ_j A_j W_j) q⁰_i, then some member of the family of T
has profile q⁰ and its image specializes to y. -/
theorem exists_snc_member_with_profile_of_weights {ι : Type*} [Fintype ι] {r : ℕ}
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
    (hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective) (y : X)
    (hpoly : ∀ j, y ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
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
    (W : Fin r → ℕ) (hW : W ≠ 0) (hWy : ∀ j, W j ≠ 0 → y ∈ closure ({ξ j} : Set X))
    (hWprof : ∀ i, ∑ j, (cartierCoefficient (Dv i) (ξ j) : ℝ) * (W j : ℝ) =
      (∑ j, ((d : ℝ) - cartierCoefficient B (ξ j)) / d * (W j : ℝ)) * q₀ i) :
    ∃ k : Fin r', y ∈ closure ({ρ (ξT k)} : Set X) ∧
      ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d * q₀ i := by
  obtain ⟨U, hUint, hUnoeth, hUover, hUsm, σ, hσdom, hσover, hσbij, cU, e, g, W', hg, hWW',
    hclos, hcoef, hdisc⟩ := exists_snc_extraction_prime ξ hinj hξ hsnc y W hW hWy
  refine exists_snc_member_with_profile_of_extraction_prime ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB
    hb Dv hD hDnn hc hq₀ hcq₀ hI hM hη0 hη1 nn hnn hAeff y hpoly cT ξT hinjT hξT hsncT hTB hTD
    Gc hGc hTG hGcI σ hσbij cU e hclos fun i => ?_
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have h1 : (cartierCoefficient (cartierPullback σ (Dv i)) (e : U) : ℝ) =
      ∑ j, (cartierCoefficient (Dv i) (ξ j) : ℝ) * (W' j : ℝ) := by
    rw [hcoef (Dv i) (hD i)]
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  have h2 : (d : ℝ) + (cartierCoefficient (logDiscrepancyDivisor n σ hσbij c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cU etaleCharts_cover) (e : U) : ℝ) =
        (d : ℝ) * ∑ j, (W' j : ℝ) - ∑ j, (cartierCoefficient B (ξ j) : ℝ) * (W' j : ℝ) := by
    have h := congrArg (Int.cast : ℤ → ℝ) (hdisc c₀ f₀ d B hB)
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_natCast] at h
    exact h
  have hE : ∑ j, (cartierCoefficient (Dv i) (ξ j) : ℝ) * (W j : ℝ) =
      (g : ℝ) * ∑ j, (cartierCoefficient (Dv i) (ξ j) : ℝ) * (W' j : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hWW' j]
      push_cast
      ring
  have hA : ∑ j, ((d : ℝ) - cartierCoefficient B (ξ j)) / d * (W j : ℝ) =
      (g : ℝ) * (((d : ℝ) * ∑ j, (W' j : ℝ) -
        ∑ j, (cartierCoefficient B (ξ j) : ℝ) * (W' j : ℝ)) / d) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [hWW' j]
      push_cast
      ring
  have h3 := hWprof i
  rw [hE, hA, mul_assoc] at h3
  rw [h1, h2]
  exact mul_left_cancel₀ hgpos.ne' h3

/-- The divisor S is not empty when the profile is a rational point of the polytope. Let q⁰ be a
rational convex combination Σ_j λ_j z_j of the profiles z_j = (e_ij / A_j)_i of the members of the
family of X whose closure contains y, A_j being the log discrepancy of ξ_j. Then q⁰ is the profile
of a monomial valuation, and some member of the family of the principalizing model T has profile
q⁰ and its image specializes to y. -/
theorem exists_snc_member_with_profile_of_convex_combination {ι : Type*} [Fintype ι] {r : ℕ}
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
    (hAeff : ∀ k : {i // i ∈ profileSupport q₀}, (nn k.1 • Dv k.1).IsEffective) (y : X)
    (hpoly : ∀ j, y ∈ closure ({ξ j} : Set X) →
      ∑ i, c i * (cartierCoefficient (Dv i) (ξ j) : ℝ) ≤
        ((d : ℝ) - cartierCoefficient B (ξ j)) / d)
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
    ∃ k : Fin r', y ∈ closure ({ρ (ξT k)} : Set X) ∧
      ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d * q₀ i := by
  classical
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hbpos : ∀ j, (0 : ℝ) < (d : ℝ) - cartierCoefficient B (ξ j) := fun j => by
    have h' : ((cartierCoefficient B (ξ j) : ℤ) : ℝ) < (d : ℝ) := by exact_mod_cast hb j
    linarith
  have hbposQ : ∀ j, (0 : ℚ) < (d : ℚ) - cartierCoefficient B (ξ j) := fun j => by
    have h' : ((cartierCoefficient B (ξ j) : ℤ) : ℚ) < (d : ℚ) := by exact_mod_cast hb j
    linarith
  obtain ⟨Dn, W, hDn, hWdef⟩ := exists_common_denominator_nat
    (fun j => lam j / ((d : ℚ) - cartierCoefficient B (ξ j)))
    (fun j => div_nonneg (hlam j) (hbposQ j).le)
  have hDnpos : (0 : ℝ) < Dn := by exact_mod_cast hDn
  have hWreal : ∀ j, (W j : ℝ) =
      (Dn : ℝ) * ((lam j : ℝ) / ((d : ℝ) - cartierCoefficient B (ξ j))) := by
    intro j
    have h := congrArg (fun q : ℚ => (q : ℝ)) (hWdef j)
    simpa using h
  have hlamR : ∑ j, (lam j : ℝ) = 1 := by exact_mod_cast hlam1
  refine exists_snc_member_with_profile_of_weights ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB hb Dv hD
    hDnn hc hq₀ hcq₀ hI hM hη0 hη1 nn hnn hAeff y hpoly cT ξT hinjT hξT hsncT hTB hTD Gc hGc hTG
    hGcI W ?_ ?_ ?_
  · obtain ⟨j, hj⟩ : ∃ j, lam j ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : ∑ j, lam j = 0 := Finset.sum_eq_zero fun j _ => h j
      rw [hlam1] at h0
      exact one_ne_zero h0
    intro hW0
    have h0 : (W j : ℝ) = 0 := by rw [hW0]; simp
    rw [hWreal j] at h0
    have hjR : (lam j : ℝ) ≠ 0 := by exact_mod_cast hj
    rcases mul_eq_zero.mp h0 with h | h
    · exact hDnpos.ne' h
    · rcases div_eq_zero_iff.mp h with h | h
      · exact hjR h
      · exact (hbpos j).ne' h
  · intro j hWj
    apply hlamy
    intro hl
    apply hWj
    have h0 : (W j : ℝ) = 0 := by rw [hWreal j, hl]; simp
    exact_mod_cast h0
  · intro i
    have hsumA : ∑ j, ((d : ℝ) - cartierCoefficient B (ξ j)) / d * (W j : ℝ) = (Dn : ℝ) / d := by
      have h1 : ∀ j, ((d : ℝ) - cartierCoefficient B (ξ j)) / d * (W j : ℝ) =
          (Dn : ℝ) / d * (lam j : ℝ) := by
        intro j
        rw [hWreal j]
        have := (hbpos j).ne'
        field_simp
      rw [Finset.sum_congr rfl fun j _ => h1 j, ← Finset.mul_sum, hlamR, mul_one]
    rw [hsumA, hq₀lam i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hWreal j]
    have := (hbpos j).ne'
    field_simp

end Nonempty

end MixedFujita

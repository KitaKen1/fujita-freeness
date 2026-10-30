/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.IsolationCoefficientOnModel
public import MixedFujita.PrincipalizedIdealCoefficients

/-!
The divisor S of section 6.2 of the manuscript is not empty (step 12).

Let T be a proper smooth birational model of X whose crepant boundary is supported on a simple
normal crossing family ξ_s, and let x be a prime divisor of an arbitrary smooth birational test
model U of X. The valuative criterion and spreading out give a morphism from a neighbourhood of
x to T; the members of the family have orders o_s ≥ 0 along x through it. These orders compute
the coefficient at x of the pullback of every Cartier divisor of X whose pullback to T is
supported on the family, the minimum formula for a principalized sum of ideal sheaves, and they
satisfy Σ_s (log discrepancy of ξ_s) o_s ≤ (log discrepancy of x).

Consequence. Let (X, B) be a simple normal crossing pair, D_i divisors supported on its family,
and T a model principalizing the sum of the ideal sheaves of the divisors (M/q⁰_i) D_i, on which
the inequality (28) holds near a point y. If some smooth birational test model has a prime
divisor x of profile q⁰ whose image specializes to y, then a member of the family of T has
profile q⁰ and its image specializes to y: all inequalities in

  A_x = Σ_s Ψ_s o_s ≤ Σ_s A_s o_s ≤ A_x

are equalities, so Ψ_s = A_s whenever o_s > 0, and equality in (28) forces the profile. The
extracted divisor need not be transferred to T, and no tower of blow-ups is used: an extraction
on any test model, proper or not, is enough.
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

section TestPrime

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The orders of the simple normal crossing family of a proper smooth model along a prime
divisor x of an arbitrary smooth birational test model: nonnegative integers o_s, zero unless the
closure of ξ_s contains a fixed point of the model over the image of x, which compute the
coefficient at x of the pullback of every Cartier divisor whose pullback to the model is
supported on the family, satisfy the minimum formula for a divisor G of the model whose ideal
sheaf is the inverse image of a sum of ideal sheaves of effective Cartier divisors, and bound the
log discrepancy of x from below. -/
theorem exists_snc_orders_at_test_prime {κ : Type*} [Finite κ] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (A : κ → CartierDivisor X) (hA : ∀ k, (A k).IsEffective) (G : CartierDivisor T)
    (hG : G.IsEffective)
    (hGsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient G (t : T) = 0)
    (hGI : effectiveCartierIdealSheaf G hG =
      (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (x : CodimensionOnePoint U) :
    ∃ (o : Fin r → ℤ) (t₀ : T), ρ t₀ = σ (x : U) ∧ (∀ s, 0 ≤ o s) ∧
      (∀ s, o s ≠ 0 → t₀ ∈ closure ({ξ s} : Set T)) ∧
      (∀ D' : CartierDivisor X, (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback ρ D') (t : T) = 0) →
        cartierCoefficient (cartierPullback σ D') (x : U) =
          ∑ s, cartierCoefficient (cartierPullback ρ D') (ξ s) * o s) ∧
      ((∀ k, ∑ s, cartierCoefficient G (ξ s) * o s ≤
          cartierCoefficient (cartierPullback σ (A k)) (x : U)) ∧
        ∃ k, ∑ s, cartierCoefficient G (ξ s) * o s =
          cartierCoefficient (cartierPullback σ (A k)) (x : U)) ∧
      (d : ℤ) * ∑ s, o s -
          ∑ s, cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s) * o s ≤
        (d : ℤ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U) := by
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  let : Nonempty W := ⟨⟨(x : U), hx⟩⟩
  let : IsIntegral W.toScheme := hW
  let : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  have : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsDominant α := hdom
  let : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨(x : U), hx⟩
  have hιbij : Function.Bijective (W.ι.stalkMap w) :=
    ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w)
  have hw : Order.coheight w = 1 :=
    (coheight_eq_of_stalkMap_bijective W.ι w hιbij).trans x.property
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ e : EtaleChart K W.toScheme n, w ∈ e.U from
      TopologicalSpace.Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
          TopologicalSpace.Opens.mem_top w))⟩
  have : Smooth (W.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdvrW := smoothOverField_codimensionOne_stalk_DVR (K := K) p
  have hdvrU : IsDiscreteValuationRing (U.presheaf.stalk (W.ι (p : W.toScheme))) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨o, ho, hosupp, hpull, hdisc⟩ := exists_snc_orders_at_prime α hα ξ hinj hξ hsnc p
  -- coefficients on the neighbourhood are the coefficients on the test model
  have htr : ∀ D' : CartierDivisor X,
      cartierCoefficient (cartierPullback (W.ι ≫ σ) D') (p : W.toScheme) =
        cartierCoefficient (cartierPullback σ D') (x : U) := by
    intro D'
    rw [cartierPullback_comp σ W.ι D']
    exact cartierCoefficient_pullback_of_stalkMap_bijective W.ι p x.property hιbij
      (cartierPullback σ D')
  refine ⟨o, α w, ?_, ho, hosupp, ?_, ?_, ?_⟩
  · have h := Scheme.Hom.comp_apply α ρ w
    rw [hcomm, Scheme.Hom.comp_apply] at h
    exact h.symm
  · intro D' hD'
    have h1 := hpull (cartierPullback ρ D') hD'
    rw [← cartierPullback_comp ρ α D'] at h1
    have h2 : cartierCoefficient (cartierPullback (W.ι ≫ σ) D') (p : W.toScheme) =
        ∑ s, cartierCoefficient (cartierPullback ρ D') (ξ s) * o s := by
      simpa only [hcomm] using h1
    rw [← htr D']
    exact h2
  · have hG' := cartierPullback_isEffective α G hG
    have hI : effectiveCartierIdealSheaf (cartierPullback α G) hG' =
        (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap (W.ι ≫ σ) := by
      rw [effectiveCartierIdealSheaf_cartierPullback α G hG, hGI,
        ← Scheme.IdealSheafData.comap_comp, hcomm]
    have hmin := cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
      (W.ι ≫ σ) A hA (cartierPullback α G) hG' hI (p : W.toScheme)
    rw [← hpull G hGsupp]
    simpa only [htr] using hmin
  · have h := hdisc cT (crepantPullbackFormUnit ρ hρ c f cT) d
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) hsupport cW
    rw [crepantBoundaryCartier_smooth_recombine,
      ← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover] at h
    have h' : (d : ℤ) * ∑ s, o s -
          ∑ s, cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s) * o s ≤
        (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
          (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι)
          c f d D cW etaleCharts_cover) (p : W.toScheme) := by
      simpa only [hcomm] using h
    have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
      σ W.ι hσ hι c f d D cU cW p x.property hιbij
    rw [heq] at h'
    exact h'

end TestPrime

section Arithmetic

/-- If Σ_s Ψ_s o_s = A, Σ_s A_s o_s ≤ A, the weights o_s are nonnegative, Ψ_s ≤ A_s whenever
o_s ≠ 0, and A > 0, then Ψ_s = A_s for some s with o_s ≠ 0. -/
theorem exists_index_eq_of_weighted_sum_eq {τ : Type*} [Fintype τ] {o As Ψs : τ → ℝ} {Ae : ℝ}
    (ho : ∀ s, 0 ≤ o s) (hΨ : ∀ s, o s ≠ 0 → Ψs s ≤ As s) (hsum : ∑ s, As s * o s ≤ Ae)
    (hΨe : ∑ s, Ψs s * o s = Ae) (hAe : 0 < Ae) : ∃ s, o s ≠ 0 ∧ Ψs s = As s := by
  have hterm : ∀ s, 0 ≤ (As s - Ψs s) * o s := by
    intro s
    by_cases hs : o s = 0
    · rw [hs, mul_zero]
    · exact mul_nonneg (sub_nonneg.mpr (hΨ s hs)) (ho s)
  have hzero : ∑ s, (As s - Ψs s) * o s = 0 := by
    have hsplit : ∑ s, (As s - Ψs s) * o s = ∑ s, As s * o s - ∑ s, Ψs s * o s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hle : ∑ s, (As s - Ψs s) * o s ≤ 0 := by
      rw [hsplit, hΨe]
      linarith
    exact le_antisymm hle (Finset.sum_nonneg fun s _ => hterm s)
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun s _ => hterm s).mp hzero
  obtain ⟨s, hs⟩ : ∃ s, o s ≠ 0 := by
    by_contra hno
    have hno' : ∀ s, o s = 0 := fun s => by_contra fun h => hno ⟨s, h⟩
    have h0 : ∑ s, Ψs s * o s = 0 := Finset.sum_eq_zero fun s _ => by rw [hno' s, mul_zero]
    rw [h0] at hΨe
    exact hAe.ne hΨe
  refine ⟨s, hs, ?_⟩
  have h := (mul_eq_zero.mp (hall s (Finset.mem_univ s))).resolve_right hs
  linarith

end Arithmetic

section Extraction

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

/-- The divisor S is not empty. Let (X, B) be a simple normal crossing pair, D_i divisors
supported on its family, and T a proper smooth model with a simple normal crossing family
supporting the crepant boundary, the pullbacks of the D_i and the divisor G whose ideal sheaf is
the inverse image of the sum of the ideal sheaves of the (M/q⁰_i) D_i. Let y be a point of X such
that c · z_j ≤ 1 for every member ξ_j of the family of X whose closure contains y. If a smooth
birational test model has a prime divisor e of profile q⁰ whose image specializes to y, then some
member of the family of T has profile q⁰ and its image specializes to y. -/
theorem exists_snc_member_with_profile_of_extraction_prime {ι : Type*} [Fintype ι] {r : ℕ}
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
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U)
    (hye : y ∈ closure ({σ (e : U)} : Set X))
    (hprof : ∀ i, (cartierCoefficient (cartierPullback σ (Dv i)) (e : U) : ℝ) =
      ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n σ hσ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cU etaleCharts_cover) (e : U)) / d * q₀ i) :
    ∃ k : Fin r', y ∈ closure ({ρ (ξT k)} : Set X) ∧
      ∀ i, (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT k) : ℝ) =
        ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT k)) / d * q₀ i := by
  classical
  obtain ⟨o, t₀, ht₀, ho, hosupp, hpullD, ⟨-, kmin, hkmin⟩, hdisc⟩ :=
    exists_snc_orders_at_test_prime ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) cT ξT hinjT hξT
      hsncT hTB (fun k : {i // i ∈ profileSupport q₀} => nn k.1 • Dv k.1) hAeff Gc hGc hTG hGcI
      σ hσ cU e
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- real names for the integers involved
  obtain ⟨oR, hoR⟩ : ∃ oR : Fin r' → ℝ, ∀ s, oR s = (o s : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨vT, hvT⟩ : ∃ vT : ι → Fin r' → ℝ, ∀ i s,
      vT i s = (cartierCoefficient (cartierPullback ρ (Dv i)) (ξT s) : ℝ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨gT, hgT⟩ : ∃ gT : Fin r' → ℝ, ∀ s, gT s = (cartierCoefficient Gc (ξT s) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨δT, hδT⟩ : ∃ δT : Fin r' → ℝ, ∀ s,
      δT s = (cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (ξT s) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨ve, hve⟩ : ∃ ve : ι → ℝ, ∀ i,
      ve i = (cartierCoefficient (cartierPullback σ (Dv i)) (e : U) : ℝ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ae, hAe⟩ : ∃ Ae : ℝ, Ae = ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n σ hσ
      c₀ f₀ d (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cU etaleCharts_cover) (e : U)) / d := ⟨_, rfl⟩
  have hprofR : ∀ i, ve i = Ae * q₀ i := fun i => by rw [hve i, hAe]; exact hprof i
  have hoR0 : ∀ s, 0 ≤ oR s := fun s => by rw [hoR s]; exact_mod_cast ho s
  have hoRne : ∀ s, oR s ≠ 0 → o s ≠ 0 := by
    intro s hs h0
    apply hs
    rw [hoR s, h0, Int.cast_zero]
  -- positivity of the log discrepancy of the extraction prime
  have hAe_pos : 0 < Ae := by
    have h := isSNCFamily_actual_discrepancy_bound σ hσ c₀ f₀ d hd B ξ hinj hξ hsnc hB hb cU e
    have h' : -(d : ℝ) < (cartierCoefficient (logDiscrepancyDivisor n σ hσ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cU etaleCharts_cover) (e : U) : ℝ) := by exact_mod_cast h
    rw [hAe]
    exact div_pos (by linarith) hdpos
  -- pullback coefficients of the D_i at the extraction prime
  have hvesum : ∀ i, ve i = ∑ s, vT i s * oR s := by
    intro i
    rw [hve i, hpullD (Dv i) (hTD i)]
    push_cast
    exact Finset.sum_congr rfl fun s _ => by rw [hvT i s, hoR s]
  -- the coefficient of G at the extraction prime
  have hge : ∑ s, gT s * oR s = M * Ae := by
    have h1 : ∑ s, gT s * oR s =
        ((cartierCoefficient (cartierPullback σ (nn kmin.1 • Dv kmin.1)) (e : U) : ℤ) : ℝ) := by
      rw [← hkmin]
      push_cast
      exact Finset.sum_congr rfl fun s _ => by rw [hgT s, hoR s]
    have hpos := mem_profileSupport.mp kmin.2
    rw [h1, cartierPullback_nsmul, cartierCoefficient_nsmul]
    push_cast
    rw [← hve kmin.1, hprofR kmin.1, hnn kmin.1 kmin.2]
    field_simp
  -- the sum of the log discrepancies
  have hbT : ∀ s, cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cT etaleCharts_cover) (ξT s) = -cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (ξT s) := by
    intro s
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
  have hsum : ∑ s, ((d : ℝ) + δT s) / d * oR s ≤ Ae := by
    simp only [hbT] at hdisc
    have h' : (d : ℝ) * ∑ s, (o s : ℝ) - ∑ s, -(cartierCoefficient (logDiscrepancyDivisor n ρ hρ
          c₀ f₀ d (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (ξT s) : ℝ) * (o s : ℝ) ≤
        (d : ℝ) + (cartierCoefficient (logDiscrepancyDivisor n σ hσ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cU etaleCharts_cover) (e : U) : ℝ) := by
      exact_mod_cast hdisc
    rw [hAe, le_div_iff₀ hdpos]
    refine le_trans (le_of_eq ?_) h'
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hδT s, hoR s]
    field_simp
    ring
  -- the images of the members with nonzero order specialize to y
  have hspec : ∀ s, o s ≠ 0 → y ∈ closure ({ρ (ξT s)} : Set X) := by
    intro s hs
    have h1 : ρ t₀ ∈ closure ({ρ (ξT s)} : Set X) := by
      have h := image_closure_subset_closure_image ρ.continuous
        (Set.mem_image_of_mem ρ (hosupp s hs))
      rwa [Set.image_singleton] at h
    rw [ht₀] at h1
    exact closure_minimal (Set.singleton_subset_iff.mpr h1) isClosed_closure hye
  -- the inequality (28) and its equality case at these members
  have hmodel := fun (s : Fin r') (hs : o s ≠ 0) =>
    isolation_coefficient_on_principalized_model ρ hρ ξ hinj hξ hsnc c₀ f₀ d hd B hB Dv hD hDnn
      cT ⟨ξT s, hξT s⟩ hc hq₀ hcq₀ hI
      (fun j hj => hpoly j (closure_minimal (Set.singleton_subset_iff.mpr hj) isClosed_closure
        (hspec s hs))) hM hη0.le hη1.le nn hnn hAeff Gc hGc hGcI
  have hle : ∀ s, oR s ≠ 0 →
      (1 - η) * ∑ i, c i * vT i s + η / M * gT s ≤ ((d : ℝ) + δT s) / d := by
    intro s hs
    simp only [hvT, hgT, hδT]
    exact (hmodel s (hoRne s hs)).1
  -- the weighted sum of the coefficients of Ψ is the log discrepancy of the extraction prime
  have hΨe : ∑ s, ((1 - η) * ∑ i, c i * vT i s + η / M * gT s) * oR s = Ae := by
    have h1 : ∑ s, ((1 - η) * ∑ i, c i * vT i s + η / M * gT s) * oR s =
        (1 - η) * ∑ i, c i * ∑ s, vT i s * oR s + η / M * ∑ s, gT s * oR s := by
      have hterm : ∀ s, ((1 - η) * ∑ i, c i * vT i s + η / M * gT s) * oR s =
          (1 - η) * ∑ i, c i * (vT i s * oR s) + η / M * (gT s * oR s) := by
        intro s
        rw [add_mul, mul_assoc, Finset.sum_mul, mul_assoc]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_comm]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have h2 : ∑ i, c i * ∑ s, vT i s * oR s = Ae := by
      calc ∑ i, c i * ∑ s, vT i s * oR s = ∑ i, c i * (Ae * q₀ i) :=
            Finset.sum_congr rfl fun i _ => by rw [← hvesum i, hprofR i]
        _ = Ae * ∑ i, c i * q₀ i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = Ae := by rw [hcq₀, mul_one]
    rw [h1, h2, hge]
    field_simp
    ring
  obtain ⟨s, hs, hΨA⟩ := exists_index_eq_of_weighted_sum_eq hoR0 hle hsum hΨe hAe_pos
  have hs' : o s ≠ 0 := hoRne s hs
  refine ⟨s, hspec s hs', ?_⟩
  simp only [hvT, hgT, hδT] at hΨA
  exact ((hmodel s hs').2 hη0 hη1).mp hΨA

end Extraction

end MixedFujita

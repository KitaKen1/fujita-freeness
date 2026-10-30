/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorSemigroup
public import MixedFujita.WeightedMonomialOrder
public import MixedFujita.GradedSlices

/-!
The count #G_0(h) ≥ I_W(h) of §5.2. Split the Taylor variables at the centre into the normal
directions `Fin r` (crossing and fibre coordinates) and the tangent directions `Fin (d + 1)` of
W. Suppose the exponents of old weight zero form an initial segment of the monomial order, the
coefficients of every section there vanish unless the normal part is zero (the restriction to the
stratum comes from W), and on the tangent exponents they are the Taylor coefficients of the
restriction to W. Then every possible initial exponent of the restricted sections is an initial
exponent of the sections with zero normal part, so the central slice G_0(h) has at least as many
points as the restriction image has dimensions. A section whose Taylor expansion is a unit times
a product of tangent coordinates puts the cube {0,1}^(d+1) into one central slice, and a root
bound for the restriction image becomes the central-slice input of the slice growth (17) and the
moment growth (18). The geometric factorization of the restriction through W is an input.
-/

@[expose] public section

namespace MixedFujita

section Abstract

variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The coefficients of `f` on `S`, extended by zero. -/
noncomputable def maskedCoefficientMap (f : V →ₗ[K] (α → K)) (S : Set α) :
    V →ₗ[K] (α → K) where
  toFun v := S.indicator (f v)
  map_add' v w := by
    funext a
    by_cases ha : a ∈ S
    · simp only [map_add, Pi.add_apply, Set.indicator_of_mem ha]
    · simp only [Pi.add_apply, Set.indicator_of_notMem ha, add_zero]
  map_smul' c v := by
    funext a
    by_cases ha : a ∈ S
    · simp only [map_smul, Pi.smul_apply, Set.indicator_of_mem ha, RingHom.id_apply]
    · simp only [Pi.smul_apply, Set.indicator_of_notMem ha, smul_zero, RingHom.id_apply]

theorem maskedCoefficientMap_apply (f : V →ₗ[K] (α → K)) (S : Set α) (v : V) :
    maskedCoefficientMap f S v = S.indicator (f v) := rfl

variable [LinearOrder α]

/-- Initial indices depend only on the image vectors. -/
theorem initialIndexSet_range_subtype (g : V →ₗ[K] (α → K)) :
    initialIndexSet (LinearMap.range g).subtype = initialIndexSet g := by
  ext p
  constructor
  · rintro ⟨⟨_, v, rfl⟩, h⟩
    exact ⟨v, h⟩
  · rintro ⟨v, h⟩
    exact ⟨⟨g v, v, rfl⟩, h⟩

theorem initialIndexSet_ncard_eq_finrank_range [FiniteDimensional K V] [WellFoundedLT α]
    (g : V →ₗ[K] (α → K)) :
    (initialIndexSet g).ncard = Module.finrank K (LinearMap.range g) := by
  rw [← initialIndexSet_range_subtype]
  exact initialIndexSet_card _ (Submodule.injective_subtype _)

/-- An initial index of the masked coefficients is an initial index of the coefficients, when
`S` lies in an initial segment `Z` on which the coefficients vanish off `S`. -/
theorem initialIndexSet_masked_subset (f : V →ₗ[K] (α → K)) {S Z : Set α} (hSZ : S ⊆ Z)
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → a < b) (hzero : ∀ v, ∀ a ∈ Z, a ∉ S → f v a = 0) :
    initialIndexSet (maskedCoefficientMap f S) ⊆ initialIndexSet f ∩ S := by
  rintro a ⟨v, hv0, hv⟩
  have haS : a ∈ S := by
    by_contra haS
    exact hv0 (by rw [maskedCoefficientMap_apply, Set.indicator_of_notMem haS])
  refine ⟨⟨v, ?_, fun b hb => ?_⟩, haS⟩
  · rwa [maskedCoefficientMap_apply, Set.indicator_of_mem haS] at hv0
  · have hb' := hv b hb
    rw [maskedCoefficientMap_apply] at hb'
    by_cases hbS : b ∈ S
    · rwa [Set.indicator_of_mem hbS] at hb'
    · by_cases hbZ : b ∈ Z
      · exact hzero v b hbZ hbS
      · exact absurd hb (not_lt.mpr (hZ a (hSZ haS) b hbZ).le)

/-- The slice `S` of initial indices has at least the dimension of the masked image. -/
theorem finrank_masked_le_ncard [FiniteDimensional K V] [WellFoundedLT α]
    (f : V →ₗ[K] (α → K)) {S Z : Set α} (hSZ : S ⊆ Z)
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → a < b) (hzero : ∀ v, ∀ a ∈ Z, a ∉ S → f v a = 0) :
    Module.finrank K (LinearMap.range (maskedCoefficientMap f S)) ≤
      (initialIndexSet f ∩ S).ncard := by
  rw [← initialIndexSet_ncard_eq_finrank_range]
  exact Set.ncard_le_ncard (initialIndexSet_masked_subset f hSZ hZ hzero)
    ((initialIndexSet_finite f).inter_of_left S)

end Abstract

section PowerSeries

variable {K : Type*} [Field K]

/-- A tangent exponent, with zero normal part. -/
def tangentExponent (r : ℕ) {d : ℕ} (β : Fin (d + 1) →₀ ℕ) : (Fin r ⊕ Fin (d + 1)) →₀ ℕ :=
  Finsupp.sumElim 0 β

theorem tangentExponent_injective (r : ℕ) {d : ℕ} :
    Function.Injective (tangentExponent r (d := d)) := by
  intro β γ h
  ext i
  exact congrArg (fun a : (Fin r ⊕ Fin (d + 1)) →₀ ℕ => a (Sum.inr i)) h

theorem splitTaylorExponent_tangentExponent (r : ℕ) {d : ℕ} (β : Fin (d + 1) →₀ ℕ) :
    splitTaylorExponent r d (tangentExponent r β) = (0, fun i => (β i : ℤ)) := by
  apply Prod.ext <;> funext i <;> rfl

/-- An exponent with zero normal part is a tangent exponent. -/
theorem exists_tangentExponent_eq {r d : ℕ} {a : (Fin r ⊕ Fin (d + 1)) →₀ ℕ}
    (h : ∀ i, a (Sum.inl i) = 0) : ∃ β, tangentExponent r β = a := by
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => a (Sum.inr i)), ?_⟩
  ext (i | i)
  · exact (h i).symm
  · rfl

theorem realExponentWeight_tangentExponent {r d : ℕ} {w : Fin r ⊕ Fin (d + 1) → ℝ}
    (hw : ∀ i, w (Sum.inr i) = 0) (β : Fin (d + 1) →₀ ℕ) :
    realExponentWeight w (tangentExponent r β) = 0 := by
  change ∑ i, w i * ((tangentExponent r β i : ℕ) : ℝ) = 0
  rw [Fintype.sum_sum_type]
  simp [tangentExponent, hw]

theorem realExponentWeight_nonneg {σ : Type*} [Fintype σ] {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (a : σ →₀ ℕ) : 0 ≤ realExponentWeight w a :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)

/-- Exponents of weight zero come first in the weighted order. -/
theorem weightedMonomialOrder_zeroWeight_lt {σ : Type*} [Fintype σ] (m : MonomialOrder σ)
    (w : σ → ℝ) (v : σ → ℕ) (hw : ∀ i, 0 ≤ w i) {a b : σ →₀ ℕ}
    (ha : realExponentWeight w a = 0) (hb : realExponentWeight w b ≠ 0) :
    (weightedMonomialOrder m w v hw).toSyn a < (weightedMonomialOrder m w v hw).toSyn b := by
  rw [weightedMonomialOrder_lt_iff]
  left
  rw [ha]
  exact lt_of_le_of_ne (realExponentWeight_nonneg hw b) (Ne.symm hb)

/-- A unit times a monomial has that monomial as its initial monomial, in any monomial order. -/
theorem isInitialMonomial_unit_mul_monomial {σ : Type*} (m : MonomialOrder σ)
    {u : MvPowerSeries σ K} (hu : MvPowerSeries.constantCoeff u ≠ 0) (e : σ →₀ ℕ) :
    IsInitialMonomial m (u * MvPowerSeries.monomial e 1) e := by
  classical
  have h0 : IsInitialMonomial m u 0 := by
    refine ⟨by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply], fun q hq => ?_⟩
    rw [map_zero] at hq
    exact absurd hq (not_lt.mpr (m.zero_le _))
  have he : IsInitialMonomial m (MvPowerSeries.monomial e (1 : K)) e := by
    refine ⟨by rw [MvPowerSeries.coeff_monomial_same]; exact one_ne_zero, fun q hq => ?_⟩
    rw [MvPowerSeries.coeff_monomial, ite_eq_right_iff]
    rintro rfl
    exact absurd hq (lt_irrefl _)
  simpa only [zero_add] using initialMonomial_mul m h0 he

variable {r d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ j, FiniteDimensional K (V j)]

/-- §5.2: the central slice G_0(j) has at least as many points as the restriction image `R j`
has dimensions, when the restriction of `T` to the exponents of zero old weight is `R`. -/
theorem taylor_zeroSlice_card_ge (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (R : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K)
    (Z : Set ((Fin r ⊕ Fin (d + 1)) →₀ ℕ))
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → m.toSyn a < m.toSyn b)
    (htan : ∀ β, tangentExponent r β ∈ Z)
    (hcoef : ∀ j v β, MvPowerSeries.coeff (tangentExponent r β) (T j v) =
      MvPowerSeries.coeff β (R j v))
    (hzero : ∀ j v, ∀ a ∈ Z, (∃ i, a (Sum.inl i) ≠ 0) → MvPowerSeries.coeff a (T j v) = 0)
    (j : ℕ) :
    Module.finrank K (LinearMap.range (R j)) ≤
      (exponentSlice (taylorExponentPoints m T) j 0).card := by
  classical
  let f : V j →ₗ[K] (m.syn → K) := (monomialCoefficientMap m).comp (T j)
  let S : Set m.syn := Set.range fun β => m.toSyn (tangentExponent r β)
  let Z' : Set m.syn := m.toSyn.symm ⁻¹' Z
  have hSZ : S ⊆ Z' := by
    rintro _ ⟨β, rfl⟩
    change m.toSyn.symm (m.toSyn (tangentExponent r β)) ∈ Z
    rw [AddEquiv.symm_apply_apply]
    exact htan β
  have hZ' : ∀ a ∈ Z', ∀ b, b ∉ Z' → a < b := by
    intro a ha b hb
    simpa only [AddEquiv.apply_symm_apply] using hZ _ ha _ hb
  have hzero' : ∀ v, ∀ a ∈ Z', a ∉ S → f v a = 0 := by
    intro v a ha haS
    apply hzero j v _ ha
    by_contra hall
    push Not at hall
    obtain ⟨β, hβ⟩ := exists_tangentExponent_eq hall
    exact haS ⟨β, show m.toSyn (tangentExponent r β) = a by rw [hβ, AddEquiv.apply_symm_apply]⟩
  have hcount := finrank_masked_le_ncard f hSZ hZ' hzero'
  -- the restriction image is a linear image of the masked coefficients
  let Ψ : (m.syn → K) →ₗ[K] MvPowerSeries (Fin (d + 1)) K :=
    { toFun := fun g β => g (m.toSyn (tangentExponent r β))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : R j = Ψ.comp (maskedCoefficientMap f S) := by
    apply LinearMap.ext
    intro v
    apply MvPowerSeries.ext
    intro β
    change MvPowerSeries.coeff β (R j v) =
      S.indicator (f v) (m.toSyn (tangentExponent r β))
    rw [Set.indicator_of_mem (show m.toSyn (tangentExponent r β) ∈ S from ⟨β, rfl⟩)]
    change _ = MvPowerSeries.coeff (m.toSyn.symm (m.toSyn (tangentExponent r β))) (T j v)
    rw [AddEquiv.symm_apply_apply, hcoef]
  have hle : Module.finrank K (LinearMap.range (R j)) ≤
      Module.finrank K (LinearMap.range (maskedCoefficientMap f S)) := by
    rw [hR, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  refine hle.trans (hcount.trans ?_)
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun a => (splitTaylorExponent r d (m.toSyn.symm a)).2)
    ?_ ?_ (Finset.finite_toSet _)
  · rintro a ⟨⟨v, hv⟩, β, rfl⟩
    rw [AddEquiv.symm_apply_apply, splitTaylorExponent_tangentExponent]
    rw [Finset.mem_coe, mem_exponentSlice, ← splitTaylorExponent_tangentExponent]
    apply Finset.mem_image.mpr
    refine ⟨tangentExponent r β, (mem_initialMonomialFinset m (LinearMap.range (T j))
      (tangentExponent r β)).mpr ⟨T j v, ⟨v, rfl⟩, ?_⟩, rfl⟩
    rw [initialMonomial_iff_initialCoefficient]
    exact hv
  · rintro a ⟨-, β, rfl⟩ b ⟨-, γ, rfl⟩ hab
    simp only [AddEquiv.symm_apply_apply, splitTaylorExponent_tangentExponent] at hab
    have hβγ : β = γ := by
      ext i
      exact_mod_cast congrFun hab i
    rw [hβγ]

/-- §5.2 in the weighted order: the exponents of zero old weight form the initial segment, and
the tangent directions carry no old weight. -/
theorem weighted_zeroSlice_card_ge (m₀ : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (w : Fin r ⊕ Fin (d + 1) → ℝ) (v : Fin r ⊕ Fin (d + 1) → ℕ) (hw : ∀ i, 0 ≤ w i)
    (hwt : ∀ i, w (Sum.inr i) = 0)
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (R : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K)
    (hcoef : ∀ j s β, MvPowerSeries.coeff (tangentExponent r β) (T j s) =
      MvPowerSeries.coeff β (R j s))
    (hzero : ∀ j s a, realExponentWeight w a = 0 → (∃ i, a (Sum.inl i) ≠ 0) →
      MvPowerSeries.coeff a (T j s) = 0)
    (j : ℕ) :
    Module.finrank K (LinearMap.range (R j)) ≤
      (exponentSlice (taylorExponentPoints (weightedMonomialOrder m₀ w v hw) T) j 0).card :=
  taylor_zeroSlice_card_ge _ T R {a | realExponentWeight w a = 0}
    (fun _ ha _ hb => weightedMonomialOrder_zeroWeight_lt m₀ w v hw ha hb)
    (fun β => realExponentWeight_tangentExponent hwt β) hcoef
    (fun j s a ha => hzero j s a ha) j

/-- §5.2: sections whose Taylor expansions are units times products of tangent coordinates put
the cube {0,1}^(d+1) into the central slice. -/
theorem taylor_binaryVectors_subset_zeroSlice (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K) (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin (d + 1)), ∃ (x : V h₀) (u : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K),
      MvPowerSeries.constantCoeff u ≠ 0 ∧
        T h₀ x = u * MvPowerSeries.monomial (tangentExponent r (∑ i ∈ s, Finsupp.single i 1)) 1) :
    binaryVectors (d + 1) ⊆ exponentSlice (taylorExponentPoints m T) h₀ 0 := by
  classical
  intro γ hγ
  have hγ01 : ∀ i, γ i = 0 ∨ γ i = 1 := by
    intro i
    have h := Fintype.mem_piFinset.mp hγ i
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  obtain ⟨x, u, hu, hx⟩ := hprod (Finset.univ.filter fun i => γ i = 1)
  set β : Fin (d + 1) →₀ ℕ := ∑ i ∈ Finset.univ.filter (fun i => γ i = 1), Finsupp.single i 1
  have hβ : (fun i => (β i : ℤ)) = γ := by
    funext i
    simp only [β, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rcases hγ01 i with h | h <;> simp [h]
  rw [mem_exponentSlice, ← hβ, ← splitTaylorExponent_tangentExponent]
  apply Finset.mem_image.mpr
  refine ⟨tangentExponent r β, (mem_initialMonomialFinset m (LinearMap.range (T h₀))
    (tangentExponent r β)).mpr ⟨T h₀ x, ⟨x, rfl⟩, ?_⟩, rfl⟩
  rw [hx]
  exact isInitialMonomial_unit_mul_monomial m hu _

end PowerSeries

/-- A lower bound for the number of points bounds the slice radius from below. -/
theorem sliceRadius_ge_of_card_ge {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) {I : ℕ}
    (hI : I ≤ E.card) :
    (((d + 1).factorial * I : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹ ≤ sliceRadius E := by
  unfold sliceRadius
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  push_cast
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hI) (by positivity)

/-- The root bound (13) for the restriction image, in the form s (q + 1 - s^(d+1)), gives the
central-slice input λ q - C of (17) with λ = s and C = s (s^(d+1) - 1). -/
theorem zeroSlice_radius_lower_of_root {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) {I q s : ℕ}
    (hI : I ≤ E.card)
    (hroot : (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * I : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹) :
    (s : ℝ) * q - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) ≤ sliceRadius E := by
  have h := hroot.trans (sliceRadius_ge_of_card_ge E hI)
  linarith

section Growth

variable {K : Type*} [Field K] {r d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)] [∀ j, FiniteDimensional K (V j)]

/-- §5.2 assembled: the slice growth (17) and the moment growth (18) from the restriction data.
The central-slice input of (17) comes from #G_0(q) ≥ dim (restriction image) and the root
bound (13) for the restriction image, the cube from products of tangent coordinates. -/
theorem taylor_weightedSliceMoment_growth_of_restriction
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h x y, T (j + h) (μ j h x y) = T j x * T h y)
    (R : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K)
    (Z : Set ((Fin r ⊕ Fin (d + 1)) →₀ ℕ))
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → m.toSyn a < m.toSyn b)
    (htan : ∀ β, tangentExponent r β ∈ Z)
    (hcoef : ∀ j x β, MvPowerSeries.coeff (tangentExponent r β) (T j x) =
      MvPowerSeries.coeff β (R j x))
    (hzero : ∀ j x, ∀ a ∈ Z, (∃ i, a (Sum.inl i) ≠ 0) → MvPowerSeries.coeff a (T j x) = 0)
    (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin (d + 1)), ∃ (x : V h₀) (u : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K),
      MvPowerSeries.constantCoeff u ≠ 0 ∧
        T h₀ x = u * MvPowerSeries.monomial (tangentExponent r (∑ i ∈ s, Finsupp.single i 1)) 1)
    (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * Module.finrank K (LinearMap.range (R q)) : ℕ) : ℝ) ^
        ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (j h : ℕ) (w : (Fin r → ℤ) → ℝ) (hh : H + h₀ ≤ h)
    (hr : 0 ≤ (s : ℝ) * h - ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀))
    (hw : ∀ p, 0 ≤ w p) :
    weightedSliceMoment (taylorExponentPoints m T) j w +
      (d + 2 : ℝ) * ((s : ℝ) * h - ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀)) *
        weightedSliceCount (taylorExponentPoints m T) j w ≤
      weightedSliceMoment (taylorExponentPoints m T) (j + h) w :=
  taylor_weightedSliceMoment_growth m T μ hT H h₀
    (taylor_binaryVectors_subset_zeroSlice m T h₀ hprod) (Nat.cast_nonneg s) hH
    (fun q hq => zeroSlice_radius_lower_of_root _
      (taylor_zeroSlice_card_ge m T R Z hZ htan hcoef hzero q) (hroot q hq))
    j h w hh hr hw

end Growth

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesExponents
public import MixedFujita.SimplexMoment

/-!
The algebraic bridge from graded vector spaces with injective multiplicative
Taylor maps into MvPowerSeries to the finite exponent/slice API.
Constructing the Taylor maps from geometric sections remains a separate
geometric dependency. WeightedTaylorOrder constructs the manuscript's order.
-/

@[expose] public section

namespace MixedFujita

open scoped Pointwise

noncomputable def splitTaylorExponent (r d : ℕ) :
    ((Fin r ⊕ Fin (d + 1)) →₀ ℕ) →+
      ((Fin r → ℤ) × (Fin (d + 1) → ℤ)) where
  toFun a := (fun i => (a (Sum.inl i) : ℤ), fun i => (a (Sum.inr i) : ℤ))
  map_zero' := by
    apply Prod.ext <;> funext i <;> simp
  map_add' := by
    intro a b
    apply Prod.ext <;> funext i <;> simp

theorem splitTaylorExponent_injective (r d : ℕ) :
    Function.Injective (splitTaylorExponent r d) := by
  intro a b h
  apply Finsupp.ext
  rintro (i | i)
  · have hi := congrFun (congrArg Prod.fst h) i
    change (a (Sum.inl i) : ℤ) = (b (Sum.inl i) : ℤ) at hi
    exact_mod_cast hi
  · have hi := congrFun (congrArg Prod.snd h) i
    change (a (Sum.inr i) : ℤ) = (b (Sum.inr i) : ℤ) at hi
    exact_mod_cast hi

theorem splitTaylorExponent_nonneg (r d : ℕ)
    (a : (Fin r ⊕ Fin (d + 1)) →₀ ℕ) :
    (∀ i, 0 ≤ (splitTaylorExponent r d a).1 i) ∧
      (∀ i, 0 ≤ (splitTaylorExponent r d a).2 i) := by
  constructor <;> intro i <;> exact Int.natCast_nonneg _

variable {K : Type*} [Field K] {r d : ℕ}
  {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ j, FiniteDimensional K (V j)]

noncomputable def taylorExponentPoints (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K) (j : ℕ) :
    Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)) := by
  classical
  exact (initialMonomialFinset m (LinearMap.range (T j))).image (splitTaylorExponent r d)

theorem taylorExponentPoints_card (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (j : ℕ) (hT : Function.Injective (T j)) :
    (taylorExponentPoints m T j).card = Module.finrank K (V j) := by
  classical
  rw [taylorExponentPoints, Finset.card_image_of_injective _ (splitTaylorExponent_injective r d),
    initialMonomialFinset_card, LinearMap.finrank_range_of_inj hT]

theorem taylor_weightedSliceCount_one (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (j : ℕ) (hT : Function.Injective (T j)) :
    weightedSliceCount (taylorExponentPoints m T) j (fun _ => 1) =
      (Module.finrank K (V j) : ℝ) := by
  rw [weightedSliceCount_one, taylorExponentPoints_card m T j hT]

theorem taylorExponentPoints_semigroup (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h v w, T (j + h) (μ j h v w) = T j v * T h w) :
    GradedExponentSemigroup (taylorExponentPoints m T) := by
  classical
  intro j h a b ha hb
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
  apply Finset.mem_image.mpr
  refine ⟨p + q, ?_, map_add _ p q⟩
  apply initialMonomialFinset_add_subset m _ _ _ ?_
    (Finset.mem_add.mpr ⟨p, hp, q, hq, rfl⟩)
  intro φ hφ ψ hψ
  obtain ⟨v, rfl⟩ := hφ
  obtain ⟨w, rfl⟩ := hψ
  exact ⟨μ j h v w, hT j h v w⟩

theorem taylorExponentPoints_nonneg (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (j : ℕ) {a : (Fin r → ℤ) × (Fin (d + 1) → ℤ)}
    (ha : a ∈ taylorExponentPoints m T j) :
    (∀ i, 0 ≤ a.1 i) ∧ (∀ i, 0 ≤ a.2 i) := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
  exact splitTaylorExponent_nonneg r d p

theorem taylor_exponentSlice_nonneg (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (j : ℕ) (p : Fin r → ℤ) {γ : Fin (d + 1) → ℤ}
    (hγ : γ ∈ exponentSlice (taylorExponentPoints m T) j p) : ∀ i, 0 ≤ γ i :=
  (taylorExponentPoints_nonneg m T j
    ((mem_exponentSlice _ _ _ _).mp hγ)).2

theorem taylor_weighted_firstMoment_bound (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p) :
    (d + 1 : ℝ) / (d + 2 : ℝ) * weightedSliceMoment (taylorExponentPoints m T) j w ≤
      ∑ p ∈ exponentSupport (taylorExponentPoints m T) j,
        w p * (∑ γ ∈ exponentSlice (taylorExponentPoints m T) j p,
          ((∑ i, (γ i : ℝ)) + (d + 1 : ℝ))) :=
  weighted_exponentSlice_firstMoment_bound _ _ _ hw
    (fun p _ _ hγ => taylor_exponentSlice_nonneg m T j p hγ)

theorem taylor_weightedSliceMoment_growth (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h v w, T (j + h) (μ j h v w) = T j v * T h w)
    (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice (taylorExponentPoints m T) h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤
      sliceRadius (exponentSlice (taylorExponentPoints m T) q 0))
    (j h : ℕ) (w : (Fin r → ℤ) → ℝ)
    (hh : H + h₀ ≤ h) (hr : 0 ≤ lam * h - (C + lam * h₀))
    (hw : ∀ p, 0 ≤ w p) :
    weightedSliceMoment (taylorExponentPoints m T) j w +
      (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
        weightedSliceCount (taylorExponentPoints m T) j w ≤
      weightedSliceMoment (taylorExponentPoints m T) (j + h) w :=
  weightedSliceMoment_growth _ (taylorExponentPoints_semigroup m T μ hT)
    H h₀ hcube hlam hH hlower j h w hh hr hw

end MixedFujita

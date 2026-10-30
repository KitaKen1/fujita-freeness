/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InteriorStartLowerGrowth
public import MixedFujita.TaylorInteriorStart

/-!
The adapted-basis Taylor interior inequality from a strict dimension lower bound.
The initial-exponent count equals the dimension, so an eventual lower bound c j^n suffices;
no limit of dimensions divided by j^n is assumed. The adapted-basis construction is the same
as in TaylorInteriorStart, with the new lattice-average estimate substituted.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

variable {K : Type*} [Field K]

/-- The numerical Taylor start (7) using only dimension lower growth and an order upper bound. -/
theorem taylor_interior_start_of_dimension_lower {n : ℕ} (hn : 0 < n) {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
    [∀ j, Module K (V j)] [∀ j, FiniteDimensional K (V j)]
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin n) K) (hT : ∀ j, Function.Injective (T j))
    {c b C : ℝ} (hc : 0 < c) (hb : 0 < b) (hC : 0 ≤ C)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤ (Module.finrank K (V j) : ℝ))
    (hord : ∀ᶠ j : ℕ in atTop, ∀ x : V j, x ≠ 0 →
      realWeightedOrder (fun _ => (1 : ℝ)) (T j x) ≤ C * j)
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t → t ≤ b →
      ∃ B : Module.Basis (Fin (Module.finrank K (V j))) K (V j),
        minimizationFunctional j t (ζ * n)
          (fun i => ζ * realWeightedOrder (fun _ => (1 : ℝ)) (T j (B i))) ≤ 1 - δ := by
  classical
  set w : Fin n → ℝ := fun _ => 1 with hw_def
  have hw : ∀ i, 0 ≤ w i := fun _ => zero_le_one
  set m₀ := finiteLexMonomialOrder (Fin n)
  set m := weightedMonomialOrder m₀ w (fun _ => 0) hw with hm
  set E : ℕ → Finset (Fin n → ℕ) := fun j =>
    (initialMonomialFinset m (LinearMap.range (T j))).image (fun p : Fin n →₀ ℕ => (p : Fin n → ℕ))
    with hE
  have hEcard : ∀ j, ((E j).card : ℝ) = Module.finrank K (V j) := by
    intro j
    rw [hE, Finset.card_image_of_injective _ (DFunLike.coe_injective (F := Fin n →₀ ℕ)),
      initialMonomialFinset_card,
      LinearMap.finrank_range_of_inj (hT j)]
  have hN' : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤ ((E j).card : ℝ) := by
    simpa only [hEcard] using hN
  have hdeg : ∀ (φ : MvPowerSeries (Fin n) K) (p : Fin n →₀ ℕ), IsInitialMonomial m φ p →
      ((∑ i, (p : Fin n → ℕ) i : ℕ) : ℝ) = realWeightedOrder w φ := by
    intro φ p hp
    rw [realWeightedOrder_of_isInitialMonomial m₀ w _ hw hp]
    change _ = ∑ i, w i * (p i : ℝ)
    simp [hw_def]
  have hord' : ∀ᶠ j : ℕ in atTop, ∀ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) ≤ C * j := by
    filter_upwards [hord] with j hj γ hγ
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨φ, ⟨x, rfl⟩, hpφ⟩ := (mem_initialMonomialFinset m _ p).mp hp
    have hx : x ≠ 0 := by
      rintro rfl
      exact initialMonomial_series_ne_zero m hpφ (map_zero _)
    rw [hdeg _ p hpφ]
    exact hj x hx
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ :=
    interior_start_of_dimension_lower n hn E hc hb hC hN' hord' hvol
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hev] with j hj t ht₀t htb
  set S := LinearMap.range (T j) with hS
  set f := subspaceCoefficientMap m S with hf
  have hfin := initialIndexSet_finite f
  let _ : Fintype (initialIndexSet f) := hfin.fintype
  set Bs := weightedSubspaceInitialBasis m₀ w (fun _ => 0) hw S with hBs
  set eT := LinearEquiv.ofInjective (T j) (hT j) with heT
  set B0 := Bs.map eT.symm with hB0
  set e := B0.indexEquiv (Module.finBasis K (V j)) with he
  refine ⟨B0.reindex e, ?_⟩
  have hval : ∀ k, realWeightedOrder w (T j (B0 k)) =
      ((∑ i, (m.toSyn.symm k.val : Fin n → ℕ) i : ℕ) : ℝ) := by
    intro k
    have h1 : T j (B0 k) = (Bs k : MvPowerSeries (Fin n) K) := by
      have h2 : ((eT (eT.symm (Bs k)) : S) : MvPowerSeries (Fin n) K) = T j (eT.symm (Bs k)) :=
        LinearEquiv.ofInjective_apply (T j) _
      rw [LinearEquiv.apply_symm_apply] at h2
      rw [hB0, Module.Basis.map_apply]
      exact h2.symm
    rw [h1, hdeg _ _ (weightedSubspaceInitialBasis_spec m₀ w _ hw S k)]
  have hsum1 : ∑ i, Real.exp (ζ * n / t - ζ * realWeightedOrder w (T j ((B0.reindex e) i)) / j) =
      ∑ k, Real.exp (ζ * n / t - ζ * realWeightedOrder w (T j (B0 k)) / j) := by
    simp only [Module.Basis.reindex_apply]
    exact Equiv.sum_comp e.symm
      (fun k => Real.exp (ζ * n / t - ζ * realWeightedOrder w (T j (B0 k)) / j))
  have hEj : E j = hfin.toFinset.image (fun k => ((m.toSyn.symm k : Fin n →₀ ℕ) : Fin n → ℕ)) := by
    rw [hE]
    simp only [initialMonomialFinset, Finset.image_image]
    rfl
  have hinj : ∀ x ∈ hfin.toFinset, ∀ y ∈ hfin.toFinset,
      (fun k => ((m.toSyn.symm k : Fin n →₀ ℕ) : Fin n → ℕ)) x =
        (fun k => ((m.toSyn.symm k : Fin n →₀ ℕ) : Fin n → ℕ)) y → x = y := by
    intro x _ y _ hxy
    exact m.toSyn.symm.injective (DFunLike.coe_injective (F := Fin n →₀ ℕ) hxy)
  have hsum2 : ∑ k, Real.exp (ζ * n / t - ζ * realWeightedOrder w (T j (B0 k)) / j) =
      ∑ γ ∈ E j, Real.exp (ζ * n / t - ζ * (((∑ i, γ i : ℕ) : ℝ) / j)) := by
    rw [hEj, Finset.sum_image hinj,
      Finset.sum_subtype hfin.toFinset (fun x => hfin.mem_toFinset)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hval k]
    congr 1
    ring
  have hcard := hEcard j
  unfold minimizationFunctional
  rw [hsum1.trans hsum2, ← hcard]
  exact hj t ht₀t htb


end MixedFujita

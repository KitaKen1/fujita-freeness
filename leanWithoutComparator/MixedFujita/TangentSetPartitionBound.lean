/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MovingCenterLimit
public import MixedFujita.InitialMonomialRename

/-!
The inequality (20) of section 5.3 for Taylor data in n variables with a set of tangent variables.

The abstract inequality `taylor_uniform_partition_bound` is stated for power series whose variables
are split as normal variables `Fin r` and tangent variables `Fin (d + 1)`. At a general closed
point of the centre of a weight the Taylor variables are indexed by `Fin n` and the tangent
coordinates form a subset T with d + 1 elements. Here the inequality is transported: for graded
multiplicative Taylor maps into power series in n variables, a set Z of exponents which is an
initial segment of the monomial order and contains the exponents supported on T, such that the
coefficients at the exponents of Z with a nonzero part outside T vanish, sections whose Taylor
expansions are units times the squarefree monomials in the variables of T, and a root bound for
the dimension of the coefficients on Z, the inequality holds with

* Q_j the sum of a weight over the initial exponents of degree j, the weight depending only on
  the part of the exponent outside T, and
* the tangential sum, the sum over the initial exponents of degree M of the weight times the
  degree in the variables of T.
-/

@[expose] public section

namespace MixedFujita

attribute [local instance] Classical.propDecidable

section Splitting

variable {n d : ℕ}

/-- A bijection from n variables to normal and tangent variables, for a set of d + 1 tangent
variables. -/
theorem exists_equiv_sum_of_card (Tan : Finset (Fin n)) (hTan : Tan.card = d + 1) :
    ∃ (r : ℕ) (e : Fin n ≃ Fin r ⊕ Fin (d + 1)), ∀ i, i ∈ Tan ↔ ∃ t, e i = Sum.inr t := by
  obtain ⟨e₂⟩ : Nonempty ({i // i ∈ Tan} ≃ Fin (d + 1)) :=
    ⟨Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hTan])⟩
  obtain ⟨e₃⟩ : Nonempty ({i // ¬ i ∈ Tan} ≃ Fin (Fintype.card {i // ¬ i ∈ Tan})) :=
    ⟨Fintype.equivFin _⟩
  refine ⟨Fintype.card {i // ¬ i ∈ Tan},
    (Equiv.sumCompl (· ∈ Tan)).symm.trans ((Equiv.sumCongr e₂ e₃).trans (Equiv.sumComm _ _)),
    fun i => ?_⟩
  by_cases hi : i ∈ Tan
  · refine ⟨fun _ => ⟨e₂ ⟨i, hi⟩, ?_⟩, fun _ => hi⟩
    change Sum.swap (Sum.map e₂ e₃ ((Equiv.sumCompl (· ∈ Tan)).symm i)) = _
    rw [Equiv.sumCompl_symm_apply_of_pos hi]
    rfl
  · refine ⟨fun h => absurd h hi, ?_⟩
    rintro ⟨t, ht⟩
    exfalso
    change Sum.swap (Sum.map e₂ e₃ ((Equiv.sumCompl (· ∈ Tan)).symm i)) = _ at ht
    rw [Equiv.sumCompl_symm_apply_of_neg hi] at ht
    exact Sum.inl_ne_inr ht

/-- The exponent of a squarefree monomial. -/
theorem finset_sum_single_one_apply {ι : Type*} (s : Finset ι) (j : ι) :
    (∑ i ∈ s, Finsupp.single i 1 : ι →₀ ℕ) j = if j ∈ s then 1 else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

end Splitting

section Bound

variable {K : Type*} [Field K]

/-- The coefficients of power series at the exponents of a set Z. -/
noncomputable def zeroSliceCoefficientMap {σ W : Type*} [AddCommGroup W] [Module K W]
    (Z : Set (σ →₀ ℕ)) (f : W →ₗ[K] MvPowerSeries σ K) : W →ₗ[K] (Z → K) :=
  LinearMap.pi fun a => (MvPowerSeries.coeff (a : σ →₀ ℕ)).comp f

theorem zeroSliceCoefficientMap_apply {σ W : Type*} [AddCommGroup W] [Module K W]
    (Z : Set (σ →₀ ℕ)) (f : W →ₗ[K] MvPowerSeries σ K) (x : W) (a : Z) :
    zeroSliceCoefficientMap Z f x a = MvPowerSeries.coeff (a : σ →₀ ℕ) (f x) :=
  rfl

/-- The initial exponents only depend on the space. -/
theorem initialMonomialFinset_congr {σ : Type*} (m : MonomialOrder σ)
    {S S' : Submodule K (MvPowerSeries σ K)} [FiniteDimensional K S] [FiniteDimensional K S']
    (h : S = S') : initialMonomialFinset m S = initialMonomialFinset m S' := by
  ext p
  rw [mem_initialMonomialFinset, mem_initialMonomialFinset, h]

variable {n d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ j, FiniteDimensional K (V j)]

/-- (20) for Taylor data in n variables with a set T of d + 1 tangent variables. -/
theorem taylor_uniform_partition_bound_of_tangentSet (Tan : Finset (Fin n))
    (hTan : Tan.card = d + 1) (m : MonomialOrder (Fin n))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin n) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h x y, T (j + h) (μ j h x y) = T j x * T h y)
    (Z : Set (Fin n →₀ ℕ))
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → m.toSyn a < m.toSyn b)
    (htan : ∀ a : Fin n →₀ ℕ, (∀ i, i ∉ Tan → a i = 0) → a ∈ Z)
    (hzero : ∀ j x, ∀ a ∈ Z, (∃ i, i ∉ Tan ∧ a i ≠ 0) → MvPowerSeries.coeff a (T j x) = 0)
    (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin n), s ⊆ Tan → ∃ (x : V h₀) (u : MvPowerSeries (Fin n) K),
      MvPowerSeries.constantCoeff u ≠ 0 ∧
        T h₀ x = u * MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single i 1) 1)
    (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * Module.finrank K
        (LinearMap.range (zeroSliceCoefficientMap Z (T q))) : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (l M : ℕ) (hl : 0 < l) (hM : l * (H + h₀ + s ^ (d + 1)) ≤ M)
    (wt : (Fin n →₀ ℕ) → ℝ) (hwt : ∀ p, 0 ≤ wt p)
    (hinv : ∀ p q : Fin n →₀ ℕ, (∀ i, i ∉ Tan → p i = q i) → wt p = wt q)
    (hQM : 0 < ∑ p ∈ initialMonomialFinset m (LinearMap.range (T M)), wt p) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range l,
      (((s : ℝ) * (auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l : ℕ) -
        ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀)) / M) *
          ((∑ p ∈ initialMonomialFinset m (LinearMap.range (T (auxiliaryDegree M i l))), wt p) /
            ∑ p ∈ initialMonomialFinset m (LinearMap.range (T M)), wt p)) ≤
      (∑ p ∈ initialMonomialFinset m (LinearMap.range (T M)), wt p * ∑ i ∈ Tan, (p i : ℝ)) /
          ((M : ℝ) * ∑ p ∈ initialMonomialFinset m (LinearMap.range (T M)), wt p) +
        (d + 1 : ℝ) / M := by
  obtain ⟨r, e, he⟩ := exists_equiv_sum_of_card Tan hTan
  -- the transported Taylor maps
  obtain ⟨T', hT'def⟩ : ∃ T' : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K,
      ∀ j, T' j = (MvPowerSeries.renameEquiv K e).toLinearMap.comp (T j) := ⟨_, fun _ => rfl⟩
  have hT'apply : ∀ j x, T' j x = MvPowerSeries.renameEquiv K e (T j x) := by
    intro j x
    rw [hT'def]
    rfl
  have hT' : ∀ j h x y, T' (j + h) (μ j h x y) = T' j x * T' h y := by
    intro j h x y
    rw [hT'apply, hT'apply, hT'apply, hT, map_mul]
  have hcoef' : ∀ j x (a : Fin n →₀ ℕ),
      MvPowerSeries.coeff (Finsupp.equivMapDomain e a) (T' j x) =
        MvPowerSeries.coeff a (T j x) := by
    intro j x a
    rw [hT'apply]
    exact coeff_equivMapDomain_renameEquiv e (T j x) a
  have hrange : ∀ j, LinearMap.range (T' j) =
      (LinearMap.range (T j)).map (MvPowerSeries.renameEquiv K e).toLinearMap := by
    intro j
    rw [hT'def]
    exact LinearMap.range_comp _ _
  -- the transported set of exponents
  obtain ⟨Z', hZ'def⟩ : ∃ Z' : Set ((Fin r ⊕ Fin (d + 1)) →₀ ℕ),
      ∀ a', a' ∈ Z' ↔ Finsupp.equivMapDomain e.symm a' ∈ Z := ⟨{a' | _}, fun _ => Iff.rfl⟩
  have hZ' : ∀ a ∈ Z', ∀ b, b ∉ Z' →
      (monomialOrderMapEquiv m e).toSyn a < (monomialOrderMapEquiv m e).toSyn b := by
    intro a ha b hb
    exact hZ _ ((hZ'def a).mp ha) _ (fun hb' => hb ((hZ'def b).mpr hb'))
  have htan' : ∀ β, tangentExponent r β ∈ Z' := by
    intro β
    rw [hZ'def]
    refine htan _ fun i hi => ?_
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm]
    cases hei : e i with
    | inl a => rfl
    | inr t => exact absurd ((he i).mpr ⟨t, hei⟩) hi
  -- the restriction to the tangent variables
  obtain ⟨R', hR'def⟩ : ∃ R' : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K,
      ∀ j, R' j = (MvPowerSeries.killCompl (⟨Sum.inr, Sum.inr_injective⟩ :
        Fin (d + 1) ↪ Fin r ⊕ Fin (d + 1))).toLinearMap.comp (T' j) := ⟨_, fun _ => rfl⟩
  have hemb : ∀ β : Fin (d + 1) →₀ ℕ, Finsupp.embDomain (⟨Sum.inr, Sum.inr_injective⟩ :
      Fin (d + 1) ↪ Fin r ⊕ Fin (d + 1)) β = tangentExponent r β := by
    intro β
    ext (a | t)
    · rw [Finsupp.embDomain_apply, dite_eq_right]
      · rfl
      · rintro ⟨t, ht⟩
        exact Sum.inr_ne_inl ht
    · exact Finsupp.embDomain_apply_self _ β t
  have hcoefR : ∀ j x β, MvPowerSeries.coeff (tangentExponent r β) (T' j x) =
      MvPowerSeries.coeff β (R' j x) := by
    intro j x β
    rw [hR'def, ← hemb β]
    exact (MvPowerSeries.coeff_killCompl (T' j x) β).symm
  have hzero' : ∀ j x, ∀ a ∈ Z', (∃ i, a (Sum.inl i) ≠ 0) →
      MvPowerSeries.coeff a (T' j x) = 0 := by
    rintro j x a' ha' ⟨i, hi⟩
    rw [← equivMapDomain_equivMapDomain_symm e a', hcoef']
    refine hzero j x _ ((hZ'def a').mp ha') ⟨e.symm (Sum.inl i), ?_, ?_⟩
    · intro hmem
      obtain ⟨t, ht⟩ := (he _).mp hmem
      rw [Equiv.apply_symm_apply] at ht
      exact Sum.inl_ne_inr ht
    · rw [Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
      exact hi
  -- the cube
  have hprod' : ∀ s' : Finset (Fin (d + 1)), ∃ (x : V h₀)
      (u : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K), MvPowerSeries.constantCoeff u ≠ 0 ∧
        T' h₀ x = u * MvPowerSeries.monomial
          (tangentExponent r (∑ i ∈ s', Finsupp.single i 1)) 1 := by
    intro s'
    obtain ⟨x, u, hu, hx⟩ := hprod (s'.image fun t => e.symm (Sum.inr t)) (by
      intro i hi
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hi
      exact (he _).mpr ⟨t, Equiv.apply_symm_apply e _⟩)
    refine ⟨x, MvPowerSeries.renameEquiv K e u, ?_, ?_⟩
    · change MvPowerSeries.constantCoeff (MvPowerSeries.rename e u) ≠ 0
      rw [MvPowerSeries.constantCoeff_rename]
      exact hu
    · rw [hT'apply, hx, map_mul]
      have hexp : Finsupp.equivMapDomain e
          (∑ i ∈ s'.image fun t => e.symm (Sum.inr t), Finsupp.single i 1) =
            tangentExponent r (∑ i ∈ s', Finsupp.single i 1) := by
        ext y
        rw [Finsupp.equivMapDomain_apply, finset_sum_single_one_apply]
        rcases y with a | t
        · rw [ite_eq_right]
          · rfl
          · intro hmem
            obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hmem
            exact Sum.inr_ne_inl (e.symm.injective ht)
        · change _ = (∑ i ∈ s', Finsupp.single i 1 : Fin (d + 1) →₀ ℕ) t
          rw [finset_sum_single_one_apply]
          by_cases ht : t ∈ s'
          · rw [ite_eq_left ht, ite_eq_left (Finset.mem_image.mpr ⟨t, ht, rfl⟩)]
          · rw [ite_eq_right ht, ite_eq_right]
            intro hmem
            obtain ⟨t', ht', hEq⟩ := Finset.mem_image.mp hmem
            exact ht (Sum.inr_injective (e.symm.injective hEq) ▸ ht')
      congr 1
      change MvPowerSeries.rename e (MvPowerSeries.monomial _ 1) = _
      rw [MvPowerSeries.rename_monomial, ← Finsupp.equivMapDomain_eq_mapDomain, hexp]
  -- the dimension of the restriction
  have hker : ∀ q, LinearMap.ker (R' q) = LinearMap.ker (zeroSliceCoefficientMap Z (T q)) := by
    intro q
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro hx
      funext a
      change MvPowerSeries.coeff (a : Fin n →₀ ℕ) (T q x) = 0
      by_cases hsupp : ∀ i, i ∉ Tan → (a : Fin n →₀ ℕ) i = 0
      · obtain ⟨β, hβ⟩ := exists_tangentExponent_eq
          (a := Finsupp.equivMapDomain e (a : Fin n →₀ ℕ)) (fun i => by
            rw [Finsupp.equivMapDomain_apply]
            refine hsupp _ fun hmem => ?_
            obtain ⟨t, ht⟩ := (he _).mp hmem
            rw [Equiv.apply_symm_apply] at ht
            exact Sum.inl_ne_inr ht)
        rw [← hcoef' q x, ← hβ, hcoefR, hx, map_zero]
      · push Not at hsupp
        obtain ⟨i, hi, hai⟩ := hsupp
        exact hzero q x _ a.2 ⟨i, hi, hai⟩
    · intro hx
      ext β
      rw [← hcoefR, map_zero, ← equivMapDomain_equivMapDomain_symm e (tangentExponent r β),
        hcoef']
      exact congrFun hx ⟨_, (hZ'def _).mp (htan' β)⟩
  have hroot' : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * Module.finrank K (LinearMap.range (R' q)) : ℕ) : ℝ) ^
        ((d : ℝ) + 1)⁻¹ := by
    intro q hq
    have h1 := LinearMap.finrank_range_add_finrank_ker (R' q)
    have h2 := LinearMap.finrank_range_add_finrank_ker (zeroSliceCoefficientMap Z (T q))
    rw [hker q] at h1
    have h3 : Module.finrank K (LinearMap.range (R' q)) =
        Module.finrank K (LinearMap.range (zeroSliceCoefficientMap Z (T q))) := by omega
    rw [h3]
    exact hroot q hq
  -- the weight as a function of the normal part
  obtain ⟨w', hw'def⟩ : ∃ w' : (Fin r → ℤ) → ℝ, ∀ ν, w' ν = wt (Finsupp.equivFunOnFinite.symm
      (fun i => Sum.elim (fun a => (ν a).toNat) (fun _ => 0) (e i))) := ⟨_, fun _ => rfl⟩
  have hw' : ∀ ν, 0 ≤ w' ν := fun ν => by
    rw [hw'def]
    exact hwt _
  have hw'eq : ∀ p : Fin n →₀ ℕ,
      w' (splitTaylorExponent r d (Finsupp.equivMapDomain e p)).1 = wt p := by
    intro p
    rw [hw'def]
    refine hinv _ _ fun i hi => ?_
    change Sum.elim (fun a => ((splitTaylorExponent r d (Finsupp.equivMapDomain e p)).1 a).toNat)
      (fun _ => 0) (e i) = p i
    cases hei : e i with
    | inl a =>
      change (((Finsupp.equivMapDomain e p) (Sum.inl a) : ℕ) : ℤ).toNat = p i
      rw [Int.toNat_natCast, Finsupp.equivMapDomain_apply, ← hei, Equiv.symm_apply_apply]
    | inr t => exact absurd ((he i).mpr ⟨t, hei⟩) hi
  have hsplit := splitTaylorExponent_injective r d
  -- the weighted counts and the tangential sum
  have hQ : ∀ j, weightedSliceCount (taylorExponentPoints (monomialOrderMapEquiv m e) T') j w' =
      ∑ p ∈ initialMonomialFinset m (LinearMap.range (T j)), wt p := by
    intro j
    rw [weightedSliceCount_eq_sum, taylorExponentPoints,
      Finset.sum_image (fun a _ b _ h => hsplit h),
      initialMonomialFinset_congr _ (hrange j),
      sum_initialMonomialFinset_map_renameEquiv m e (LinearMap.range (T j))]
    exact Finset.sum_congr rfl fun p _ => hw'eq p
  have hTanimg : Tan = (Finset.univ : Finset (Fin (d + 1))).image fun t => e.symm (Sum.inr t) := by
    ext i
    rw [he i, Finset.mem_image]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Finset.mem_univ _, by rw [← ht, Equiv.symm_apply_apply]⟩
    · rintro ⟨t, -, rfl⟩
      exact ⟨t, Equiv.apply_symm_apply e _⟩
  have hTsum : weightedTangentialSum (taylorExponentPoints (monomialOrderMapEquiv m e) T') M w' =
      ∑ p ∈ initialMonomialFinset m (LinearMap.range (T M)), wt p * ∑ i ∈ Tan, (p i : ℝ) := by
    rw [weightedTangentialSum, taylorExponentPoints,
      Finset.sum_image (fun a _ b _ h => hsplit h),
      initialMonomialFinset_congr _ (hrange M),
      sum_initialMonomialFinset_map_renameEquiv m e (LinearMap.range (T M))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw'eq p]
    congr 1
    have hsum : ∑ i ∈ Tan, (p i : ℝ) = ∑ t : Fin (d + 1), (p (e.symm (Sum.inr t)) : ℝ) := by
      rw [hTanimg, Finset.sum_image (fun a _ b _ h => Sum.inr_injective (e.symm.injective h))]
    rw [hsum]
    refine Finset.sum_congr rfl fun t _ => ?_
    change (((Finsupp.equivMapDomain e p (Sum.inr t) : ℕ) : ℤ) : ℝ) = _
    rw [Finsupp.equivMapDomain_apply, Int.cast_natCast]
  have hmain := taylor_uniform_partition_bound (monomialOrderMapEquiv m e) T' μ hT' R' Z' hZ'
    htan' hcoefR hzero' h₀ hprod' s H hroot' hH l M hl hM w' hw' (by rw [hQ M]; exact hQM)
  simp only [hQ, hTsum] at hmain
  exact hmain

end Bound

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasisAttainment
public import MixedFujita.SNCWeightSpecializationComparison
public import MixedFujita.ClosedPointLocus

/-!
Normalized profiles through realization by test primes, for the closedness of the realization
sets in the point (step 9). Let Q(y) be the normalized profiles realized at y by the bases of the
sections of D (weights on simple normal crossing models) and P_β(y) the statement that some
basis realizes β at y in the sense of test primes (`IsRealizedProfile`).

* A datum at y with α_i A < v_i or α_i = 0 realizes α by test primes, so a rational profile
  α ∈ Q(y) gives (1 − 1/(l + 2)) α ∈ P(y) for every l, with the same basis.
* Conversely, at a point where the realization sets in the tuple are closed (Lemma 3 at the point),
  the bases realizing (1 − 1/(l + 2)) α form a decreasing sequence of zero sets meeting the bases,
  so one basis realizes them all (`polynomialZeroSet_nested_inter_nonempty`), and the limit
  datum on a resolution gives α ∈ Q(y) (`mem_sncWeightNormalizedProfiles_iff`).
* Entries ≤ 0 do not matter (the values of the data are ≥ 0).

So the closedness of {y | α ∈ Q(y)} on closed points follows from the closedness of the sets
{y | P_β(y)} of rational β ≥ 0, as a countable intersection
(`isClosedOnClosedPoints_normalizedProfiles_of_realized`).
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

/-- Countable (indeed arbitrary) intersections of sets closed on closed points. -/
theorem isClosedOnClosedPoints_iInter {T : Type*} [TopologicalSpace T] {ι : Sort*}
    (s : ι → Set T) (h : ∀ i, IsClosedOnClosedPoints (s i)) :
    IsClosedOnClosedPoints (⋂ i, s i) := by
  choose Z hZ hrep using h
  refine ⟨⋂ i, Z i, isClosed_iInter hZ, fun x hx => ?_⟩
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => hrep i x hx

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

omit [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] in
/-- The values of a profile datum are nonnegative. -/
theorem sncWeightProfiles_snd_nonneg (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D y s) (i : Fin N) :
    0 ≤ p.2 i := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, -, -, hv⟩ := hp
  rw [hv i]
  refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) ?_
  have h := cartierCoefficient_nonneg_of_isEffective _
    (cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective D (s i) (hs i))) (ξ k)
  exact_mod_cast h

omit [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] in
/-- Negative entries of a profile do not matter. -/
theorem mem_sncWeightNormalizedProfiles_iff_max_zero (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (N : ℕ) (y : Y) (q : Fin N → ℝ) :
    q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y ↔
      (fun i => max (q i) 0) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  constructor
  · rintro ⟨B, p, hp, hp1, hq⟩
    refine ⟨B, p, hp, hp1, fun i => ?_⟩
    show max (q i) 0 * p.1 ≤ p.2 i
    rcases le_total (q i) 0 with h | h
    · rw [max_eq_right h, zero_mul]
      exact sncWeightProfiles_snd_nonneg cY fY d D₀ D y B hp i
    · rw [max_eq_left h]
      exact hq i
  · intro h
    exact sncWeightNormalizedProfiles_down cY fY d D₀ D N y _ h q fun i => le_max_left _ _

omit [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] in
/-- A datum realizing the normalized profile q realizes, by test primes and with the same tuple,
every profile whose entries are zero or strictly below those of q. -/
theorem isRealizedProfile_of_sncWeightProfile (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ D y s) (hp1 : 0 < p.1)
    {q : Fin N → ℝ} (hq : ∀ i, q i * p.1 ≤ p.2 i) {α : Fin N → ℝ}
    (hα : ∀ i, α i = 0 ∨ α i < q i) : IsRealizedProfile cY fY d D₀ D y s α := by
  have key : ∀ i, α i = 0 ∨ α i * p.1 < p.2 i := fun i =>
    (hα i).imp id fun h => lt_of_lt_of_le (mul_lt_mul_of_pos_right h hp1) (hq i)
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, hwΦ, hA, hv⟩ := hp
  exact isRealizedProfile_of_sncWeight π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc hBsupp D s hs hGsupp
    y w hw0 hwΦ (by rw [← hA]; exact hp1) (fun i => by
      rw [← hA, ← hv i]
      exact key i)

/-- A basis realizing by test primes a sequence of profiles converging to q, with some q_i > 0,
realizes q as a normalized profile (on a klt pair). -/
theorem mem_sncWeightNormalizedProfiles_of_tendsto (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (D : CartierDivisor Y) (y : Y) {N : ℕ} (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (α : ℕ → Fin N → ℝ) (q : Fin N → ℝ) (hα0 : ∀ l i, 0 ≤ α l i)
    (hreal : ∀ l, IsRealizedProfile cY fY d D₀ D y B (α l)) (hlim : Tendsto α atTop (𝓝 q))
    (hqpos : ∃ i, 0 < q i) : q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  have hs : ∀ i, B i ≠ 0 := B.ne_zero
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
    hGsupp⟩ := exists_proper_snc_model_with cY fY d D₀
      (fun i => cartierSectionZeroDivisor D (B i) (hs i))
  obtain ⟨u, hu0, huΦ, huA, huv⟩ := exists_normalized_sncWeight_of_tendsto_isRealizedProfile π
    hπ cY fY d hd D₀ hklt cX ξ hinj hξ hsnc hBsupp D B hs hGsupp y α q hα0 hreal hlim hqpos
  refine ⟨B, (1, fun i => ∑ k, u k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (B i) (hs i))) (ξ k) : ℝ)),
    ⟨hs, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, u, hinj, hξ, hsnc,
      hBsupp, hGsupp, hu0, huΦ, huA.symm, fun i => rfl⟩, one_pos, fun i => ?_⟩
  rw [mul_one]
  exact huv i

/-- The scaled profiles (1 − 1/(l + 2)) α. -/
def scaledProfile {N : ℕ} (α : Fin N → ℚ) (l : ℕ) : Fin N → ℚ :=
  fun i => (1 - 1 / ((l : ℚ) + 2)) * α i

theorem scaledProfile_factor_pos (l : ℕ) : (0 : ℚ) < 1 - 1 / ((l : ℚ) + 2) := by
  have h : (1 : ℚ) / ((l : ℚ) + 2) < 1 := by
    rw [div_lt_one (by positivity)]
    have : (0 : ℚ) ≤ l := Nat.cast_nonneg l
    linarith
  linarith

theorem scaledProfile_factor_lt_one (l : ℕ) : 1 - 1 / ((l : ℚ) + 2) < 1 := by
  have : (0 : ℚ) < 1 / ((l : ℚ) + 2) := by positivity
  linarith

theorem scaledProfile_nonneg {N : ℕ} {α : Fin N → ℚ} (hα0 : ∀ i, 0 ≤ α i) (l : ℕ) (i : Fin N) :
    0 ≤ scaledProfile α l i :=
  mul_nonneg (scaledProfile_factor_pos l).le (hα0 i)

theorem scaledProfile_mono {N : ℕ} {α : Fin N → ℚ} (hα0 : ∀ i, 0 ≤ α i) {l l' : ℕ}
    (hll : l ≤ l') (i : Fin N) : scaledProfile α l i ≤ scaledProfile α l' i := by
  unfold scaledProfile
  apply mul_le_mul_of_nonneg_right _ (hα0 i)
  have h1 : ((l : ℚ) + 2) ≤ (l' : ℚ) + 2 := by exact_mod_cast Nat.add_le_add_right hll 2
  have h2 : 1 / ((l' : ℚ) + 2) ≤ 1 / ((l : ℚ) + 2) :=
    one_div_le_one_div_of_le (by positivity) h1
  linarith

theorem tendsto_scaledProfile {N : ℕ} (α : Fin N → ℚ) :
    Tendsto (fun l => fun i => ((scaledProfile α l i : ℚ) : ℝ)) atTop
      (𝓝 fun i => (α i : ℝ)) := by
  rw [tendsto_pi_nhds]
  intro i
  have h : Tendsto (fun l : ℕ => (1 : ℝ) / ((l : ℝ) + 2)) atTop (𝓝 0) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 : Tendsto (fun l : ℕ => (l : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    exact (tendsto_const_nhds.div_atTop h2)
  have h3 : Tendsto (fun l : ℕ => (1 - (1 : ℝ) / ((l : ℝ) + 2)) * (α i : ℝ)) atTop
      (𝓝 ((1 - 0) * (α i : ℝ))) := (tendsto_const_nhds.sub h).mul tendsto_const_nhds
  rw [sub_zero, one_mul] at h3
  refine h3.congr fun l => ?_
  simp only [scaledProfile]
  push_cast
  ring

/-- At a point where the realization sets in the tuple are closed, a rational profile α ≥ 0 with
some α_i > 0 is a normalized profile exactly when every (1 − 1/(l + 2)) α is realized by some
basis in the sense of test primes. -/
theorem mem_sncWeightNormalizedProfiles_iff (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (D : CartierDivisor Y) (y : Y) (hclosed : RealizationSetsZariskiClosed cY fY d D₀ D y)
    {N : ℕ} (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (α : Fin N → ℚ) (hα0 : ∀ i, 0 ≤ α i)
    (hαpos : ∃ i, 0 < α i) :
    (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y ↔
      ∀ l : ℕ, ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY fY d D₀ D y B (fun i => ((scaledProfile α l i : ℚ) : ℝ)) := by
  classical
  constructor
  · rintro ⟨B, p, hp, hp1, hq⟩ l
    refine ⟨B, isRealizedProfile_of_sncWeightProfile cY fY d hd D₀ D y B hp hp1 hq fun i => ?_⟩
    rcases (hα0 i).lt_or_eq with h | h
    · right
      have h1 : ((scaledProfile α l i : ℚ) : ℝ) < (α i : ℝ) := by
        have h2 : scaledProfile α l i < α i := by
          unfold scaledProfile
          have := scaledProfile_factor_lt_one l
          nlinarith
        exact_mod_cast h2
      exact h1
    · left
      simp [scaledProfile, ← h]
  · intro hreal
    have : Nonempty (Fin N) := ⟨hαpos.choose⟩
    have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
    have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
      (Module.finrank_eq_card_basis b₀).symm
    set tup : (Fin N × Fin N → K) → Fin N → Γ(D.sheaf, ⊤) :=
      fun c i => ∑ k, c (i, k) • b₀ k with htup
    have hcoord : ∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        ∃ c : Fin N × Fin N → K, LinearIndependent K (tup c) ∧ tup c = ⇑B := by
      intro B
      have h : tup (fun ik => b₀.repr (B ik.1) ik.2) = ⇑B := by
        funext i
        exact b₀.sum_repr (B i)
      exact ⟨fun ik => b₀.repr (B ik.1) ik.2, by rw [h]; exact B.linearIndependent, h⟩
    choose I hI using fun l => hclosed N N b₀ (scaledProfile α l) (scaledProfile_nonneg hα0 l)
    have hmem : ∀ l c, c ∈ polynomialZeroSet (I l) ↔
        IsRealizedProfile cY fY d D₀ D y (tup c) (fun i => ((scaledProfile α l i : ℚ) : ℝ)) := by
      intro l c
      rw [← hI l]
      rfl
    have hanti : Antitone fun l => polynomialZeroSet (I l) := by
      intro l l' hll c hc
      exact (hmem l c).mpr (isRealizedProfile_antitone cY fY d D₀ D y (tup c)
        (fun i => by exact_mod_cast scaledProfile_mono hα0 hll i) ((hmem l' c).mp hc))
    have hne : ∀ l, (polynomialZeroSet (I l) ∩
        {c : Fin N × Fin N → K | LinearIndependent K (tup c)}).Nonempty := by
      intro l
      obtain ⟨B, hB⟩ := hreal l
      obtain ⟨c, hcG, hc⟩ := hcoord B
      exact ⟨c, (hmem l c).mpr (by rw [hc]; exact hB), hcG⟩
    obtain ⟨c, hc, hcG⟩ := polynomialZeroSet_nested_inter_nonempty I
      {c : Fin N × Fin N → K | LinearIndependent K (tup c)} hanti hne
    have hBc : ⇑(basisOfLinearIndependentOfCardEqFinrank hcG hcard) = tup c :=
      coe_basisOfLinearIndependentOfCardEqFinrank hcG hcard
    refine mem_sncWeightNormalizedProfiles_of_tendsto cY fY d hd D₀ hklt D y
      (basisOfLinearIndependentOfCardEqFinrank hcG hcard)
      (fun l i => ((scaledProfile α l i : ℚ) : ℝ)) _
      (fun l i => by exact_mod_cast scaledProfile_nonneg hα0 l i) (fun l => ?_)
      (tendsto_scaledProfile α) (hαpos.imp fun i hi => by exact_mod_cast hi)
    rw [hBc]
    exact (hmem l c).mp (Set.mem_iInter.mp hc l)

/-- The closedness of the normalized realization sets on closed points, from that of the sets of
points where some basis realizes a rational profile by test primes, given Lemma 3 at the closed
points. -/
theorem isClosedOnClosedPoints_normalizedProfiles_of_realized (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (D : CartierDivisor Y)
    (hclosed : ∀ y : Y, IsClosed ({y} : Set Y) → RealizationSetsZariskiClosed cY fY d D₀ D y)
    {N : ℕ} (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hP : ∀ β : Fin N → ℚ, (∀ i, 0 ≤ β i) → IsClosedOnClosedPoints {y : Y |
      ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY fY d D₀ D y B (fun i => (β i : ℝ))})
    (α : Fin N → ℚ) (hα0 : ∀ i, 0 ≤ α i) (hαpos : ∃ i, 0 < α i) :
    IsClosedOnClosedPoints {y : Y |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} := by
  obtain ⟨Z, hZ, hrep⟩ := isClosedOnClosedPoints_iInter _ fun l =>
    hP (scaledProfile α l) (scaledProfile_nonneg hα0 l)
  refine ⟨Z, hZ, fun y hy => ?_⟩
  rw [← hrep y hy, Set.mem_iInter]
  exact mem_sncWeightNormalizedProfiles_iff cY fY d hd D₀ hklt D y (hclosed y hy) b₀ α hα0 hαpos

end MixedFujita

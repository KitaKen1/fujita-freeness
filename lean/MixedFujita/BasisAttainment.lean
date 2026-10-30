/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizedProfiles
public import MixedFujita.HironakaSNCModelExistence

/-!
Attainment of the minimum over all bases (step 11, section 3.2 of the manuscript), from the
closedness of the realization sets.

Let (Y, pair) be klt over a field of characteristic zero, D a Cartier divisor whose space of
sections has a basis b₀ of N > 0 elements, x a point and t, j > 0. For a basis B of the sections
the profile data are the pairs (A(w), (v_i(w))_i) of the weights w over the fibre of x on the
proper simple normal crossing models of the pair and of the zero divisors of B, and the objective
is Φ(a, v) = Σ_i exp(a/t − v_i/j). Assume

* the closedness of the realization sets at x (`RealizationSetsZariskiClosed`, Lemma 3 of the
  manuscript for these families; a hypothesis here);
* uniform bounds below a level L: every datum (a, v) of every basis with Φ(a, v) ≤ L has
  a_* ≤ a ≤ a^* and 0 ≤ v_i ≤ C a (section 3.1);
* some datum of some basis has objective below L and below N (the interior condition).

Then some basis B* and some datum of B* have objective at most that of every datum of every basis:
the infimum over all bases and all weights is attained. The proper simple normal crossing model
of B* on which the limit weight lives is constructed by resolution.

The parameters of the abstract theorem are the coefficient matrices of the tuples with respect to
b₀; the tuples of linearly independent sections are the bases.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- Attainment of the minimum of the objective over all bases of the sections of D and all weights
over the fibre of x on their proper simple normal crossing models, from the closedness of the
realization sets, the uniform bounds of section 3.1 below a level L and the interior condition. -/
theorem exists_basis_sncWeightProfile_minimizer (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (D : CartierDivisor Y) (x : Y) {N : ℕ} (hN : 0 < N)
    (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤))
    (hclosed : RealizationSetsZariskiClosed cY fY d D₀ D x) {t j : ℝ} (ht : 0 < t) (hj : 0 < j)
    {L aLow aHigh Cq : ℝ} (haLow : 0 < aLow)
    (hbd : ∀ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
      ∀ p ∈ sncWeightProfiles cY fY d D₀ D x B, (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ L →
        aLow ≤ p.1 ∧ p.1 ≤ aHigh ∧ ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ Cq * p.1)
    (hint : ∃ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
      ∃ p ∈ sncWeightProfiles cY fY d D₀ D x B, (∑ i, Real.exp (p.1 / t - p.2 i / j)) < L ∧
        (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N) :
    ∃ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)), ∃ p ∈ sncWeightProfiles cY fY d D₀ D x B,
      ∀ (B' : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
        ∀ p' ∈ sncWeightProfiles cY fY d D₀ D x B',
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
  have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
    (Module.finrank_eq_card_basis b₀).symm
  -- the tuple of a coefficient matrix
  set tup : (Fin N × Fin N → K) → Fin N → Γ(D.sheaf, ⊤) :=
    fun c i => ∑ k, c (i, k) • b₀ k with htup
  -- bases and linearly independent tuples
  have hbasis : ∀ c : Fin N × Fin N → K, LinearIndependent K (tup c) →
      ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤), ⇑B = tup c := fun c hc =>
    ⟨basisOfLinearIndependentOfCardEqFinrank hc hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hc hcard⟩
  have hcoord : ∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∃ c : Fin N × Fin N → K, LinearIndependent K (tup c) ∧ tup c = ⇑B := by
    intro B
    have h : tup (fun ik => b₀.repr (B ik.1) ik.2) = ⇑B := by
      funext i
      exact b₀.sum_repr (B i)
    exact ⟨fun ik => b₀.repr (B ik.1) ik.2, by rw [h]; exact B.linearIndependent, h⟩
  obtain ⟨c, hcG, p, hp, hmin⟩ := exists_basis_profile_minimizer hN ht hj
    {c : Fin N × Fin N → K | LinearIndependent K (tup c)}
    (fun c => sncWeightProfiles cY fY d D₀ D x (tup c))
    (fun c α => IsRealizedProfile cY fY d D₀ D x (tup c) α)
    (fun α hα => hclosed N N b₀ α hα)
    (fun c α α' h hr => isRealizedProfile_antitone cY fY d D₀ D x (tup c) h hr)
    (by
      rintro c - p hp hp1 α - hα
      obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
        hBsupp, hGsupp, hw0, hwΦ, hA, hv⟩ := hp
      exact isRealizedProfile_of_sncWeight π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc hBsupp D (tup c)
        hs hGsupp x w hw0 hwΦ (by rw [← hA]; exact hp1) (fun i => by
          rw [← hA, ← hv i]
          exact hα i))
    (by
      intro c hc α q hα0 hreal hlim hqpos
      have hs : ∀ i, tup c i ≠ 0 := fun i => LinearIndependent.ne_zero i hc
      obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
        hGsupp⟩ := exists_proper_snc_model_with cY fY d D₀
          (fun i => cartierSectionZeroDivisor D (tup c i) (hs i))
      obtain ⟨u, hu0, huΦ, huA, huv⟩ := exists_normalized_sncWeight_of_tendsto_isRealizedProfile π
        hπ cY fY d hd D₀ hklt cX ξ hinj hξ hsnc hBsupp D (tup c) hs hGsupp x α q hα0 hreal hlim
        hqpos
      exact ⟨fun i => ∑ k, u k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (tup c i) (hs i))) (ξ k) : ℝ),
        ⟨hs, X, hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, u, hinj, hξ, hsnc,
          hBsupp, hGsupp, hu0, huΦ, huA.symm, fun i => rfl⟩, huv⟩)
    (fun c _ p hp lam hlam => sncWeightProfiles_smul cY fY d D₀ D x (tup c) hp hlam)
    haLow
    (by
      intro c hc p hp hL
      obtain ⟨B, hB⟩ := hbasis c hc
      exact hbd B p (by rw [hB]; exact hp) hL)
    (by
      obtain ⟨B, p, hp, h1, h2⟩ := hint
      obtain ⟨c, hcG, hc⟩ := hcoord B
      exact ⟨c, hcG, p, by rw [hc]; exact hp, h1, h2⟩)
  obtain ⟨B, hB⟩ := hbasis c hcG
  refine ⟨B, p, by rw [hB]; exact hp, fun B' p' hp' => ?_⟩
  obtain ⟨c', hc'G, hc'⟩ := hcoord B'
  exact hmin c' hc'G p' (by rw [hc']; exact hp')

end MixedFujita

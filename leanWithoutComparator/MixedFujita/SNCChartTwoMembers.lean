/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HyperplaneGenericPoint

/-!
A simple normal crossing chart in which two given members are the first two coordinates
(step 9, strict transform charts).

If a point t lies on the closures of two distinct members ξ_i, ξ_j of a simple normal crossing
family, an SNC chart at t assigns them coordinates (a member through the chart meets it in the
zero locus of its coordinate, so it cannot be unassigned), the coordinates are distinct, and
relabelling the coordinates by a permutation sending 0 and 1 to them gives a chart at t in which
ξ_i is the hyperplane y_0 = 0 and ξ_j is y_1 = 0 (`exists_snc_chart_two_members_at`): the chart of
the strict transform H' = ξ_i and the meeting component E = ξ_j at a point of H' ∩ E. The prime of
a point t of an affine open with y ∈ P_t maps to a prime of Γ(U)/(y), and an element lies in it
exactly when it comes from P_t (`mem_map_primeIdealOf_quotient_iff`): the prime 𝔓 of the point in
B = C/(y_0).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section TwoMembers

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

/-- At a point on the closures of two distinct members of a simple normal crossing family there is
an SNC chart in which the two members are the hyperplanes of the first two coordinates. -/
theorem exists_snc_chart_two_members_at {r : ℕ} (ξ : Fin r → X) (hsnc : IsSNCFamily K (n + 2) ξ)
    (t : X) (i j : Fin r) (hij : i ≠ j) (hi : t ∈ closure ({ξ i} : Set X))
    (hj : t ∈ closure ({ξ j} : Set X)) :
    ∃ (c : EtaleChart K X (n + 2)) (σ : Fin r → Option (Fin (n + 2))), t ∈ c.U ∧
      IsSNCChart c ξ σ ∧ σ i = some 0 ∧ σ j = some 1 := by
  classical
  obtain ⟨c, σ, htc, hc⟩ := hsnc t
  have hassigned : ∀ k, t ∈ closure ({ξ k} : Set X) → ∃ a, σ k = some a := by
    intro k hk
    cases h : σ k with
    | none =>
      exfalso
      have h2 := hc.2 k
      rw [h] at h2
      have : t ∈ closure ({ξ k} : Set X) ∩ c.U := ⟨hk, htc⟩
      rw [h2] at this
      exact this
    | some a => exact ⟨a, rfl⟩
  obtain ⟨a, ha⟩ := hassigned i hi
  obtain ⟨b, hb⟩ := hassigned j hj
  have hab : a ≠ b := by
    intro he
    exact hij (hc.1 i j a ha (he ▸ hb))
  -- a permutation sending 0 to a and 1 to b
  let e₁ : Fin (n + 2) ≃ Fin (n + 2) := Equiv.swap 0 a
  let b' : Fin (n + 2) := e₁ b
  have hb'0 : b' ≠ 0 := by
    intro h0
    apply hab
    have : e₁ b = e₁ a := by
      change b' = e₁ a
      rw [h0]
      simp [e₁]
    exact (e₁.injective this).symm
  let e₂ : Fin (n + 2) ≃ Fin (n + 2) := Equiv.swap 1 b'
  let e : Fin (n + 2) ≃ Fin (n + 2) := e₂.trans e₁
  have he0 : e 0 = a := by
    have h01 : (0 : Fin (n + 2)) ≠ 1 := by simp
    change e₁ (e₂ 0) = a
    rw [show e₂ 0 = 0 from Equiv.swap_apply_of_ne_of_ne h01 hb'0.symm]
    simp [e₁]
  have he1 : e 1 = b := by
    change e₁ (e₂ 1) = b
    rw [show e₂ 1 = b' from Equiv.swap_apply_left 1 b']
    simp [b', e₁]
  refine ⟨etaleChartReindex c e, fun k => (σ k).map e.symm, htc, isSNCChart_reindex c ξ σ hc e,
    ?_, ?_⟩
  · show (σ i).map e.symm = some 0
    rw [ha, Option.map_some, ← he0, Equiv.symm_apply_apply]
  · show (σ j).map e.symm = some 1
    rw [hb, Option.map_some, ← he1, Equiv.symm_apply_apply]

end TwoMembers

section PointPrime

/-- The prime of a point of an affine open containing y maps to a prime of the quotient by (y),
whose members are exactly the classes of members of the prime. -/
theorem mem_map_primeIdealOf_quotient_iff {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (t : X) (ht : t ∈ U) (y : Γ(X, U)) (hy : y ∈ (hU.primeIdealOf ⟨t, ht⟩).asIdeal)
    (f : Γ(X, U)) :
    Ideal.Quotient.mk (Ideal.span {y}) f ∈
        ((hU.primeIdealOf ⟨t, ht⟩).asIdeal.map (Ideal.Quotient.mk (Ideal.span {y}))) ↔
      f ∈ (hU.primeIdealOf ⟨t, ht⟩).asIdeal := by
  have hle : RingHom.ker (Ideal.Quotient.mk (Ideal.span {y})) ≤
      (hU.primeIdealOf ⟨t, ht⟩).asIdeal := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact hy
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨f', hf', he⟩
    have hd : f' - f ∈ RingHom.ker (Ideal.Quotient.mk (Ideal.span {y})) := by
      rw [RingHom.mem_ker, map_sub, he, sub_self]
    have := Ideal.sub_mem _ hf' (hle hd)
    simpa using this
  · intro hf
    exact ⟨f, hf, rfl⟩

end PointPrime

end MixedFujita

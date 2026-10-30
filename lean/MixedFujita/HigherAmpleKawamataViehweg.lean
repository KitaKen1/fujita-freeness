/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleKawamataViehweg

/-!
The ample SNC Kawamata--Viehweg statement in an arbitrary cohomological degree.
This is a new interface; the original degree-one statement is unchanged.
The signed-roundup reduction is degree independent. The characteristic-zero
proof is supplied by `KawamataViehwegCharZero`, using its existing all-degree
closed-fibre vanishing and cocycle specialization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Kawamata–Viehweg vanishing in degree `j` for an ample adjoint divisor with a fractional
simple normal crossing boundary: if `m (Q − K_T) − Σ a_k E_k` is ample with `0 ≤ a_k < m`, then
`Hʲ(T, O_T(Q)) = 0`. -/
def KawamataViehwegVanishingSNCAmpleInDegree (K : Type u) [Field K] (n j : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
    Function.Injective ξ → (∀ k, Order.coheight (ξ k) = 1) → IsSNCFamily K n ξ →
    ∀ E : Fin r → CartierDivisor T,
      (∀ (k : Fin r) (z : CodimensionOnePoint T),
        cartierCoefficient (E k) (z : T) = if (z : T) = ξ k then 1 else 0) →
    ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r → ℕ, (∀ k, a k < m) →
      CartierIsAmpleProj K (m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k) →
      Subsingleton (Scheme.Modules.Cohomology Q.sheaf j)

/-- **The ample Kawamata–Viehweg statement for a signed SNC boundary after adding its integer
roundup** (the argument of check-394 with an ample adjoint divisor). -/
theorem signed_snc_roundup_vanishing_of_ample_KV_inDegree
    (K : Type u) [Field K] {n j : ℕ} (hKV : KawamataViehwegVanishingSNCAmpleInDegree K n j)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B E Q : CartierDivisor T) (d : ℕ) (hd : 1 ≤ d)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient B (t : T) = 0)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉)
    (hamp : CartierIsAmpleProj K (d • (Q - smoothCanonicalDivisor cT) - B)) :
    Subsingleton (Scheme.Modules.Cohomology (Q + E).sheaf j) := by
  classical
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  let C := B + d • E
  have hc (t : CodimensionOnePoint T) : 0 ≤ cartierCoefficient C (t : T) ∧
      cartierCoefficient C (t : T) < (d : ℤ) := by
    rw [cartierCoefficient_add, cartierCoefficient_nsmul, hE t]
    exact boundary_add_roundup_coefficient_mem_Ico _ d hd
  let a : Fin r → ℕ := fun i => (cartierCoefficient C (ξ i)).toNat
  have haeq (i : Fin r) : (a i : ℤ) = cartierCoefficient C (ξ i) :=
    Int.toNat_of_nonneg (hc ⟨ξ i, hξ i⟩).1
  have ha (i : Fin r) : a i < d := by
    have h : (a i : ℤ) < (d : ℤ) := by rw [haeq]; exact (hc ⟨ξ i, hξ i⟩).2
    exact_mod_cast h
  obtain ⟨F, _, _, hFc⟩ := exists_snc_component_cartier (K := K) ξ hξ hsnc
  have heq : C = ∑ i, a i • F i := by
    apply cartierDivisor_eq_of_forall_coefficient_eq hnormT
    intro t
    have hcomb := cartierCoefficient_member_combination ξ hinj F hFc (fun i => (a i : ℤ)) t
    simp only [natCast_zsmul] at hcomb
    rcases hcomb with ⟨i, hti, hci⟩ | ⟨hti, hci⟩
    · rw [hci, hti]
      exact (haeq i).symm
    · rw [hci]
      have hB0 := hsupport t hti
      have hE0 : cartierCoefficient E (t : T) = 0 := by rw [hE t, hB0]; norm_num
      rw [cartierCoefficient_add, cartierCoefficient_nsmul, hB0, hE0, mul_zero, add_zero]
  have hadj : d • ((Q + E) - smoothCanonicalDivisor cT) - ∑ i, a i • F i =
      d • (Q - smoothCanonicalDivisor cT) - B := by rw [← heq]; dsimp [C]; module
  exact hKV T cT r ξ hinj hξ hsnc F hFc (Q + E) d hd a ha (hadj ▸ hamp)

end MixedFujita

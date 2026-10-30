/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KawamataViehwegStatement
public import MixedFujita.RoundupBoundaryNormalization
public import MixedFujita.NormalCartierCoefficientExt

/-! 通常KVから実roundup付き符号付きSNC境界のH1消滅。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open TopCat.Presheaf TopCat.Sheaf
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The usual SNC KV statement applies to an arbitrary signed SNC boundary
after adding its actual integer negative-boundary roundup. All effective
fractional component numerators and their equality are constructed internally. -/
theorem signed_snc_roundup_H1_vanishing_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B E Q : CartierDivisor T) (d : ℕ) (hd : 1 ≤ d)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉)
    (hnef : CartierIsNef K (d • (Q - smoothCanonicalDivisor cT) - B))
    (hbig : CartierIsBig K (d • (Q - smoothCanonicalDivisor cT) - B)) :
    Subsingleton (Scheme.Modules.Cohomology (Q + E).sheaf 1) := by
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
  exact hKV T cT r ξ hinj hξ hsnc F hFc (Q + E) d hd a ha
    (hadj ▸ hnef) (hadj ▸ hbig)

end MixedFujita

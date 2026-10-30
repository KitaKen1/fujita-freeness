/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierAmpleDefinition
public import MixedFujita.CartierSectionPowers
public import MixedFujita.CartierTauProducts

/-!
The multiplicity half of Lemma 1 on a log resolution, without a Segre embedding (step 5). Let T be
smooth with an ample divisor J (some multiple is a hyperplane class) and B a Cartier divisor such
that k J - B has a nonzero section τ for some k ≥ 1; this holds for B = ρ^*L when T is embedded
with hyperplane class J_T and k J_T - ρ^*L is effective, as for blow-ups, where J_T = ρ^*(mL) - E.
For a nonzero section s of j B the product s τ^j is a nonzero section of (j k) J, and multiplying
by a section never lowers the order of vanishing. So the uniform bound ord_z ≤ c D for sections of
D J gives ord_z(s) ≤ (c k) j at every closed point, uniformly in z and j: the bound
mult_z(ρ^*s) ≤ C j used in Lemma 1 on T, for the pulled-back sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section Product

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Multiplying by a section never lowers the order of vanishing. -/
theorem cartierSectionVanishingOrder_le_product (D E : CartierDivisor X) (x : X)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s ≤
      cartierSectionVanishingOrder (D + E) x (cartierSectionProduct D E s t) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt x
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    cartierSectionVanishingOrder_eq_localCoefficient (D + E) x (f * g) (hf.mul hg),
    cartierSectionProduct_localCoefficient D E x f g hf hg]
  rw [← ENat.forall_natCast_le_iff_le]
  intro d hd
  rw [localAdicOrder_nat_le_iff] at hd ⊢
  exact Ideal.mul_mem_right _ _ hd

end Product

set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The order bound for multiples of B when k J - B is effective for an ample J on smooth Y. -/
theorem vanishingOrder_le_of_effective_difference [Smooth (Y ↘ Spec (CommRingCat.of K))] {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {J : CartierDivisor Y}
    (hJ : CartierIsAmpleProj K J) (B : CartierDivisor Y) {k : ℕ} (hk : 1 ≤ k)
    (τ : Γ((k • J - B).sheaf, ⊤)) (hτ : τ ≠ 0) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ j : ℕ, 1 ≤ j → ∀ s : Γ((j • B).sheaf, ⊤), s ≠ 0 →
      cartierSectionVanishingOrder (j • B) x s ≤ ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := cartierIsAmpleProj_vanishingOrder_le (K := K) hn hd hJ
  refine ⟨c * k, fun x hx j hj s hs => ?_⟩
  have hsum : B + (k • J - B) = k • J := by abel
  have hdiv : j • B + j • (k • J - B) = (j * k) • J := by
    rw [← smul_add, hsum, smul_smul]
  set t := cartierSectionPower (k • J - B) τ j with ht
  have hu : cartierSectionCast hdiv (cartierSectionProduct (j • B) (j • (k • J - B)) s t) ≠ 0 :=
    cartierSectionCast_ne_zero _ _
      (cartierSectionProduct_ne_zero _ _ _ _ hs (cartierSectionPower_ne_zero _ _ hτ j))
  have h1 := cartierSectionVanishingOrder_le_product (j • B) (j • (k • J - B)) x s t
  have h2 := hc x hx (j * k) (Nat.mul_pos hj hk) _ hu
  rw [cartierSectionCast_vanishingOrder] at h2
  calc cartierSectionVanishingOrder (j • B) x s
      ≤ cartierSectionVanishingOrder (j • B + j • (k • J - B)) x
          (cartierSectionProduct (j • B) (j • (k • J - B)) s t) := h1
    _ ≤ ((c * (j * k) : ℕ) : ℕ∞) := h2
    _ = ((c * k * j : ℕ) : ℕ∞) := by rw [mul_comm j k, mul_assoc]

end MixedFujita

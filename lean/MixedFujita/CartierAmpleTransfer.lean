/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveSectionOrderBound

/-!
Transfer of the uniform order bound to a divisor with a multiple linearly equivalent to the
hyperplane class. If m·A = J + div f with m ≥ 1, the m-th power of a section s of j·A,
multiplied by f^j, is a section t of j·J with the same local coefficient as s^m. Hence
m · ord_x(s) = ord_x(t) ≤ c j at every closed point, with c from the hyperplane class. This is
Lemma 1's multiplicity bound for the ample divisor A of the manuscript on the smooth variety
itself.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Uniform linear order bound for the sections of the multiples of a divisor A with
m·A = J + div f. -/
theorem cartierMultiple_vanishingOrder_le
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (A : CartierDivisor Y) {m : ℕ} (hm : 1 ≤ m) (f : Y.functionFieldˣ)
    (hA : m • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y f) :
    ∃ c : ℕ, ∀ x : Y, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
      ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 →
        cartierSectionVanishingOrder (j • A) x s ≤ ((c * j : ℕ) : ℕ∞) := by
  obtain ⟨c, hc⟩ := projectiveHyperplane_cartierOrder_le e g hg hggen he hn hd
  refine ⟨c, fun x hx j hj s hs => ?_⟩
  have hdiv : m • (j • A) = j • projectiveHyperplaneCartier e g hg hggen +
      principalCartierDivisor Y (f ^ j) := by
    rw [← mul_nsmul, mul_comm, mul_nsmul, hA, nsmul_add, principalCartierDivisor_power]
  -- s^m, as a rational section of j·J + div f^j, times f^j
  have hmem : (rationalFunctionsEquiv (X := Y) ⊤).symm
      (cartierSectionRational (j • A) s ^ m) ∈
        (j • projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y (f ^ j)).sections ⊤ := by
    rw [← hdiv]
    exact cartierSectionPower_mem_sections (j • A) s m
  have hmem' := (cartierSections_mem_principalShift
    (j • projectiveHyperplaneCartier e g hg hggen) (f ^ j) ⊤ _).mp hmem
  obtain ⟨t, htdef⟩ : ∃ t : Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      t = CartierDivisor.sectionMk _ hmem' := ⟨_, rfl⟩
  have ht : cartierSectionRational (j • projectiveHyperplaneCartier e g hg hggen) t =
      ((f ^ j : Y.functionFieldˣ) : Y.functionField) * cartierSectionRational (j • A) s ^ m := by
    rw [htdef, cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk,
      rationalFunctionsEquiv_rationalFunctionsMul_app, LinearEquiv.apply_symm_apply]
  have hr : cartierSectionRational (j • A) s ≠ 0 :=
    (map_ne_zero_iff _ (cartierSectionRational_injective _)).mpr hs
  have ht0 : t ≠ 0 := by
    intro h0
    have h := congrArg (cartierSectionRational (j • projectiveHyperplaneCartier e g hg hggen)) h0
    rw [ht, map_zero] at h
    exact (mul_ne_zero (Units.ne_zero _) (pow_ne_zero m hr)) h
  have hbound := hc x hx j hj t ht0
  -- the orders agree: ord_x t = m · ord_x s
  have hord : cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x t =
      m • cartierSectionVanishingOrder (j • A) x s := by
    obtain ⟨u, hu⟩ := (projectiveHyperplaneCartier e g hg hggen).exists_isLocalEquationAt x
    have huj := cartierLocalEquation_pow _ x u hu j
    have hloc : (m • (j • A)).IsLocalEquationAt x (u ^ j * f ^ j) := by
      rw [hdiv]
      exact huj.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x _)
    let := smoothScheme_stalk_isNoetherianRing (K := K) x
    obtain ⟨_, _, coords, _, _⟩ := geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) d hn
      (projectiveHyperplaneCartier e g hg hggen) x hx
    rw [← cartierSectionVanishingOrder_power (j • A) x coords s m,
      cartierSectionVanishingOrder_eq_localCoefficient _ x _ huj t,
      cartierSectionVanishingOrder_eq_localCoefficient _ x _ hloc]
    congr 1
    apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image, ht,
      cartierSectionPower_rational, Units.val_mul, mul_assoc]
  rw [hord] at hbound
  calc cartierSectionVanishingOrder (j • A) x s
      = 1 • cartierSectionVanishingOrder (j • A) x s := (one_nsmul _).symm
    _ ≤ m • cartierSectionVanishingOrder (j • A) x s := nsmul_le_nsmul_left zero_le hm
    _ ≤ _ := hbound

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessAmple
public import MixedFujita.ZeroDimensionalCartierFreeness
public import MixedFujita.IitakaGrowth

/-!
Construct the Iitaka growth exponent of an actual ample Cartier divisor in positive dimension.
The upper estimate extracts the section-product argument already used for uniqueness of the
exponent: embed jD into jMD for one fixed very ample MD and use the actual projective Hilbert
bound. Bigness supplies the frequent lower bound. No Iitaka-dimension premise is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- A full polynomial upper bound for the sections of every multiple of an ample divisor. -/
theorem cartierIsAmpleProj_finrank_polynomial_upper {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) {D : CartierDivisor X}
    (hD : CartierIsAmpleProj K D) :
    ∃ C : ℝ, ∀ j : ℕ, (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      C * ((j : ℝ) + 1) ^ n := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_veryAmple hD
  obtain ⟨j₁, hj₁⟩ := cartierIsAmpleProj_eventually_globallyGenerated hD
  let M := j₀ + j₁ + 1
  obtain ⟨Nv, e, he, hbase, g, hg, hggen, f, hMD⟩ := hj₀ M (by dsimp [M]; omega)
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (hj₁ (M - 1) (by dsimp [M]; omega))
  obtain ⟨-, -, hfinJ, -⟩ :=
    projectiveHyperplane_hilbert_leading_integral e g hg hggen hbase hdim hn
  obtain ⟨C, hC⟩ := projectiveHyperplane_exists_finrank_le_mul_pow e g hg hggen hbase hdim hn
  refine ⟨C, fun j => ?_⟩
  have hjM : j • D + j • ((M - 1) • D) = j • (M • D) := by
    rw [← nsmul_add, ← succ_nsmul', Nat.sub_add_cancel (show 1 ≤ M by dsimp [M]; omega)]
  have hdiv : j • D + j • ((M - 1) • D) =
      j • projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor X (f ^ j) := by
    rw [hjM, hMD, nsmul_add, principalCartierDivisor_power]
  have := hfinJ j
  have hfinT : FiniteDimensional K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) := by
    rw [hdiv]
    exact Module.Finite.equiv (cartierPrincipalShiftEquiv (K := K) _ _).symm
  have hle := finrank_le_of_eq_add_of_section (K := K) (j • D) (j • ((M - 1) • D)) _ rfl
    (cartierSectionPower _ t j) (cartierSectionPower_ne_zero _ t ht j) hfinT
  have heq : Module.finrank K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) =
      Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    rw [hdiv, finrank_add_principal]
  have hleR : (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    exact_mod_cast hle.trans heq.le
  exact hleR.trans (hC j)

/-- Positive-dimensional ample divisors have an internally constructed Iitaka exponent. -/
theorem cartierIsAmpleProj_iitakaDimension {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) {D : CartierDivisor X}
    (hD : CartierIsAmpleProj K D) : CartierIitakaDimension K D n := by
  obtain ⟨d, hd, c, hc, hlow⟩ := cartierIsAmpleProj_isBig hdim hn hD
  have hdn : d = n := by exact_mod_cast hd.symm.trans hdim
  subst d
  exact ⟨⟨c, hc, hlow⟩, cartierIsAmpleProj_finrank_polynomial_upper hdim hn hD⟩

omit [IsAlgClosed K] in
/-- In dimension zero every Cartier divisor is zero, so any Iitaka growth exponent is zero.
No finite-dimensionality or existence of an exponent is assumed. -/
theorem zeroDimensional_cartierIitakaDimension_eq_zero
    (hdim : topologicalKrullDim X = 0) {D : CartierDivisor X} {k : ℕ}
    (hk : CartierIitakaDimension K D k) : k = 0 := by
  have hD := zeroDimensional_cartierDivisor_eq_zero hdim D
  subst D
  obtain ⟨⟨c, hc, hlow⟩, C, hupp⟩ := hk
  have hupper (j : ℕ) :
      (Module.finrank K Γ((j • (0 : CartierDivisor X)).sheaf, ⊤) : ℝ) ≤
        (Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) : ℝ) * ((j : ℝ) + 1) ^ 0 := by
    rw [show j • (0 : CartierDivisor X) = 0 from smul_zero j]
    simp only [pow_zero, mul_one, le_refl]
  have hle : k ≤ 0 := polynomialGrowth_lower_exponent_le (by positivity) hc hlow hupper
  omega

omit [IsAlgClosed K] in
/-- Finite dimensionality of the actual zero-dimensional section space constructs its
Iitaka exponent; no dimension-one or smoothness hypothesis is used. -/
theorem zeroDimensional_cartierIitakaDimension_of_finiteDimensional
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X)
    (hfin : FiniteDimensional K Γ(D.sheaf, ⊤)) : CartierIitakaDimension K D 0 := by
  have hD := zeroDimensional_cartierDivisor_eq_zero hdim D
  subst D
  letI := hfin
  have hpos : 0 < Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      (cartierIsGloballyGenerated_exists_nonzero_section zeroCartierDivisor_globallyGenerated)
  have hrank (j : ℕ) : Module.finrank K Γ((j • (0 : CartierDivisor X)).sheaf, ⊤) =
      Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) := by
    rw [show j • (0 : CartierDivisor X) = 0 from smul_zero j]
  constructor
  · refine ⟨1, one_pos, Filter.Frequently.of_forall (fun j => ?_)⟩
    rw [hrank]
    simp only [pow_zero, mul_one]
    exact_mod_cast hpos
  · refine ⟨(Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) : ℝ), fun j => ?_⟩
    rw [hrank]
    simp only [pow_zero, mul_one, le_refl]

end MixedFujita

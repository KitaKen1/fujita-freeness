/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PositiveIitakaFirstMixedIntersection
public import MixedFujita.ProjectiveAllDimensionSectionBounds
public import MixedFujita.BigSemiampleNumericalDimension

/-! 全次元のκ=1と正常射影曲線・曲面の元ν=κ。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The ORIGINAL numerical and Iitaka dimensions agree at exponent ONE
in every positive ambient dimension, including intermediate dimension. -/
theorem proper_semiample_iitaka_one_numerical_dimension_eq_one
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (hkappa : CartierIitakaDimension K D 1) :
    cartierNumericalDimension K n hdim D J = 1 := by
  exact le_antisymm
    (proper_semiample_cartierNumericalDimension_le_iitaka K n hdim hn hnorm D J hJ hD 1 hkappa)
    (proper_semiample_positive_iitaka_numerical_dimension_pos K n hdim hn hnorm D J hJ hD 1 le_rfl hkappa)


/-- Numerical dimension zero is equivalent to original Iitaka exponent
zero for ORIGINAL semiample divisors; curve-test numerical triviality is
not substituted for the manuscript mixed-intersection definition. -/
theorem proper_semiample_numerical_dimension_zero_iff_iitaka_zero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) :
    cartierNumericalDimension K n hdim D J = 0 ↔ k = 0 := by
  constructor
  · intro hzero
    by_contra hk
    have hpos := proper_semiample_positive_iitaka_numerical_dimension_pos
      K n hdim hn hnorm D J hJ hD k (by omega) hkappa
    omega
  · intro hk
    subst k
    exact proper_semiample_iitaka_zero_cartierNumericalDimension_eq_zero K n hdim hn hnorm D J hJ hD hkappa


/-- The ORIGINAL Iitaka growth exponent is bounded by the ordinary
dimension, using the already proved actual affine Cartier section bound. -/
theorem proper_cartierIitakaDimension_le_dim
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (D : CartierDivisor X) (k : ℕ) (hkappa : CartierIitakaDimension K D k) : k ≤ n := by
  obtain ⟨C, hC, hupper⟩ := cartier_affineMultiples_finrank_polynomial_upper_all_dimensions
    hdim ⟨J, hJ⟩ D 0
  obtain ⟨c, hc, hlower⟩ := hkappa.1
  have hu : ∀ j : ℕ, (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤ C * ((j : ℝ) + 1) ^ n := by
    intro j
    have he := congrArg (fun F : CartierDivisor X =>
      (Module.finrank K Γ(F.sheaf, ⊤) : ℝ)) (add_zero (j • D))
    exact he ▸ hupper j
  exact polynomialGrowth_lower_exponent_le (by positivity) hc hlower hu


/-- The ORIGINAL intersection-theoretic nu equals the ORIGINAL Iitaka
exponent for ALL semiample divisors on normal projective CURVES AND
SURFACES in characteristic zero. Every possible exponent is covered. -/
theorem proper_semiample_numerical_dimension_eq_iitaka_of_dim_le_two
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) (hn2 : n ≤ 2)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) :
    cartierNumericalDimension K n hdim D J = k := by
  have hkn := proper_cartierIitakaDimension_le_dim K n hdim J hJ D k hkappa
  by_cases hk0 : k = 0
  · subst k
    exact proper_semiample_iitaka_zero_cartierNumericalDimension_eq_zero K n hdim hn hnorm D J hJ hD hkappa
  by_cases hk1 : k = 1
  · subst k
    exact proper_semiample_iitaka_one_numerical_dimension_eq_one K n hdim hn hnorm D J hJ hD hkappa
  have hkn' : k = n := by omega
  subst k
  exact (proper_semiample_full_iitaka_numerical_dimension_eq K n hdim hn hnorm D J hJ hD hkappa).1

end MixedFujita

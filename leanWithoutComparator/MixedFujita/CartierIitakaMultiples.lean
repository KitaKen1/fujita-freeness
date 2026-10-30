/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialGrowthDilation
public import MixedFujita.CartierBigOperations
public import MixedFujita.KltIsolationGeneration

/-!
The actual growth definition of Iitaka dimension is unchanged by every positive multiple of
any Cartier divisor with finite-dimensional graded sections. In each degree with a nonzero
section s, multiply by s^(q-1) to embed that entire section space into degree qj. Degrees with
no sections have dimension zero. Thus neither global generation, semiampleness nor any
coherent-direct-image estimate is needed for the comparison. An ambient ample divisor supplies
finite dimensionality internally in the ordinary positive-dimensional projective setting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Raising one actual nonzero degree-j section to power q-1 embeds the entire degree-j
section space into degree qj; the zero-section case has dimension zero. -/
theorem cartier_finrank_le_positive_multiple
    (D : CartierDivisor X) {q : ℕ} (hq : 0 < q) (j : ℕ)
    (hfin : FiniteDimensional K Γ(((q * j) • D).sheaf, ⊤)) :
    Module.finrank K Γ((j • D).sheaf, ⊤) ≤
      Module.finrank K Γ(((q * j) • D).sheaf, ⊤) := by
  by_cases hex : ∃ s : Γ((j • D).sheaf, ⊤), s ≠ 0
  · obtain ⟨s, hs⟩ := hex
    apply finrank_le_of_eq_add_of_section (K := K) (j • D) ((q - 1) • (j • D))
      ((q * j) • D) _ (cartierSectionPower _ s (q - 1))
      (cartierSectionPower_ne_zero _ s hs (q - 1)) hfin
    rw [mul_nsmul', ← succ_nsmul', Nat.sub_add_cancel (show 1 ≤ q from hq)]
  · have hall (s : Γ((j • D).sheaf, ⊤)) : s = 0 := by
      by_contra hs
      exact hex ⟨s, hs⟩
    have : Subsingleton Γ((j • D).sheaf, ⊤) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _

/-- Every positive multiple has exactly the same Iitaka growth exponent. -/
theorem cartierIitakaDimension_nsmul_iff
    (D : CartierDivisor X)
    (hfin : ∀ j : ℕ, FiniteDimensional K Γ((j • D).sheaf, ⊤))
    {q : ℕ} (hq : 0 < q) (k : ℕ) :
    CartierIitakaDimension K D k ↔ CartierIitakaDimension K (q • D) k := by
  have hshift (j : ℕ) : (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ(((q * (j + 0)) • D).sheaf, ⊤) := by
    exact_mod_cast cartier_finrank_le_positive_multiple D hq j (hfin _)
  have h := polynomialGrowth_positive_dilation_iff (f := fun j : ℕ =>
    (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ)) (k := k) (by positivity) hq hshift
  have hmul (j : ℕ) : (q * j) • D = j • (q • D) := by
    rw [Nat.mul_comm q j, mul_nsmul']
  have hrank (j : ℕ) : Module.finrank K Γ(((q * j) • D).sheaf, ⊤) =
      Module.finrank K Γ((j • (q • D)).sheaf, ⊤) := by rw [hmul j]
  simpa only [CartierIitakaDimension, hrank] using h

/-- In the positive-dimensional projective setting, the ordinary ample hypothesis supplies
finite dimensionality internally; it is not an additional unproved geometric input. -/
theorem cartierIitakaDimension_nsmul_iff_of_ample_ambient
    [Infinite K] {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    {q : ℕ} (hq : 0 < q) (k : ℕ) :
    CartierIitakaDimension K D k ↔ CartierIitakaDimension K (q • D) k :=
  cartierIitakaDimension_nsmul_iff D
    (fun j => cartier_finiteDimensional_sections_of_ample hdim hn hA (j • D)) hq k

end MixedFujita

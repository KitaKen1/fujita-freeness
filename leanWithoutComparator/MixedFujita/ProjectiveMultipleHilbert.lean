/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ResidueSandwich
public import MixedFujita.ProjectiveSubspaceBound
public import MixedFujita.CartierGradedSections

/-!
Hilbert asymptotics for all multiples of a Cartier divisor A whose multiple k A is the hyperplane
class J of an actual smooth integral closed subscheme of polynomial projective space over an
algebraically closed field. If m A has a nonzero section for every m ≥ e₀, multiplication by it
embeds Γ(j A) into Γ((j + m) A); choosing j + m a multiple of k shows that every Γ(j A) is finite
dimensional, and the residue sandwich carries h^0(q J) ~ r q^d / d! to
h^0(j A) ~ r j^d / (k^d d!) for all j. The existence of the nonzero sections in all large degrees
is the input (for an ample A it follows from Serre vanishing).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
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

/-- Hilbert asymptotics for all multiples of A when k A is the hyperplane class and m A has a
nonzero section for every m ≥ e₀. -/
theorem projectiveHyperplane_hilbert_of_multiple
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (A : CartierDivisor Y) {k : ℕ}
    (hk : 0 < k) (hkA : k • A = projectiveHyperplaneCartier e g hg hggen) (e₀ : ℕ)
    (hsec : ∀ m, e₀ ≤ m → ∃ σ : Γ((m • A).sheaf, ⊤), σ ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ _ : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K Γ((D • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d) atTop
        (𝓝 ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) := by
  obtain ⟨r, hr, hfinJ, hlimJ⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  set J := projectiveHyperplaneCartier e g hg hggen with hJ
  have hmul : ∀ q : ℕ, (k * q) • A = q • J := by
    intro q
    rw [mul_comm, mul_smul, hkA]
  have hfinMul : ∀ q : ℕ, FiniteDimensional K Γ(((k * q) • A).sheaf, ⊤) := by
    intro q
    rw [hmul q]
    exact hfinJ q
  -- every multiple is finite dimensional
  have hfin : ∀ D : ℕ, FiniteDimensional K Γ((D • A).sheaf, ⊤) := by
    intro D
    set m := k * (D + e₀ + 1) - D with hm
    have hmD : m + D = k * (D + e₀ + 1) := by
      have : D + e₀ + 1 ≤ k * (D + e₀ + 1) := Nat.le_mul_of_pos_left _ hk
      omega
    have hme : e₀ ≤ m := by
      have : D + e₀ + 1 ≤ k * (D + e₀ + 1) := Nat.le_mul_of_pos_left _ hk
      omega
    obtain ⟨σ, hσ⟩ := hsec m hme
    have hcod : FiniteDimensional K Γ(((m + D) • A).sheaf, ⊤) := by
      rw [hmD]
      exact hfinMul _
    exact Module.Finite.of_injective (cartierNsmulProductLinear (K := K) A m D σ)
      (cartierNsmulProduct_injective A m D σ hσ)
  refine ⟨r, hr, hfin, ?_⟩
  set h : ℕ → ℝ := fun D => (Module.finrank K Γ((D • A).sheaf, ⊤) : ℝ) with hh
  have hmono : ∀ j m, e₀ ≤ m → h j ≤ h (j + m) := by
    intro j m hm
    obtain ⟨σ, hσ⟩ := hsec m hm
    have hle := LinearMap.finrank_le_finrank_of_injective
      (f := cartierNsmulProductLinear (K := K) A m j σ)
      (cartierNsmulProduct_injective A m j σ hσ)
    simp only [hh]
    rw [add_comm j m]
    exact_mod_cast hle
  have hlim : Tendsto (fun q : ℕ => h (k * q) / ((k * q : ℕ) : ℝ) ^ d) atTop
      (𝓝 ((r : ℝ) / d.factorial / (k : ℝ) ^ d)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hfun : ∀ q : ℕ, h (k * q) / ((k * q : ℕ) : ℝ) ^ d =
        (Module.finrank K Γ((q • J).sheaf, ⊤) : ℝ) / (q : ℝ) ^ d / (k : ℝ) ^ d := by
      intro q
      simp only [hh]
      rw [show Module.finrank K Γ(((k * q) • A).sheaf, ⊤) =
          Module.finrank K Γ((q • J).sheaf, ⊤) by rw [hmul q]]
      push_cast
      rw [mul_pow, div_div, mul_comm ((k : ℝ) ^ d)]
    simp only [hfun]
    exact hlimJ.div_const _
  exact tendsto_of_residue_sandwich hk e₀ hmono hlim

end MixedFujita

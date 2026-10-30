/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalSteinGradedCartierDescent
public import MixedFujita.CartierIitakaMultiples
public import MixedFujita.AmpleIitakaExistence
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
For an eventually free divisor in the ordinary positive-dimensional projective setting,
the internally constructed Stein target of a positive free multiple has the same Iitaka growth
as the original divisor D. No finite-dimensionality premise, Iitaka exponent or contraction
map is supplied. If the geometric dimension of this constructed target is a positive integer d,
construct Iitaka(D)=d and identify any supplied Iitaka exponent with d. The dimension theorem below constructs the finite dimension witness and handles the zero-dimensional
target too, identifying its actual dimension with any supplied Iitaka exponent of D. Descent of
D itself rather than its one chosen positive multiple remains open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseSectionScalarTower

/-- The original D, and not only its chosen free multiple, has the Iitaka growth of the
same actual ample divisor on the internally constructed normal Stein target. -/
theorem eventuallyGloballyGenerated_exists_normal_stein_iitaka_descent
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ q : ℕ, 0 < q ∧ ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsProper (Y ↘ Spec (CommRingCat.of K)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      q • D = cartierPullback g H + principalCartierDivisor X φ ∧
      (∀ j : ℕ, Nonempty (Γ((j • (q • D)).sheaf, ⊤) ≃ₗ[K] Γ((j • H).sheaf, ⊤))) ∧
      (∀ j : ℕ, CartierIsGloballyGenerated (j • (q • D)) ↔ CartierIsGloballyGenerated (j • H)) ∧
      (∀ k : ℕ, CartierIitakaDimension K D k ↔ CartierIitakaDimension K H k) ∧
      ∀ d : ℕ, topologicalKrullDim Y = d → 1 ≤ d →
        CartierIitakaDimension K D d ∧
          ∀ k : ℕ, CartierIitakaDimension K D k → k = d := by
  obtain ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc, hgraded, hgen, hiitaka⟩ :=
    eventuallyGloballyGenerated_exists_normal_stein_divisible_graded_descent (K := K) D hfree hnorm
  letI := hY
  letI := hYN
  letI := hYO
  letI := hYft
  letI := hgd
  letI := hgo
  have hcomp (k : ℕ) : CartierIitakaDimension K D k ↔ CartierIitakaDimension K H k :=
    (cartierIitakaDimension_nsmul_iff_of_ample_ambient hdim hn hA D hq k).trans
      (hiitaka k)
  refine ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc, hgraded, hgen, hcomp, ?_⟩
  intro d hdimY hd
  have hκ : CartierIitakaDimension K D d :=
    (hcomp d).mpr (cartierIsAmpleProj_iitakaDimension hdimY hd hamp)
  exact ⟨hκ, fun k hk => CartierIitakaDimension_unique K hk hκ⟩

/-- The dimension of the internally constructed normal Stein target is the supplied Iitaka
dimension of the original D. The finite dimension witness is obtained from the existing
dimension/transcendence-degree theorem; the zero-dimensional case needs no finite-dimensional
cohomology assumption. This does not yet descend D itself. -/
theorem eventuallyGloballyGenerated_exists_normal_stein_target_dimension
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {k : ℕ} (hk : CartierIitakaDimension K D k) :
    ∃ q : ℕ, 0 < q ∧ ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      topologicalKrullDim Y = k ∧ IsProper g ∧ IsProper (Y ↘ Spec (CommRingCat.of K)) ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧ H.IsEffective ∧
      CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      q • D = cartierPullback g H + principalCartierDivisor X φ := by
  obtain ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc, hgraded, hgen, hiitaka, hdimtest⟩ :=
    eventuallyGloballyGenerated_exists_normal_stein_iitaka_descent hdim hn hA D hfree hnorm
  letI := hY
  letI := hYN
  letI := hYO
  letI := hYft
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim Y = d :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  have hkd : k = d := by
    by_cases hd0 : d = 0
    · subst d
      exact zeroDimensional_cartierIitakaDimension_eq_zero hd ((hiitaka k).mp hk)
    · exact (hdimtest d hd (by omega)).2 k hk
  refine ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    ?_, hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc⟩
  simpa only [hkd] using hd

/-- Eventual freeness constructs an Iitaka exponent in every dimension of the actual Stein
target, including zero. No growth or Iitaka-dimension input is supplied. -/
theorem eventuallyGloballyGenerated_exists_iitakaDimension_of_normal_projective
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ k : ℕ, CartierIitakaDimension K D k := by
  obtain ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc, hgraded, hgen, hiitaka, hdimtest⟩ :=
    eventuallyGloballyGenerated_exists_normal_stein_iitaka_descent hdim hn hA D hfree hnorm
  letI := hY
  letI := hYN
  letI := hYO
  letI := hYft
  obtain ⟨d, hd⟩ : ∃ d : ℕ, topologicalKrullDim Y = d :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  refine ⟨d, ?_⟩
  by_cases hd0 : d = 0
  · subst d
    obtain ⟨e⟩ := hgraded 1
    have hfinX : FiniteDimensional K Γ((1 • (q • D)).sheaf, ⊤) := by
      rw [one_nsmul]
      exact cartier_finiteDimensional_sections_of_ample hdim hn hA (q • D)
    letI := hfinX
    have hfinH : FiniteDimensional K Γ((1 • H).sheaf, ⊤) := Module.Finite.equiv e
    rw [one_nsmul] at hfinH
    exact (hiitaka 0).mpr
      (zeroDimensional_cartierIitakaDimension_of_finiteDimensional hd H hfinH)
  · exact (hdimtest d hd (by omega)).1

end MixedFujita

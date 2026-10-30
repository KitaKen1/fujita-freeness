/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierAtlasCocycle
public import MixedFujita.LogCechRestriction
public import MixedFujita.IntegerJacobsonResidueField
public import MixedFujita.ProjectiveClosureSmooth

/-!
Lemmas for the assembly of the model (step 10, R4-7).

* `exists_mem_basicOpen_of_span`: functions spanning the unit ideal on the standard charts give basic
  opens covering the scheme (so do charts on these basic opens).
* `isSNCChart_congr`: simple normal crossing position depends only on the open and the coordinates,
  so it passes to a chart on the same open whose coordinates are the restrictions.
* `exists_isMaximal_notMem`: a nonzero element of a domain of finite type over `ℤ` lies outside some
  maximal ideal (`ℤ` is a Jacobson ring, check 501).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section Cover

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {P : ℕ}
  (e : X ⟶ polynomialProjectiveScheme P R) [IsClosedImmersion e]

/-- **Functions spanning the unit ideal on each standard chart give basic opens covering the
scheme.** -/
theorem exists_mem_basicOpen_of_span {mm : Fin P → ℕ}
    (s : ∀ k, Fin (mm k) → Γ(X, projectivePullbackCoordinateOpen e k))
    (hs : ∀ k, Ideal.span (Set.range (s k)) = ⊤) (x : X) :
    ∃ k j, x ∈ X.basicOpen (s k j) := by
  have hx : x ∈ ⨆ k, projectivePullbackCoordinateOpen e k := by
    rw [iSup_projectivePullbackCoordinateOpen]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hV := projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k
  have hcov : ⨆ f : Set.range (s k), X.basicOpen (f : Γ(X, projectivePullbackCoordinateOpen e k)) =
      projectivePullbackCoordinateOpen e k :=
    hV.iSup_basicOpen_eq_self_iff.mpr (hs k)
  rw [← hcov] at hk
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hk
  exact ⟨k, j, hj⟩

end Cover

section SNC

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- **Simple normal crossing position passes to a chart on the same open with the restricted
coordinates.** -/
theorem isSNCChart_congr [IsIntegral X] {c c' : EtaleChart K X n} (hU : c'.U = c.U)
    (hcoords : ∀ a, c'.coords (MvPolynomial.X a) =
      (X.presheaf.map (homOfLE hU.le).op).hom (c.coords (MvPolynomial.X a)))
    {r : ℕ} {ξ : Fin r → X} {σ : Fin r → Option (Fin n)} (h : IsSNCChart c ξ σ) :
    IsSNCChart c' ξ σ := by
  have h' := isSNCChart_etaleChartRestrict h c'.U c'.isAffine c'.nonempty hU.le
  refine ⟨h'.1, fun i => ?_⟩
  have hi := h'.2 i
  change closure ({ξ i} : Set X) ∩ c'.U = (σ i).elim ∅ (fun a => X.zeroLocus
    ({(sectionRestrict K hU.le) (c.coords (MvPolynomial.X a))} : Set Γ(X, c'.U)) ∩ c'.U) at hi
  rw [hi]
  cases σ i with
  | none => rfl
  | some a =>
    simp only [Option.elim_some]
    rw [hcoords a]
    rfl

end SNC

section Maximal

variable {R : Type*} [CommRing R]

/-- **A nonzero element of a domain of finite type over `ℤ` lies outside some maximal ideal.** -/
theorem exists_isMaximal_notMem [IsDomain R] [Algebra.FiniteType ℤ R] {F : R} (hF : F ≠ 0) :
    ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ F ∉ 𝔪 := by
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  have hbot : (⊥ : Ideal R).jacobson = ⊥ :=
    (isJacobsonRing_iff_prime_eq.mp this) ⊥ Ideal.isPrime_bot
  have hF' : F ∉ (⊥ : Ideal R).jacobson := by
    rw [hbot, Ideal.mem_bot]
    exact hF
  rw [Ideal.jacobson, Submodule.mem_sInf] at hF'
  push Not at hF'
  obtain ⟨𝔪, ⟨-, h𝔪⟩, hF𝔪⟩ := hF'
  exact ⟨𝔪, h𝔪, hF𝔪⟩

end Maximal

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.VeryGeneralPoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
Very general closed points of an integral scheme of finite type over an uncountable algebraically
closed field (§2.3 (6), §5.1). Countably many proper closed subsets Z_k of W are avoided by some
closed point. Take a nonempty affine open U = Spec A; A is a finitely generated K-domain, and the
preimage of each Z_k is a proper closed subset of Spec A, since U is dense in the irreducible W, so
its vanishing ideal is nonzero. A maximal ideal of A outside all these ideals is a closed point of
U avoiding every Z_k, and closed points of U are closed in W because W is a Jacobson space. A
point can also be required to lie in a given nonempty open subset, such as the smooth locus, and
for countably many closed subsets R_α a very general point lies only in those R_α that are all
of W: a rational profile realized at y is realized everywhere, in particular at x.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of K))]

/-- The K-algebra structure on the sections over an open subset. -/
@[instance_reducible]
noncomputable def sectionBaseAlgebra (U : W.Opens) : Algebra K Γ(W, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
    (W ↘ Spec (CommRingCat.of K)).appLE ⊤ U (by simp)).hom.toAlgebra

/-- Sections over an affine open are a finitely generated K-algebra. -/
theorem sectionBaseAlgebra_finiteType [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))]
    {U : W.Opens} (hU : IsAffineOpen U) :
    @Algebra.FiniteType K Γ(W, U) _ _ (sectionBaseAlgebra U) := by
  have h1 : ((W ↘ Spec (CommRingCat.of K)).appLE ⊤ U (by simp)).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable [IsAlgClosed K] [Uncountable K] [IsIntegral W]
  [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))]

include K in
/-- Countably many proper closed subsets of W are avoided by some closed point. -/
theorem exists_closedPoint_notMem_of_countable {ι : Type*} [Countable ι] (Z : ι → Set W)
    (hZ : ∀ k, IsClosed (Z k)) (hZne : ∀ k, Z k ≠ Set.univ) :
    ∃ x : W, IsClosed {x} ∧ ∀ k, x ∉ Z k := by
  obtain ⟨x₀⟩ : Nonempty W := IsIntegral.nonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hx₀U, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hUne : Nonempty U := ⟨⟨x₀, hx₀U⟩⟩
  let _ := sectionBaseAlgebra (K := K) U
  have := sectionBaseAlgebra_finiteType (K := K) hU'
  set Z' : ι → Set (PrimeSpectrum Γ(W, U)) := fun k => hU'.fromSpec ⁻¹' (Z k) with hZ'
  have hZ'cl : ∀ k, IsClosed (Z' k) := fun k => (hZ k).preimage hU'.fromSpec.continuous
  have hdense : Dense (U : Set W) := U.isOpen.dense ⟨x₀, hx₀U⟩
  have hZ'ne : ∀ k, Z' k ≠ Set.univ := by
    intro k h
    apply hZne k
    have hUZ : (U : Set W) ⊆ Z k := by
      rw [← hU'.range_fromSpec]
      rintro _ ⟨q, rfl⟩
      have hq : q ∈ Z' k := h ▸ Set.mem_univ q
      exact hq
    have hcl := closure_minimal hUZ (hZ k)
    rw [hdense.closure_eq] at hcl
    exact Set.eq_univ_of_univ_subset hcl
  set I : ι → Ideal Γ(W, U) := fun k => PrimeSpectrum.vanishingIdeal (Z' k) with hI
  have hI0 : ∀ k, I k ≠ ⊥ := by
    intro k h
    apply hZ'ne k
    rw [← (hZ'cl k).closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    have h' : PrimeSpectrum.vanishingIdeal (Z' k) = ⊥ := h
    rw [h', Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero]
  obtain ⟨Q, hQmax, hQ⟩ := exists_isMaximal_not_le_of_countable (K := K) I hI0
  set q : PrimeSpectrum Γ(W, U) := ⟨Q, hQmax.isPrime⟩
  refine ⟨hU'.fromSpec q, ?_, fun k hk => ?_⟩
  · have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (W ↘ Spec (CommRingCat.of K))
    have hq : q ∈ closedPoints (Spec Γ(W, U)) := by
      exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hQmax
    rw [← hU'.fromSpec.isOpenEmbedding.preimage_closedPoints] at hq
    exact hq
  · apply hQ k
    intro f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf q hk

include K in
/-- A very general closed point in a given nonempty open subset, such as the smooth locus. -/
theorem exists_closedPoint_mem_open_notMem_of_countable {ι : Type*} [Countable ι]
    (O : Set W) (hO : IsOpen O) (hOne : O.Nonempty) (Z : ι → Set W) (hZ : ∀ k, IsClosed (Z k))
    (hZne : ∀ k, Z k ≠ Set.univ) : ∃ x : W, IsClosed {x} ∧ x ∈ O ∧ ∀ k, x ∉ Z k := by
  obtain ⟨x, hx, hxZ⟩ := exists_closedPoint_notMem_of_countable (K := K)
    (fun k : Option ι => k.elim Oᶜ Z) (fun k => by
      cases k with
      | none => exact hO.isClosed_compl
      | some k => exact hZ k)
    (fun k => by
      cases k with
      | none =>
        intro h
        obtain ⟨y, hy⟩ := hOne
        have h' : Oᶜ = Set.univ := h
        have : y ∈ Oᶜ := h' ▸ Set.mem_univ y
        exact this hy
      | some k => exact hZne k)
  refine ⟨x, hx, ?_, fun k => hxZ (some k)⟩
  have h := hxZ none
  simpa using h

include K in
/-- For countably many closed subsets R_α, a very general closed point lies only in those that
are all of W: a profile realized at y is realized at every point. -/
theorem exists_closedPoint_mem_imp_eq_univ {ι : Type*} [Countable ι] (R : ι → Set W)
    (hR : ∀ α, IsClosed (R α)) : ∃ y : W, IsClosed {y} ∧ ∀ α, y ∈ R α → R α = Set.univ := by
  obtain ⟨y, hy, hyR⟩ := exists_closedPoint_notMem_of_countable (K := K)
    (fun α : {α // R α ≠ Set.univ} => R α.1) (fun α => hR α.1) (fun α => α.2)
  refine ⟨y, hy, fun α hα => ?_⟩
  by_contra h
  exact hyR ⟨α, h⟩ hα

end MixedFujita

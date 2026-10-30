/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFiniteAffineNeighborhood
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Mathlib.Order.KrullDimension

/-!
A linear system of parameters from dimension. On an actual integral scheme mapped to
polynomial projective space, with Noetherian underlying space and topological Krull
dimension at most d, over an infinite field, every degree-one form g avoiding the
generic point extends to degree-one forms g, z_1, ..., z_d without common zero. Each
new form avoids the generic points of the finitely many irreducible components of the
current common zero locus, so every chain of irreducible closed sets with top in the
new locus extends by one inside the old locus. After d+1 cuts no chain remains, so the
locus is empty. Only the chain definition of dimension is used.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n K)

/-- The common zero locus on Y of one form. -/
def projectiveFormZeroLocus (ℓ : MvPolynomial (Fin n) K) : Set Y :=
  {z | ℓ ∈ (e z).asHomogeneousIdeal}

theorem projectiveFormZeroLocus_isClosed (ℓ : MvPolynomial (Fin n) K) :
    IsClosed (projectiveFormZeroLocus e ℓ) := by
  have h : projectiveFormZeroLocus e ℓ =
      e.base ⁻¹' ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) ℓ : Set _)ᶜ) := by
    ext z
    simp [projectiveFormZeroLocus, Proj.mem_basicOpen]
  rw [h]
  exact (Proj.basicOpen _ ℓ).isOpen.isClosed_compl.preimage e.base.hom.continuous

/-- Every chain of irreducible closed sets with top in Z has length < r. -/
def ChainsBelow (Z : Set Y) (r : ℕ) : Prop :=
  ∀ l : LTSeries (IrreducibleCloseds Y), (l.last : Set Y) ⊆ Z → l.length < r

theorem chainsBelow_univ {d : ℕ} (hdim : topologicalKrullDim Y ≤ d) :
    ChainsBelow (Set.univ : Set Y) (d + 1) := by
  intro l _
  have h := Order.LTSeries.length_le_krullDim l
  have h' : (l.length : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := h.trans hdim
  have h'' : l.length ≤ d := by exact_mod_cast h'
  omega

theorem eq_empty_of_chainsBelow_zero {Z : Set Y} (hZ : IsClosed Z) (h : ChainsBelow Z 0) :
    Z = ∅ := by
  by_contra hne
  obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne
  let W : IrreducibleCloseds Y := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hW : (W : Set Y) ⊆ Z := closure_minimal (Set.singleton_subset_iff.mpr hz) hZ
  exact Nat.not_lt_zero _ (h (RelSeries.singleton _ W) hW)

/-- One cut by a form avoiding the generic points of finitely many irreducible closed sets
covering Z lowers the chain bound by one. -/
theorem chainsBelow_inter_zeroLocus {Z : Set Y} {r : ℕ} (h : ChainsBelow Z (r + 1))
    (S : Finset (IrreducibleCloseds Y)) (hS : Z ⊆ ⋃ W ∈ S, (W : Set Y))
    (hSZ : ∀ W ∈ S, (W : Set Y) ⊆ Z) (ℓ : MvPolynomial (Fin n) K)
    (hℓ : ∀ W ∈ S, ∃ w ∈ (W : Set Y), ℓ ∉ (e w).asHomogeneousIdeal) :
    ChainsBelow (Z ∩ projectiveFormZeroLocus e ℓ) r := by
  intro l hl
  have hT : (l.last : Set Y) ⊆ ⋃ W ∈ S, (W : Set Y) := (hl.trans Set.inter_subset_left).trans hS
  obtain ⟨W, hWS, hTW⟩ : ∃ W ∈ S, (l.last : Set Y) ⊆ W := by
    have hirr := l.last.isIrreducible
    have hfin := (isIrreducible_iff_sUnion_isClosed.mp hirr) (S.image (fun W : IrreducibleCloseds Y => (W : Set Y)))
      (by
        intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨W, _, rfl⟩ := ht
        exact W.isClosed)
      (by
        intro x hx
        obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (hT hx)
        exact ⟨W, by simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨W, hW, rfl⟩,
          hxW⟩)
    obtain ⟨t, ht, hsub⟩ := hfin
    simp only [Finset.mem_image] at ht
    obtain ⟨W, hW, rfl⟩ := ht
    exact ⟨W, hW, hsub⟩
  obtain ⟨w, hwW, hwℓ⟩ := hℓ W hWS
  have hlt : l.last < W := by
    refine lt_of_le_of_ne hTW ?_
    intro hEq
    have hw : w ∈ (l.last : Set Y) := by rw [hEq]; exact hwW
    exact hwℓ ((hl hw).2)
  have hlen := h (l.snoc W hlt) (by rw [RelSeries.last_snoc]; exact hSZ W hWS)
  rw [RelSeries.snoc_length] at hlen
  omega

variable [NoetherianSpace Y] [QuasiSober Y] [Infinite K]

/-- A nonzero degree-one form avoiding the generic points of the irreducible pieces of a
closed set, which lowers its chain bound by one. -/
theorem exists_linearForm_chainsBelow {Z : Set Y} (hZ : IsClosed Z) {r : ℕ}
    (h : ChainsBelow Z (r + 1)) (p : Y) :
    ∃ ℓ : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      (ℓ : MvPolynomial (Fin n) K) ∉ (e p).asHomogeneousIdeal ∧
        ChainsBelow (Z ∩ projectiveFormZeroLocus e ℓ) r := by
  classical
  obtain ⟨S, hSirr, hSeq⟩ := NoetherianSpace.exists_finset_irreducible (⟨Z, hZ⟩ : Closeds Y)
  have hZS : Z = ⋃ W ∈ S, (W : Set Y) := by
    have h' := congrArg (fun C : Closeds Y => (C : Set Y)) hSeq
    simpa [Closeds.coe_finset_sup] using h'
  let S' : Finset (IrreducibleCloseds Y) :=
    (S.attach).image fun W => ⟨W.1, hSirr W, W.1.isClosed⟩
  let gp : IrreducibleCloseds Y → Y := fun W => W.isIrreducible.genericPoint
  have hgp : ∀ W : IrreducibleCloseds Y, gp W ∈ (W : Set Y) := fun W =>
    (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem
  obtain ⟨ℓ, hℓ⟩ := polynomialProjective_finiteSubset_linearForm_nonvanishing
    (insert (e p) ((fun W => e (gp W)) '' (S' : Set (IrreducibleCloseds Y))))
    ((S'.finite_toSet.image _).insert _)
  refine ⟨ℓ, hℓ _ (Set.mem_insert _ _), ?_⟩
  apply chainsBelow_inter_zeroLocus e h S'
  · intro x hx
    rw [hZS] at hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨⟨W, hSirr ⟨W, hW⟩, W.isClosed⟩, ?_, hxW⟩
    exact Finset.mem_image.mpr ⟨⟨W, hW⟩, Finset.mem_attach _ _, rfl⟩
  · intro W hW
    obtain ⟨W', _, rfl⟩ := Finset.mem_image.mp hW
    intro x hx
    rw [hZS]
    exact Set.mem_iUnion₂.mpr ⟨W'.1, W'.2, hx⟩
  · intro W hW
    exact ⟨gp W, hgp W, hℓ _ (Set.mem_insert_of_mem _ ⟨W, hW, rfl⟩)⟩

/-- Iterated cuts: r forms emptying a closed set with chain bound r. -/
theorem exists_linearForms_empty (p : Y) :
    ∀ (r : ℕ) (Z : Set Y), IsClosed Z → ChainsBelow Z r →
      ∃ z : Fin r → MvPolynomial.homogeneousSubmodule (Fin n) K 1,
        (∀ i, ((z i : MvPolynomial (Fin n) K)) ∉ (e p).asHomogeneousIdeal) ∧
        ∀ x ∈ Z, ∃ i, ((z i : MvPolynomial (Fin n) K)) ∉ (e x).asHomogeneousIdeal
  | 0, Z, hZ, h => by
      refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
      intro x hx
      rw [eq_empty_of_chainsBelow_zero hZ h] at hx
      exact hx.elim
  | r + 1, Z, hZ, h => by
      obtain ⟨ℓ, hℓp, hℓ⟩ := exists_linearForm_chainsBelow e hZ h p
      obtain ⟨z, hzp, hz⟩ := exists_linearForms_empty p r (Z ∩ projectiveFormZeroLocus e ℓ)
        (hZ.inter (projectiveFormZeroLocus_isClosed e ℓ)) hℓ
      refine ⟨Fin.cons ℓ z, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hℓp
        · simpa using hzp i
      · intro x hx
        by_cases hxℓ : (ℓ : MvPolynomial (Fin n) K) ∈ (e x).asHomogeneousIdeal
        · obtain ⟨i, hi⟩ := hz x ⟨hx, hxℓ⟩
          exact ⟨i.succ, by simpa using hi⟩
        · exact ⟨0, by simpa using hxℓ⟩

/-- A linear system of parameters starting with g: no common zero on Y. -/
theorem projective_exists_linearSystem [IsIntegral Y] {d : ℕ} (hdim : topologicalKrullDim Y ≤ d)
    (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    ∃ y : Fin (d + 1) → MvPolynomial (Fin n) K, y 0 = g ∧ (∀ i, (y i).IsHomogeneous 1) ∧
      (∀ i, y i ≠ 0) ∧ ∀ z : Y, ∃ i, y i ∉ (e z).asHomogeneousIdeal := by
  have hbase := chainsBelow_univ (Y := Y) hdim
  let W₀ : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hfirst : ChainsBelow (Set.univ ∩ projectiveFormZeroLocus e g) d := by
    apply chainsBelow_inter_zeroLocus e hbase {W₀}
    · intro x _
      exact Set.mem_iUnion₂.mpr ⟨W₀, Finset.mem_singleton_self _, Set.mem_univ x⟩
    · intro W _
      exact Set.subset_univ _
    · intro W hW
      rw [Finset.mem_singleton] at hW
      subst hW
      exact ⟨genericPoint Y, show genericPoint Y ∈ (Set.univ : Set Y) from Set.mem_univ _, hggen⟩
  obtain ⟨z, hzp, hz⟩ := exists_linearForms_empty e (genericPoint Y) d _
    (isClosed_univ.inter (projectiveFormZeroLocus_isClosed e g)) hfirst
  refine ⟨Fin.cons g (fun i => (z i : MvPolynomial (Fin n) K)), by simp, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hg
    · simp only [Fin.cons_succ]
      exact (z i).2
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]
      rintro rfl
      exact hggen (Ideal.zero_mem _)
    · simp only [Fin.cons_succ]
      intro h0
      exact hzp i (h0 ▸ Ideal.zero_mem _)
  · intro x
    by_cases hxg : g ∈ (e x).asHomogeneousIdeal
    · obtain ⟨i, hi⟩ := hz x ⟨Set.mem_univ _, hxg⟩
      exact ⟨i.succ, by simpa using hi⟩
    · exact ⟨0, by simpa using hxg⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KodairaLemmaPieces
public import TauCeti.Topology.KrullDimension

/-! For d>=2, avoiding finitely many generic points of a closed complement, except the prescribed closed point, forces every integral closed subscheme of dimension d-1 to meet the given nonempty open. Proof uses the actual finite irreducible decomposition and strict dimension bounds. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
theorem exists_finite_avoidance_for_positive_dimensional_hypersurfaces
    {Y : Scheme.{u}} [IsIntegral Y] [NoetherianSpace Y]
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 2 ≤ d)
    (x : Y) (hx : IsClosed {x}) (U : Y.Opens) (hU : Nonempty U) :
    ∃ Z : Set Y, Z.Finite ∧ x ∉ Z ∧
      ∀ (T : Scheme.{u}) (_ : IsIntegral T) (i : T ⟶ Y) (_ : IsClosedImmersion i),
        topologicalKrullDim T = (d - 1 : ℕ) →
        (∀ y ∈ Z, y ∉ Set.range i) → ∃ t : T, i t ∈ U := by
  classical
  obtain ⟨S, hS, hSc, hSi, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let η (C : S) : Y := (hSi C.val C.property).genericPoint
  have hη (C : S) : IsGenericPoint (η C) C.val :=
    (hSi C.val C.property).isGenericPoint_genericPoint (hSc C.val C.property)
  let Z := Set.range η \ {x}
  let : Finite S := hS.to_subtype
  refine ⟨Z, (Set.finite_range η).sdiff, by simp [Z], ?_⟩
  intro T hT i hi hdimT havoid
  let := hT
  let := hi
  by_contra! hno
  have hy : i (genericPoint T) ∈ ((U : Set Y)ᶜ) := hno _
  rw [hcover] at hy
  obtain ⟨C, hCS, hyC⟩ := Set.mem_sUnion.mp hy
  let c : S := ⟨C, hCS⟩
  have hg : IsGenericPoint (i (genericPoint T)) (Set.range i) := by
    have h := (genericPoint_spec T).image i.continuous
    simp only [Set.image_univ] at h
    change IsGenericPoint (i (genericPoint T)) (closure (Set.range i)) at h
    rw [i.isClosedEmbedding.isClosed_range.closure_eq] at h
    exact h
  have hR : Set.range i ⊆ C := by
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyC) (hSc C hCS)
  have hdimR : topologicalKrullDim (Set.range i) = (d - 1 : ℕ) :=
    (i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq).symm.trans hdimT
  have hRC := (IsEmbedding.inclusion hR).isInducing.topologicalKrullDim_le
  have hCcompl : C ⊆ (U : Set Y)ᶜ := by
    rw [hcover]
    exact Set.subset_sUnion_of_mem hCS
  have hCne : C ≠ Set.univ := by
    intro heq
    obtain ⟨y, hyU⟩ := Set.nonempty_coe_sort.mp hU
    exact hCcompl (heq.symm ▸ Set.mem_univ y) hyU
  obtain ⟨r, _, hCr⟩ := exists_nat_topologicalKrullDim_closure_eq hdim (η c)
  rw [(hη c).def] at hCr
  have hCle := topologicalKrullDim_le_pred_of_isClosed_ne_univ hdim (hSc C hCS) hCne
  have hr : r ≤ d - 1 := by
    change topologicalKrullDim C = (r : WithBot ℕ∞) at hCr
    rw [hCr] at hCle
    exact_mod_cast hCle
  by_cases hηx : η c = x
  · have hCeq : C = ({x} : Set Y) := by
      have h := (hη c).def.symm
      simpa only [hηx, hx.closure_eq] using h
    have hzero : topologicalKrullDim C ≤ 0 := by
      rw [hCeq]
      exact topologicalKrullDim_zero_of_discreteTopology _
    have h : ((d - 1 : ℕ) : WithBot ℕ∞) ≤ 0 := by
      rw [← hdimR]
      exact hRC.trans hzero
    have h' : d - 1 ≤ 0 := by exact_mod_cast h
    omega
  · have hηnot : η c ∉ Set.range i := havoid (η c)
      ⟨Set.mem_range_self c, by simpa only [Set.mem_singleton_iff] using hηx⟩
    let D : Set C := (Subtype.val : C → Y) ⁻¹' Set.range i
    have hDc : IsClosed D := i.isClosedEmbedding.isClosed_range.preimage continuous_subtype_val
    have hDne : D ≠ Set.univ := by
      intro heq
      have hmem : (⟨η c, (hη c).mem⟩ : C) ∈ D := heq.symm ▸ Set.mem_univ _
      exact hηnot hmem
    have : IrreducibleSpace C := Subtype.irreducibleSpace (hSi C hCS)
    have hDdim : topologicalKrullDim D = topologicalKrullDim (Set.range i) := by
      have hemb : IsEmbedding (Subtype.val : C → Y) := IsEmbedding.subtypeVal
      have h := hemb.topologicalKrullDim_preimage (Set.range i)
      have hrange : Set.range (Subtype.val : C → Y) = C := by ext y; simp
      change topologicalKrullDim D =
        topologicalKrullDim ↥(Set.range i ∩ Set.range (Subtype.val : C → Y)) at h
      rw [hrange, Set.inter_eq_left.mpr hR] at h
      exact h
    have hDle := topologicalKrullDim_le_pred_of_isClosed_ne_univ hCr hDc hDne
    rw [hDdim, hdimR] at hDle
    have h' : d - 1 ≤ r - 1 := by exact_mod_cast hDle
    omega
end MixedFujita

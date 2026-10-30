/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutPureDimension
public import MixedFujita.PrincipalizedIdealCoefficients

/-! proper全射の実成分像とイデアル逆像切断の全射。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Proper surjections lift each target component to a source component
whose actual set-theoretic image is exactly the chosen target component. -/
theorem proper_surjective_exists_component_image
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (hsurj : Function.Surjective p) (Z : Set Y) (hZ : Z ∈ irreducibleComponents Y) :
    ∃ C ∈ irreducibleComponents X, p '' C = Z := by
  let z := (genericPoints.ofComponent ⟨Z, hZ⟩ : genericPoints Y)
  have hz : IsGenericPoint z.1 Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  obtain ⟨x, hx⟩ := hsurj z.1
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have himg : IsIrreducible (p '' C) := hC.1.image p p.continuous.continuousOn
  have hcl : IsClosed (p '' C) := p.isClosedMap C (isClosed_of_mem_irreducibleComponents C hC)
  have hzimg : z.1 ∈ p '' C := ⟨x, mem_irreducibleComponent, hx⟩
  have hsub : Z ⊆ p '' C := by
    rw [← hz]
    exact closure_minimal (Set.singleton_subset_iff.mpr hzimg) hcl
  exact ⟨C, hC, (hZ.2 himg hsub).antisymm hsub⟩


/-- An actual inverse-image ideal produces a proper surjection of actual
closed subschemes, with the factorization identity retained. -/
theorem proper_surjective_idealCut_map
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (hsurj : Function.Surjective p) (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (hI : I = J.comap p) :
    ∃ q : I.subscheme ⟶ J.subscheme, IsProper q ∧ Function.Surjective q ∧
      q ≫ J.subschemeι = I.subschemeι ≫ p := by
  have hle : J ≤ I.map p := by rw [hI]; exact J.le_map_comap p
  let q := I.subschemeMap J p hle
  have hfac : q ≫ J.subschemeι = I.subschemeι ≫ p :=
    Scheme.IdealSheafData.subschemeMap_subschemeι I J p hle
  let : IsProper (q ≫ J.subschemeι) := by rw [hfac]; infer_instance
  have hq : IsProper q := IsProper.of_comp q J.subschemeι
  refine ⟨q, hq, ?_, hfac⟩
  intro v
  obtain ⟨x, hx⟩ := hsurj (J.subschemeι v)
  have hxI : x ∈ (I.support : Set X) := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change p x ∈ (J.support : Set Y)
    rw [hx, ← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self v
  obtain ⟨w, hw⟩ : x ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hxI
  refine ⟨w, J.subschemeι.isClosedEmbedding.injective ?_⟩
  have h := congrArg (fun f : I.subscheme ⟶ Y => f w) hfac
  change J.subschemeι (q w) = p (I.subschemeι w) at h
  exact h.trans (hw ▸ hx)


/-- Closed sources with identical actual ranges have equal ordinary
dimension, even if their scheme structures differ. -/
theorem closedImmersion_dimension_eq_of_range_eq
    {X Y B : Scheme.{u}} (i : X ⟶ B) (j : Y ⟶ B)
    [IsClosedImmersion i] [IsClosedImmersion j] (hr : Set.range i = Set.range j) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  let e : X ≃ₜ Y := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr hr).trans j.isClosedEmbedding.isEmbedding.toHomeomorph.symm)
  exact e.isHomeomorph.topologicalKrullDim_eq e

end MixedFujita

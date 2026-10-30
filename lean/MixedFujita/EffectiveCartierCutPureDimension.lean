/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutGenerizationDimension

/-! 実Cartier切断の全既約成分の期待次元と整閉構造。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- EVERY irreducible component of the actual nonreduced Cartier cut
has an internally realized integral closed structure of expected ordinary
dimension n. The component witness and its dimension are not supplied. -/
theorem effectiveCartierCut_component_exists_integral_expected_dimension
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (G : CartierDivisor X) (hG : G.IsEffective)
    (Z : Set (effectiveCartierIdealSheaf G hG).subscheme)
    (hZ : Z ∈ irreducibleComponents (effectiveCartierIdealSheaf G hG).subscheme) :
    ∃ (T : Scheme.{u}) (i : T ⟶ (effectiveCartierIdealSheaf G hG).subscheme),
      IsIntegral T ∧ IsClosedImmersion i ∧ Set.range i = Z ∧ topologicalKrullDim T = n := by
  let I := effectiveCartierIdealSheaf G hG
  let Y := I.subscheme
  let j : Y ⟶ X := I.subschemeι
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (j ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (CommRingCat.of K))
  obtain ⟨x, hxc, hxZ, hxgen⟩ := OAI.NumericalDimensionOne.exists_closed_point_in_component_interior Y hZ
  obtain ⟨y, hxy, hyheight⟩ := effectiveCartierCut_closedPoint_exists_large_generization K n hdim G hG x hxc
  have hyZ : y ∈ Z := hxgen y hxy
  obtain ⟨T, i, hi, hT, hrange⟩ := CohomologyAux.exists_integral_closedImmersion Z
    (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
  let := hi
  let := hT
  obtain ⟨t, ht⟩ : y ∈ Set.range i := by rw [hrange]; exact hyZ
  have hlow : (n : WithBot ℕ∞) ≤ topologicalKrullDim T := by
    have htbig : (n : ℕ∞) ≤ Order.height t := by
      rw [OAI.NumericalDimensionOne.height_eq_of_closedImmersion i t, ht]
      exact hyheight
    have hle := Order.height_le_krullDim t
    rw [← OAI.NumericalDimensionOne.scheme_topologicalKrullDim_eq T] at hle
    have htbig' : (n : WithBot ℕ∞) ≤ (Order.height t : WithBot ℕ∞) := by exact_mod_cast htbig
    exact htbig'.trans hle
  have hhigh : topologicalKrullDim T ≤ n :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (effectiveCartierCut_topologicalKrullDim_le G hG n hdim.le)
  exact ⟨T, i, hT, hi, hrange, le_antisymm hhigh hlow⟩


/-- A nonempty actual Cartier cut contains an actual integral closed
subscheme of expected ordinary dimension, with no component supplied. -/
theorem effectiveCartierCut_nonempty_exists_integral_expected_dimension
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (G : CartierDivisor X) (hG : G.IsEffective)
    (hne : Nonempty (effectiveCartierIdealSheaf G hG).subscheme) :
    ∃ (T : Scheme.{u}) (i : T ⟶ (effectiveCartierIdealSheaf G hG).subscheme),
      IsIntegral T ∧ IsClosedImmersion i ∧ topologicalKrullDim T = n := by
  let x := Classical.choice hne
  obtain ⟨T, i, hT, hi, _, hdimT⟩ :=
    effectiveCartierCut_component_exists_integral_expected_dimension K n hdim G hG
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  exact ⟨T, i, hT, hi, hdimT⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineIdealSupportPrime
public import OAI.AlgebraicGeometry.NumericalDimension.CompleteIntersections
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-! 実Cartier切断の閉点から期待次元の生成点を構成。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A closed point on an actual Cartier cut has a generization INSIDE
the same cut of height at least n, when the integral proper source has
ordinary dimension n+1. No reducedness or normality of the cut is assumed. -/
theorem effectiveCartierCut_closedPoint_exists_large_generization
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (G : CartierDivisor X) (hG : G.IsEffective)
    (x : (effectiveCartierIdealSheaf G hG).subscheme) (hx : IsClosed ({x} : Set _)) :
    ∃ y : (effectiveCartierIdealSheaf G hG).subscheme, x ≤ y ∧ (n : ℕ∞) ≤ Order.height y := by
  classical
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let I := effectiveCartierIdealSheaf G hG
  let j := I.subschemeι
  have hxc : IsClosed ({j x} : Set X) := by
    simpa only [Set.image_singleton] using j.isClosedEmbedding.isClosedMap _ hx
  obtain ⟨U, hxU, hUne, a, ha, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective G hG (j x)
  let := hUne
  have hI : I.ideal U = Ideal.span ({a} : Set Γ(X, U.1)) :=
    effectiveCartierIdealSheaf_ideal_eq_span G hG U a ha hEq
  have hxS : j x ∈ I.support := by
    change j x ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self x
  have hax : a ∈ (U.2.primeIdealOf ⟨j x, hxU⟩).asIdeal := by
    have h := (idealSheaf_mem_support_iff_le_affine_prime I U ⟨j x, hxU⟩).mp hxS
    rw [hI] at h
    exact h (Ideal.subset_span (Set.mem_singleton a))
  have hc : Order.coheight (j x) = (n + 1 : ℕ) := by
    have h := (ringKrullDim_stalk_eq_coheight (x := j x)).symm.trans
      ((TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
        (X ↘ Spec (CommRingCat.of K)) hxc).trans hdim)
    exact_mod_cast h
  obtain ⟨q, hxq, hqheight, hqa⟩ := OAI.NumericalDimensionOne.scheme_section_dimension_lower
    U.1 U.2 ⟨j x, hxU⟩ ({a} : Finset Γ(X, U.1))
    (by
      intro b hb
      have hb' : b = a := by simpa using hb
      subst b
      exact hax) n
    (by simp only [Finset.card_singleton, hc]; exact le_rfl)
  have hqS : q.1 ∈ I.support := by
    apply (idealSheaf_mem_support_iff_le_affine_prime I U q).mpr
    rw [hI]
    exact Ideal.span_le.mpr (by simpa only [Finset.coe_singleton] using hqa)
  obtain ⟨y, hy⟩ : q.1 ∈ Set.range j := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hqS
  refine ⟨y, ?_, ?_⟩
  · exact j.isClosedEmbedding.isInducing.specializes_iff.mp (hy ▸ hxq)
  · rw [OAI.NumericalDimensionOne.height_eq_of_closedImmersion j y, hy]
    exact hqheight

end MixedFujita

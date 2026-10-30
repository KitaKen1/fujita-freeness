/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothIntegralNeighborhood
public import MixedFujita.FirstOrderCartierCutSmoothness
public import Hironaka.Scheme.IdealSheaf.Order.Basic
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-! A smooth proper scheme has an actual clopen integral component through every point. The inclusion is both open and closed, so the component remains proper. No characteristic, algebraic-closedness or supplied component assumption is added. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
theorem regularScheme_exists_clopen_integral_component
    {X : Scheme.{u}} [IsNoetherian X] [IsRegular X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsClosed (U : Set X) ∧ IsIntegral U ∧
      IsClosedImmersion U.ι := by
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hX := Hironaka.Sequence.hasDisjointIntegralComponents_of_isRegular (X := X)
  have hclosed : IsClosed ((X.irreducibleComponentOpen C : X.Opens) : Set X) := by
    rw [hX.irreducibleComponentOpen_eq C hC]
    exact isClosed_of_mem_irreducibleComponents C hC
  have hj : IsClosedImmersion (X.irreducibleComponentOpen C).ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact hclosed
  refine ⟨X.irreducibleComponentOpen C, ?_, hclosed,
    Hironaka.Resolution.isIntegral_irreducibleComponentOpen hX C hC, hj⟩
  change x ∈ ((X.irreducibleComponentOpen C : X.Opens) : Set X)
  rw [hX.irreducibleComponentOpen_eq C hC]
  exact mem_irreducibleComponent

theorem smoothProperScheme_exists_integral_component
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [Smooth f] [IsProper f] (x : X) :
    ∃ (T : Scheme.{u}) (j : T ⟶ X), IsOpenImmersion j ∧ IsClosedImmersion j ∧
      IsIntegral T ∧ Smooth (j ≫ f) ∧ IsProper (j ≫ f) ∧ ∃ t : T, j t = x := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := {}
  let : IsRegular X := ⟨fun y => isRegularLocalRing_stalk f y⟩
  obtain ⟨U, hxU, _, hU, hj⟩ := regularScheme_exists_clopen_integral_component x
  let := hj
  exact ⟨U, U.ι, inferInstance, hj, hU, inferInstance, inferInstance, ⟨⟨x, hxU⟩, rfl⟩⟩

theorem subscheme_stalk_dimension_drop_of_regular_equation
    {X : Scheme.{u}} (I : X.IdealSheafData) (z : I.subscheme)
    [IsRegularLocalRing (X.presheaf.stalk (I.subschemeι z))]
    (a : X.presheaf.stalk (I.subschemeι z))
    (hI : I.stalkIdeal (I.subschemeι z) = Ideal.span {a})
    (ha : a ∈ nonZeroDivisors (X.presheaf.stalk (I.subschemeι z))) :
    ringKrullDim (I.subscheme.presheaf.stalk z) + 1 =
      ringKrullDim (X.presheaf.stalk (I.subschemeι z)) := by
  have hz : I.subschemeι z ∈ I.support := by
    change I.subschemeι z ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self z
  have hm := (I.mem_support_iff_stalkIdeal_le_maximalIdeal (I.subschemeι z)).mp hz
  have ham : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι z)) := by
    apply hm
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton a)
  rw [← ringKrullDim_eq_of_ringEquiv (I.stalkQuotientEquiv z), hI]
  exact ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors ha ham
end MixedFujita

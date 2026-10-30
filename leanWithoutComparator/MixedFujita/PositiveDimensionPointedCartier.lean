/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Topology.KrullDimension
public import MixedFujita.ProjectivePointedFixedClassCut

/-!
Positive actual topological Krull dimension supplies nontriviality of the
actual scheme. Pointed Cartier cuts and one point-independent reference
sheaf therefore need no separately supplied Nontrivial instance. The actual
closed projective immersion is still an input. No Bertini existence is claimed.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem topologicalKrullDim_nonpos_of_subsingleton (Y : Type*) [TopologicalSpace Y]
    [Subsingleton Y] : topologicalKrullDim Y ≤ 0 :=
  topologicalKrullDim_zero_of_discreteTopology Y

theorem nontrivial_of_positive_topologicalKrullDim (Y : Type*) [TopologicalSpace Y]
    (h : 0 < topologicalKrullDim Y) : Nontrivial Y := by
  rcases subsingleton_or_nontrivial Y with hs | hn
  · let := hs
    exact False.elim ((not_lt_of_ge (topologicalKrullDim_nonpos_of_subsingleton Y)) h)
  · exact hn

theorem integral_positive_dimension_genericPoint_ne_closedPoint
    {Y : Scheme.{u}} [IsIntegral Y] (hdim : 0 < topologicalKrullDim Y)
    (x : Y) (hx : IsClosed {x}) : genericPoint Y ≠ x := by
  let := nontrivial_of_positive_topologicalKrullDim Y hdim
  exact integral_genericPoint_ne_closedPoint x hx

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

theorem polynomialProjective_positive_dimension_pointed_effectiveCartierCut
    (hdim : 0 < topologicalKrullDim Y)
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : (f : MvPolynomial (Fin n) K) ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  let := nontrivial_of_positive_topologicalKrullDim Y hdim
  exact polynomialProjective_closedImmersion_pointed_effectiveCartierCut e x hx Z hZ hxZ

include e in
theorem polynomialProjective_positive_dimension_exists_fixedClass_pointedCartierSections
    (hdim : 0 < topologicalKrullDim Y) :
    ∃ J : CartierDivisor Y, J.IsEffective ∧
      ∀ (x : Y), IsClosed {x} → ∀ (Z : Set Y), Z.Finite → x ∉ Z →
        ∃ (s : Γ(J.sheaf, ⊤)) (hs : s ≠ 0),
          let I := effectiveCartierIdealSheaf (cartierSectionZeroDivisor J s hs)
            (cartierSectionZeroDivisor_isEffective J s hs)
          Nonempty (InvertibleIdealPresentation I) ∧
            x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  let := nontrivial_of_positive_topologicalKrullDim Y hdim
  exact polynomialProjective_closedImmersion_exists_fixedClass_pointedCartierSections e

end MixedFujita

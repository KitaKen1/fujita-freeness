/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePullbackCartier
public import MixedFujita.ProjectiveClosedPointLinearGeneration

/-!
An actual degree-one effective Cartier cut through a closed point of a
nontrivial integral, projectively embedded scheme over an algebraically
closed field. The form avoids a prescribed finite set and the source's
generic point. The cut's ideal is invertible and its underlying image
contains the prescribed point and avoids the finite set. Smoothness,
integrality of the cut, and fixed-class comparison remain separate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem integral_genericPoint_ne_closedPoint {Y : Scheme.{u}} [IsIntegral Y] [Nontrivial Y]
    (x : Y) (hx : IsClosed {x}) : genericPoint Y ≠ x := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  have hm : y ∈ closure ({genericPoint Y} : Set Y) :=
    specializes_iff_mem_closure.mp (genericPoint_specializes y)
  rw [h, hx.closure_eq] at hm
  exact hy hm

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Nontrivial Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

theorem polynomialProjective_closedImmersion_pointed_genericAvoiding_linearForm
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      (f : MvPolynomial (Fin n) K) ∈ (e x).asHomogeneousIdeal ∧
      (f : MvPolynomial (Fin n) K) ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
      ∀ y ∈ Z, (f : MvPolynomial (Fin n) K) ∉ (e y).asHomogeneousIdeal := by
  have hxZ' : x ∉ insert (genericPoint Y) Z := by
    simp only [Set.mem_insert_iff, not_or]
    exact ⟨(integral_genericPoint_ne_closedPoint x hx).symm, hxZ⟩
  obtain ⟨f, hfx, hfy⟩ :=
    polynomialProjective_closedImmersion_pointed_linearForm_of_isAlgClosed
      e x hx (insert (genericPoint Y) Z) (hZ.insert _) hxZ'
  exact ⟨f, hfx, hfy _ (Set.mem_insert _ _), fun y hy => hfy y (Set.mem_insert_of_mem _ hy)⟩

theorem polynomialProjective_closedImmersion_pointed_effectiveCartierCut
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : (f : MvPolynomial (Fin n) K) ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  obtain ⟨f, hfx, hgeneric, hfy⟩ :=
    polynomialProjective_closedImmersion_pointed_genericAvoiding_linearForm e x hx Z hZ hxZ
  refine ⟨f, hgeneric, ⟨projectivePullbackCartierIdealPresentation e 1 f.val f.property
    Nat.zero_lt_one hgeneric⟩, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.range_subschemeι]
    exact (projectivePullbackCartierIdealSheaf_mem_support_iff e 1 f.val f.property
      Nat.zero_lt_one hgeneric x).mpr hfx
  · intro y hy
    rw [Scheme.IdealSheafData.range_subschemeι]
    intro hs
    exact hfy y hy ((projectivePullbackCartierIdealSheaf_mem_support_iff e 1 f.val f.property
      Nat.zero_lt_one hgeneric y).mp hs)

end MixedFujita

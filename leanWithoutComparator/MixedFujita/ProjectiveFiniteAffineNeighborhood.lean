/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveCharts
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Over an infinite field, one homogeneous linear form avoids any finite set
of actual points of polynomial projective space, including non-rational
points. The forms vanishing at each point form a proper vector subspace.
Finite subspace avoidance and affine D+(f) give a common affine open.
An affine morphism to this projective space, in particular a closed
immersion, transports the common affine neighborhood to its source.
-/

@[expose] public section
open AlgebraicGeometry TopologicalSpace
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] {n : ℕ}

noncomputable def polynomialProjectiveVanishingLinearForms
    (x : polynomialProjectiveScheme n K) :
    Submodule K (MvPolynomial.homogeneousSubmodule (Fin n) K 1) :=
  (x.asHomogeneousIdeal.toIdeal.restrictScalars K).comap
    (MvPolynomial.homogeneousSubmodule (Fin n) K 1).subtype

theorem polynomialProjectiveVanishingLinearForms_mem
    (x : polynomialProjectiveScheme n K)
    (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1) :
    f ∈ polynomialProjectiveVanishingLinearForms x ↔
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal := Iff.rfl

theorem polynomialProjectiveVanishingLinearForms_ne_top
    (x : polynomialProjectiveScheme n K) :
    polynomialProjectiveVanishingLinearForms x ≠ ⊤ := by
  obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart n K x
  intro h
  have hx : (⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩ :
      MvPolynomial.homogeneousSubmodule (Fin n) K 1) ∈
      polynomialProjectiveVanishingLinearForms x := h.symm ▸ Submodule.mem_top
  exact hi ((polynomialProjectiveVanishingLinearForms_mem x _).mp hx)

theorem polynomialProjective_finiteSubset_linearForm_nonvanishing [Infinite K]
    (Z : Set (polynomialProjectiveScheme n K)) (hZ : Z.Finite) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      ∀ x ∈ Z, (f : MvPolynomial (Fin n) K) ∉ x.asHomogeneousIdeal := by
  let : Finite Z := hZ.to_subtype
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun x : Z ↦ polynomialProjectiveVanishingLinearForms x.val)
    (fun x ↦ polynomialProjectiveVanishingLinearForms_ne_top x.val)
  exact ⟨f, fun x hx ↦ (polynomialProjectiveVanishingLinearForms_mem x f).not.mp (hf ⟨x, hx⟩)⟩

theorem polynomialProjective_finiteSubset_affine_neighborhood [Infinite K]
    (Z : Set (polynomialProjectiveScheme n K)) (hZ : Z.Finite) :
    ∃ U : (polynomialProjectiveScheme n K).Opens, IsAffineOpen U ∧ Z ⊆ U := by
  obtain ⟨f, hf⟩ := polynomialProjective_finiteSubset_linearForm_nonvanishing Z hZ
  exact ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) f.val,
    Proj.isAffineOpen_basicOpen _ _ f.property Nat.zero_lt_one, hf⟩

theorem polynomialProjective_affineHom_finiteSubset_affine_neighborhood [Infinite K]
    {Y : Scheme.{u}} (e : Y ⟶ polynomialProjectiveScheme n K) [IsAffineHom e]
    (Z : Set Y) (hZ : Z.Finite) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V := by
  obtain ⟨U, hU, hsub⟩ := polynomialProjective_finiteSubset_affine_neighborhood
    (e '' Z) (hZ.image e)
  exact ⟨e ⁻¹ᵁ U, hU.preimage e, fun y hy ↦ hsub ⟨y, hy, rfl⟩⟩

end MixedFujita

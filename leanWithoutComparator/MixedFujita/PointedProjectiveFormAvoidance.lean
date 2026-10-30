/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFiniteAffineNeighborhood

/-!
A closed point of actual polynomial projective space can be separated
from finitely many other points by one homogeneous form, over an infinite
field. We first separate each point using homogeneous components of the
closed point's prime ideal, raise the degrees with nonvanishing coordinates,
then avoid finitely many proper subspaces in one fixed degree.
The degree here may depend on the finite set. No smoothness, integral
hypersurface, fixed ample class, or pointed Bertini flag is asserted.
-/

@[expose] public section
open AlgebraicGeometry TopologicalSpace
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] {n : ℕ}

noncomputable def polynomialProjectiveVanishingForms (d : ℕ)
    (x : polynomialProjectiveScheme n K) :
    Submodule K (MvPolynomial.homogeneousSubmodule (Fin n) K d) :=
  (x.asHomogeneousIdeal.toIdeal.restrictScalars K).comap
    (MvPolynomial.homogeneousSubmodule (Fin n) K d).subtype

theorem polynomialProjectiveVanishingForms_mem (d : ℕ)
    (x : polynomialProjectiveScheme n K)
    (f : MvPolynomial.homogeneousSubmodule (Fin n) K d) :
    f ∈ polynomialProjectiveVanishingForms d x ↔
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal := Iff.rfl

theorem polynomialProjective_closedPoint_ideal_not_le
    (x : polynomialProjectiveScheme n K) (hx : IsClosed {x})
    (y : polynomialProjectiveScheme n K) (hy : y ≠ x) :
    ¬ x.asHomogeneousIdeal.toIdeal ≤ y.asHomogeneousIdeal.toIdeal := by
  intro h
  have hle := (ProjectiveSpectrum.as_ideal_le_as_ideal
    (MvPolynomial.homogeneousSubmodule (Fin n) K) x y).mp h
  have hmem := (ProjectiveSpectrum.le_iff_mem_closure
    (MvPolynomial.homogeneousSubmodule (Fin n) K) x y).mp hle
  change y ∈ closure ({x} : Set (polynomialProjectiveScheme n K)) at hmem
  rw [hx.closure_eq] at hmem
  exact hy (Set.mem_singleton_iff.mp hmem)

theorem polynomialProjective_closedPoint_homogeneous_separates
    (x : polynomialProjectiveScheme n K) (hx : IsClosed {x})
    (y : polynomialProjectiveScheme n K) (hy : y ≠ x) :
    ∃ d : ℕ, ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K d,
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal ∧
      (f : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal := by
  classical
  obtain ⟨f, hfx, hfy⟩ := IsConcreteLE.not_le_iff_exists.mp
    (polynomialProjective_closedPoint_ideal_not_le x hx y hy)
  have hcomponents := x.asHomogeneousIdeal.isHomogeneous.mem_iff.mp hfx
  have hnot : ∃ d, (DirectSum.decompose
      (MvPolynomial.homogeneousSubmodule (Fin n) K) f d : MvPolynomial (Fin n) K) ∉
      y.asHomogeneousIdeal.toIdeal := by
    by_contra! h
    exact hfy (y.asHomogeneousIdeal.isHomogeneous.mem_iff.mpr h)
  obtain ⟨d, hd⟩ := hnot
  exact ⟨d, DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin n) K) f d,
    hcomponents d, hd⟩

theorem polynomialProjective_separatingForm_raiseDegree
    (x y : polynomialProjectiveScheme n K) {d D : ℕ} (hd : d ≤ D)
    (f : MvPolynomial.homogeneousSubmodule (Fin n) K d)
    (hfx : (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal)
    (hfy : (f : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal) :
    ∃ g : MvPolynomial.homogeneousSubmodule (Fin n) K D,
      (g : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal ∧
      (g : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal := by
  obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart n K y
  let g : MvPolynomial (Fin n) K := f.val * MvPolynomial.X i ^ (D - d)
  have hg : g.IsHomogeneous D := by
    have h := f.property.mul ((MvPolynomial.isHomogeneous_X K i).pow (D - d))
    simpa only [one_mul, Nat.add_sub_of_le hd] using h
  refine ⟨⟨g, hg⟩, x.asHomogeneousIdeal.toIdeal.mul_mem_right _ hfx, ?_⟩
  let : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  exact y.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hfy
    (y.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hi _)

theorem polynomialProjective_fixedDegree_pointed_finite_avoidance [Infinite K]
    (d : ℕ) (x : polynomialProjectiveScheme n K)
    (Z : Set (polynomialProjectiveScheme n K)) (hZ : Z.Finite)
    (hseparate : ∀ y ∈ Z, ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K d,
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal ∧
      (f : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K d,
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal ∧
      ∀ y ∈ Z, (f : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal := by
  let : Finite Z := hZ.to_subtype
  let p := polynomialProjectiveVanishingForms d x
  let q (y : Z) : Submodule K p :=
    (polynomialProjectiveVanishingForms d y.val).comap p.subtype
  have hproper (y : Z) : q y ≠ ⊤ := by
    obtain ⟨f, hfx, hfy⟩ := hseparate y.val y.property
    let f' : p := ⟨f, hfx⟩
    intro h
    have hmem : f' ∈ q y := h.symm ▸ Submodule.mem_top
    exact hfy hmem
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Z) (K := K) (M := p) q hproper
  exact ⟨f.val, f.property, fun y hy ↦ hf ⟨y, hy⟩⟩

theorem polynomialProjective_closedPoint_finiteSubset_homogeneousForm [Infinite K]
    (x : polynomialProjectiveScheme n K) (hx : IsClosed {x})
    (Z : Set (polynomialProjectiveScheme n K)) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K d,
      (f : MvPolynomial (Fin n) K) ∈ x.asHomogeneousIdeal ∧
      ∀ y ∈ Z, (f : MvPolynomial (Fin n) K) ∉ y.asHomogeneousIdeal := by
  classical
  let : Fintype Z := hZ.fintype
  have hsep (y : Z) := polynomialProjective_closedPoint_homogeneous_separates x hx y.val
    (fun h ↦ hxZ (h ▸ y.property))
  choose degree form hform using hsep
  let d := Finset.univ.sup degree + 1
  have hdegree (y : Z) : degree y ≤ d := by
    have h := Finset.le_sup (f := degree) (Finset.mem_univ y)
    exact h.trans (Nat.le_succ _)
  obtain ⟨f, hfx, hfy⟩ := polynomialProjective_fixedDegree_pointed_finite_avoidance d x Z hZ
    (fun y hy ↦ polynomialProjective_separatingForm_raiseDegree x y (hdegree ⟨y, hy⟩)
      (form ⟨y, hy⟩) (hform ⟨y, hy⟩).1 (hform ⟨y, hy⟩).2)
  exact ⟨d, Nat.zero_lt_succ _, f, hfx, hfy⟩

theorem polynomialProjective_closedPoint_finiteSubset_affine_excluding [Infinite K]
    (x : polynomialProjectiveScheme n K) (hx : IsClosed {x})
    (Z : Set (polynomialProjectiveScheme n K)) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ U : (polynomialProjectiveScheme n K).Opens,
      IsAffineOpen U ∧ x ∉ U ∧ Z ⊆ U := by
  obtain ⟨d, hd, f, hfx, hfy⟩ :=
    polynomialProjective_closedPoint_finiteSubset_homogeneousForm x hx Z hZ hxZ
  exact ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) f.val,
    Proj.isAffineOpen_basicOpen _ _ f.property hd, fun h ↦ h hfx, hfy⟩

theorem polynomialProjective_closedImmersion_finiteSubset_affine_excluding [Infinite K]
    {Y : Scheme.{u}} (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∉ U ∧ Z ⊆ U := by
  have hex : IsClosed {e x} := by
    simpa only [Set.image_singleton] using e.isClosedEmbedding.isClosedMap {x} hx
  have hexZ : e x ∉ e '' Z := by
    rintro ⟨y, hy, he⟩
    exact hxZ (e.isClosedEmbedding.injective he ▸ hy)
  obtain ⟨U, hU, hxU, hZU⟩ :=
    polynomialProjective_closedPoint_finiteSubset_affine_excluding
      (e x) hex (e '' Z) (hZ.image e) hexZ
  exact ⟨e ⁻¹ᵁ U, hU.preimage e, hxU, fun y hy ↦ hZU ⟨y, hy, rfl⟩⟩

end MixedFujita

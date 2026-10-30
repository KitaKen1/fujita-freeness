/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedRationalPoints
public import MixedFujita.ProjectiveAffineCharts
public import MixedFujita.ProjectivePointLinearIdeal

/-!
The actual coordinate-chart prime of a closed projective point is maximal.
The existing polynomial chart isomorphism and closed-point residue-field
calculation provide normalized coordinates over an algebraically closed field.
Membership of a homogeneous polynomial is tested by actual chart evaluation.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] {n : ℕ}

noncomputable def polynomialProjectiveChartPrime (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)) :
    PrimeSpectrum (MvPolynomial {j : Fin n // j ≠ k} K) :=
  PrimeSpectrum.comap (projectiveChartRingEquiv K k).symm.toRingHom
    (ProjIsoSpecTopComponent.toSpec (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (MvPolynomial.X k) ⟨x, hxi⟩)

theorem polynomialProjectiveChartPrime_isMaximal (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) : (polynomialProjectiveChartPrime k x hxi).asIdeal.IsMaximal := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
  let z : U := ⟨x, hxi⟩
  have hpre : (Subtype.val : U → polynomialProjectiveScheme n K) ⁻¹' {x} = {z} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change y.val = z.val ↔ y = z
    exact Subtype.val_inj
  have hz : IsClosed {z} := by
    rw [← hpre]
    exact hx.preimage continuous_subtype_val
  let e := projIsoSpecTopComponent (𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) K)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one
  let p : PrimeSpectrum (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)) :=
    ProjIsoSpecTopComponent.toSpec
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k) z
  have hp : IsClosed {p} := by
    have hp' := (TopCat.homeoOfIso e).isClosedMap {z} hz
    change IsClosed ((ProjIsoSpecTopComponent.toSpec
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)) '' {z}) at hp'
    simpa only [Set.image_singleton] using hp'
  let := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hp
  exact Ideal.comap_isMaximal_of_surjective _ (projectiveChartRingEquiv K k).symm.surjective

theorem polynomialProjectiveChartPrime_dehomogenize_mem (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    {d : ℕ} (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    projectiveDehomogenize K k f ∈ (polynomialProjectiveChartPrime k x hxi).asIdeal ↔
      f ∈ x.asHomogeneousIdeal := by
  change projectiveChartAffineToLocalization K k (projectiveDehomogenize K k f) ∈
    ProjIsoSpecTopComponent.ToSpec.carrier ⟨x, hxi⟩ ↔ f ∈ x.asHomogeneousIdeal
  rw [projectiveChartAffineToLocalization_dehomogenize K k d f hf]
  exact ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _

variable [IsAlgClosed K]

noncomputable def polynomialProjectiveClosedChartEvaluation (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) : MvPolynomial {j : Fin n // j ≠ k} K →ₐ[K] K := by
  let := polynomialProjectiveChartPrime_isMaximal k x hxi hx
  exact closedPointEvaluation (polynomialProjectiveChartPrime k x hxi).asIdeal

theorem polynomialProjectiveClosedChartEvaluation_eq_zero_iff (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) (g : MvPolynomial {j : Fin n // j ≠ k} K) :
    polynomialProjectiveClosedChartEvaluation k x hxi hx g = 0 ↔
      g ∈ (polynomialProjectiveChartPrime k x hxi).asIdeal := by
  let := polynomialProjectiveChartPrime_isMaximal k x hxi hx
  exact closedPointEvaluation_eq_zero_iff (polynomialProjectiveChartPrime k x hxi).asIdeal g

noncomputable def polynomialProjectiveClosedPointCoordinates (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) (j : Fin n) : K :=
  polynomialProjectiveClosedChartEvaluation k x hxi hx (projectiveChartVariable K k j)

theorem polynomialProjectiveClosedPointCoordinates_self (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) : polynomialProjectiveClosedPointCoordinates k x hxi hx k = 1 := by
  simp [polynomialProjectiveClosedPointCoordinates, projectiveChartVariable]

theorem polynomialProjectiveClosedChartEvaluation_dehomogenize (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) (f : MvPolynomial (Fin n) K) :
    polynomialProjectiveClosedChartEvaluation k x hxi hx (projectiveDehomogenize K k f) =
      MvPolynomial.eval (polynomialProjectiveClosedPointCoordinates k x hxi hx) f := by
  have h : (polynomialProjectiveClosedChartEvaluation k x hxi hx).toRingHom.comp
      (projectiveDehomogenize K k) =
      MvPolynomial.eval (polynomialProjectiveClosedPointCoordinates k x hxi hx) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, projectiveDehomogenize_C, MvPolynomial.eval_C]
      exact (polynomialProjectiveClosedChartEvaluation k x hxi hx).commutes r
    · intro j
      simp [projectiveDehomogenize, polynomialProjectiveClosedPointCoordinates]
  exact RingHom.congr_fun h f

theorem polynomialProjectiveClosedPointCoordinates_homogeneous_mem_iff (k : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) {d : ℕ} (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    MvPolynomial.eval (polynomialProjectiveClosedPointCoordinates k x hxi hx) f = 0 ↔
      f ∈ x.asHomogeneousIdeal := by
  rw [← polynomialProjectiveClosedChartEvaluation_dehomogenize k x hxi hx f,
    polynomialProjectiveClosedChartEvaluation_eq_zero_iff]
  exact polynomialProjectiveChartPrime_dehomogenize_mem k x hxi f hf

theorem polynomialProjectiveClosedPointCoordinates_linearRelation_mem (k j : Fin n)
    (x : polynomialProjectiveScheme n K)
    (hxi : x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k))
    (hx : IsClosed {x}) :
    MvPolynomial.X j - MvPolynomial.C (polynomialProjectiveClosedPointCoordinates k x hxi hx j) *
      MvPolynomial.X k ∈ x.asHomogeneousIdeal := by
  apply (polynomialProjectiveClosedPointCoordinates_homogeneous_mem_iff k x hxi hx _
    (normalizedProjectiveLinearRelation_homogeneous _ k j)).mp
  simp [polynomialProjectiveClosedPointCoordinates_self]

end MixedFujita

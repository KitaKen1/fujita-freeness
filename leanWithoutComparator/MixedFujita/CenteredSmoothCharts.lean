/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialOriginCoordinates
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-!
Translate polynomial variables by their values at a rational point. A standard
smooth algebra thereby has an etale polynomial chart whose rational point is
the polynomial origin. The variable count is the standard smooth relative
dimension; identifying it with a geometric dimension is a separate step.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {σ K : Type*} [CommRing K]

noncomputable def polynomialTranslation (c : σ → K) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i)))
    (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i)))
    (by ext i; simp) (by ext i; simp)

@[simp]
theorem polynomialTranslation_variable (c : σ → K) (i : σ) :
    polynomialTranslation c (MvPolynomial.X i) = MvPolynomial.X i - MvPolynomial.C (c i) :=
  MvPolynomial.aeval_X _ i

@[simp]
theorem polynomialTranslation_symm_variable (c : σ → K) (i : σ) :
    (polynomialTranslation c).symm (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (c i) :=
  MvPolynomial.aeval_X _ i

variable {A : Type*} [CommRing A] [Algebra K A]

noncomputable def centeredPolynomialChart (g : MvPolynomial σ K →ₐ[K] A)
    (α : A →ₐ[K] K) : MvPolynomial σ K →ₐ[K] A :=
  g.comp (polynomialTranslation (fun i => α (g (MvPolynomial.X i)))).toAlgHom

@[simp]
theorem centeredPolynomialChart_variable
    (g : MvPolynomial σ K →ₐ[K] A) (α : A →ₐ[K] K) (i : σ) :
    centeredPolynomialChart g α (MvPolynomial.X i) =
      g (MvPolynomial.X i) - algebraMap K A (α (g (MvPolynomial.X i))) := by
  simp [centeredPolynomialChart]

theorem centeredPolynomialChart_point
    (g : MvPolynomial σ K →ₐ[K] A) (α : A →ₐ[K] K) :
    α.comp (centeredPolynomialChart g α) = MvPolynomial.aeval (fun _ => 0) := by
  ext i
  simp

theorem centeredPolynomialChart_constantCoeff
    (g : MvPolynomial σ K →ₐ[K] A) (α : A →ₐ[K] K) (p : MvPolynomial σ K) :
    α (centeredPolynomialChart g α p) = MvPolynomial.constantCoeff p := by
  have h := congrArg (fun f : MvPolynomial σ K →ₐ[K] K => f p)
    (centeredPolynomialChart_point g α)
  simpa only [AlgHom.comp_apply, MvPolynomial.aeval_zero', Algebra.algebraMap_self,
    RingHom.id_apply] using h

theorem centeredPolynomialChart_etale
    (g : MvPolynomial σ K →ₐ[K] A) (α : A →ₐ[K] K) (hg : g.Etale) :
    (centeredPolynomialChart g α).Etale := by
  change g.toRingHom.Etale at hg
  change (g.toRingHom.comp
    (polynomialTranslation (fun i => α (g (MvPolynomial.X i)))).toRingHom).Etale
  have ht : (polynomialTranslation (fun i => α (g (MvPolynomial.X i)))).toRingHom.Etale :=
    RingHom.Etale.of_bijective (polynomialTranslation _).bijective
  rw [RingHom.etale_iff_formallyUnramified_and_smooth] at ht hg ⊢
  exact ⟨RingHom.FormallyUnramified.comp ht.1 hg.1, RingHom.Smooth.comp ht.2 hg.2⟩

theorem standardSmooth_exists_centeredEtaleChart [Algebra.IsStandardSmooth K A]
    (α : A →ₐ[K] K) :
    ∃ n : ℕ, ∃ g : MvPolynomial (Fin n) K →ₐ[K] A,
      g.Etale ∧ ∀ p, α (g p) = MvPolynomial.constantCoeff p := by
  obtain ⟨n, g, hgK, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    ((RingHom.isStandardSmooth_algebraMap).mpr inferInstance :
      (algebraMap K A).IsStandardSmooth)
  let g' : MvPolynomial (Fin n) K →ₐ[K] A :=
    { g with commutes' := fun k => congrArg (fun f : K →+* A => f k) hgK }
  exact ⟨n, centeredPolynomialChart g' α, centeredPolynomialChart_etale g' α hg,
    centeredPolynomialChart_constantCoeff g' α⟩

theorem standardSmoothRelativeDimension_exists_centeredEtaleChart (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K A] (α : A →ₐ[K] K) :
    ∃ g : MvPolynomial (Fin n) K →ₐ[K] A,
      g.Etale ∧ ∀ p, α (g p) = MvPolynomial.constantCoeff p := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  exact ⟨centeredPolynomialChart g α, centeredPolynomialChart_etale g α hg,
    centeredPolynomialChart_constantCoeff g α⟩

end MixedFujita

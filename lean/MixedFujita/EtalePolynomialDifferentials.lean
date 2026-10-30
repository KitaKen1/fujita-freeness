/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCoordinateDifferentials
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Admissible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Actual Kähler bases induced by an étale map to polynomial affine space.
The coefficient algebra structure is the one induced by the actual coordinate
map. Both affine sections and their actual stalk germs are handled. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem ringHom_formallyEtale_of_etale {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) : f.FormallyEtale := by
  let _ := f.toAlgebra
  have : Algebra.Etale R S := hf
  exact Algebra.Etale.formallyEtale

theorem sectionsHom_formallyEtale_of_etale {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (.of R)) [Etale σ] (V : Y.affineOpens) :
    (sectionsHom σ V.1).FormallyEtale := by
  have hΓ : (Scheme.ΓSpecIso (.of R)).inv.hom.Etale :=
    RingHom.Etale.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)
  exact RingHom.FormallyEtale.comp
    (ringHom_formallyEtale_of_etale _ hΓ)
    (ringHom_formallyEtale_of_etale _ (σ.etale_appLE (isAffineOpen_top _) V.2 le_top))

theorem affineOpen_germ_formallyEtale {Y : Scheme.{u}} (V : Y.affineOpens)
    (p : Y) (hp : p ∈ V.1) : (Y.presheaf.germ V.1 p hp).hom.FormallyEtale := by
  let _ := Y.presheaf.algebra_section_stalk (⟨p, hp⟩ : V.1)
  have := V.2.isLocalization_stalk (⟨p, hp⟩ : V.1)
  exact Algebra.FormallyEtale.of_isLocalization (V.2.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl

noncomputable def polynomialRingHomAsAlgHom {K A : Type*} [Field K] [CommRing A]
    {n : ℕ} (τ : MvPolynomial (Fin n) K →+* A) :
    letI : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
    MvPolynomial (Fin n) K →ₐ[K] A := by
  letI : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
  exact { τ with commutes' := fun _ => rfl }

noncomputable def polynomialRingHomDifferentialBasis {K A : Type*} [Field K] [CommRing A]
    {n : ℕ} (τ : MvPolynomial (Fin n) K →+* A) (hτ : τ.FormallyEtale) :
    letI : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
    Module.Basis (Fin n) A Ω[A⁄K] := by
  letI : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
  exact etaleCoordinateBasis (polynomialRingHomAsAlgHom τ) hτ

theorem polynomialRingHomDifferentialBasis_apply {K A : Type*} [Field K] [CommRing A]
    {n : ℕ} (τ : MvPolynomial (Fin n) K →+* A) (hτ : τ.FormallyEtale) (i : Fin n) :
    letI : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
    polynomialRingHomDifferentialBasis τ hτ i = KaehlerDifferential.D K A (τ (MvPolynomial.X i)) := by
  let : Algebra K A := (τ.comp MvPolynomial.C).toAlgebra
  exact etaleCoordinateBasis_apply (polynomialRingHomAsAlgHom τ) hτ i

theorem etalePolynomial_stalkMap_formallyEtale {K : Type u} [Field K] {n : ℕ}
    {Y : Scheme.{u}} (σ : Y ⟶ Spec (.of (MvPolynomial (Fin n) K))) [Etale σ]
    (V : Y.affineOpens) (p : Y) (hp : p ∈ V.1) :
    ((Y.presheaf.germ V.1 p hp).hom.comp (sectionsHom σ V.1)).FormallyEtale :=
  RingHom.FormallyEtale.comp (sectionsHom_formallyEtale_of_etale σ V)
    (affineOpen_germ_formallyEtale V p hp)

end MixedFujita

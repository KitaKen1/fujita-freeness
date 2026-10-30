/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothRestrictionCodimZero

/-!
Étale coordinates through the ideal of a smooth closed subvariety, for rings (step 9, restriction
theorem).

For a surjection π : A → A' of smooth K-domains of relative dimensions N + d + 1 and N and a
K-point χ of A', there are t ∈ ker π, an element b with χ(π b) ≠ 0 and N + d further functions u
such that (t, u) are étale coordinates on A_b (`exists_away_etale_coordinates_through_kernel`): on
the global sections of Spec A, the conormal lemma gives t (the dimensions of the differentials at
the points are N + d + 1 and N, check-318), the coordinates extend (check-319) and are étale on a
basic open (check-318); everything is transported to A along Γ(Spec A, ⊤) ≅ A
(`specTopAlgEquiv`) and the induced isomorphism of localizations. This is the chart of the
induction step on the codimension in the restriction theorem: the hypersurface t = 0 is étale over
affine space of dimension N + d (check-320).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
open KaehlerDifferential

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section RingCoordinates

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  specAlgebraOver

/-- The global sections of Spec A, as a K-algebra isomorphic to A. -/
noncomputable def specTopAlgEquiv (A : Type u) [CommRing A] [Algebra K A] :
    A ≃ₐ[K] Γ(Spec (CommRingCat.of A), ⊤) :=
  AlgEquiv.ofRingEquiv (f := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv)
    (fun k => (specAlgebraOver_algebraMap A k).symm)

theorem specTopAlgEquiv_apply (A : Type u) [CommRing A] [Algebra K A] (a : A) :
    specTopAlgEquiv (K := K) A a = (Scheme.ΓSpecIso (CommRingCat.of A)).inv a :=
  rfl

/-- The K-point of Γ(Spec A, ⊤) corresponding to a K-point of A vanishes exactly on the prime of
the point. -/
theorem specTopAlgEquiv_point_iff {A : Type u} [CommRing A] [Algebra K A] (χ : A →ₐ[K] K)
    (r : Γ(Spec (CommRingCat.of A), ⊤)) :
    (χ.comp (specTopAlgEquiv (K := K) A).symm.toAlgHom) r = 0 ↔
      r ∈ ((isAffineOpen_top (Spec (CommRingCat.of A))).primeIdealOf
        ⟨specAlgHomPoint χ, trivial⟩).asIdeal := by
  have h := mem_primeIdealOf_specAlgHomPoint_iff χ ((specTopAlgEquiv (K := K) A).symm r)
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((specTopAlgEquiv (K := K) A).symm r) = r :=
    (specTopAlgEquiv (K := K) A).apply_symm_apply r
  rw [h1] at h
  exact h.symm

/-- For a surjection A → A' of smooth K-domains of relative dimensions N + d + 1 and N and a K-point
of A', some t ∈ ker π and N + d further functions are étale coordinates on a basic open A_b
around the point. -/
theorem exists_away_etale_coordinates_through_kernel {A A' : Type u} [CommRing A] [IsDomain A]
    [Algebra K A] [CommRing A'] [IsDomain A'] [Algebra K A'] {N d : ℕ}
    [SmoothOfRelativeDimension (N + d + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension N (Spec (CommRingCat.of A') ↘ Spec (CommRingCat.of K))]
    (π : A →ₐ[K] A') (hπ : Function.Surjective π) (χ : A' →ₐ[K] K) :
    ∃ (t b : A) (u : Fin (N + d) → A), π t = 0 ∧ (χ.comp π) b ≠ 0 ∧
      (MvPolynomial.aeval (R := K) (fun l => algebraMap A (Localization.Away b)
        ((Fin.cons t u : Fin (N + d + 1) → A) l))).toRingHom.FormallyEtale := by
  classical
  let e := specTopAlgEquiv (K := K) A
  let e' := specTopAlgEquiv (K := K) A'
  let πR : Γ(Spec (CommRingCat.of A), ⊤) →ₐ[K] Γ(Spec (CommRingCat.of A'), ⊤) :=
    (e'.toAlgHom.comp π).comp e.symm.toAlgHom
  have hπR : Function.Surjective πR := e'.surjective.comp (hπ.comp e.symm.surjective)
  let χR' : Γ(Spec (CommRingCat.of A'), ⊤) →ₐ[K] K := χ.comp e'.symm.toAlgHom
  let χR : Γ(Spec (CommRingCat.of A), ⊤) →ₐ[K] K := (χ.comp π).comp e.symm.toAlgHom
  have hχR : ∀ r, χR r = χR' (πR r) := by
    intro r
    change χ (π (e.symm r)) = χ (e'.symm (e' (π (e.symm r))))
    rw [AlgEquiv.symm_apply_apply]
  -- the dimensions of the differentials at the two points
  have hptA := specTopAlgEquiv_point_iff (K := K) (χ.comp π)
  have hptA' := specTopAlgEquiv_point_iff (K := K) χ
  obtain ⟨-, hrank⟩ := finrank_tmul_kaehler_eq (N := N + d + 1)
    (isAffineOpen_top (Spec (CommRingCat.of A))) (specAlgHomPoint (χ.comp π)) trivial χR hptA
  obtain ⟨hfd', hrank'⟩ := finrank_tmul_kaehler_eq (N := N)
    (isAffineOpen_top (Spec (CommRingCat.of A'))) (specAlgHomPoint χ) trivial χR' hptA'
  -- the conormal lemma on the global sections
  obtain ⟨t, ht, htD⟩ : ∃ t : Γ(Spec (CommRingCat.of A), ⊤), πR t = 0 ∧
      DifferentialsIndependentAt K χR ![t] := by
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
      πR.toRingHom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of A'), ⊤) K := χR'.toRingHom.toAlgebra
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) K := χR.toRingHom.toAlgebra
    haveI : IsScalarTower K Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) :=
      IsScalarTower.of_algebraMap_eq fun k => (πR.commutes k).symm
    haveI : IsScalarTower Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of A'), ⊤) K :=
      IsScalarTower.of_algebraMap_eq fun r => hχR r
    haveI := hfd'
    obtain ⟨t, ht, ht0⟩ := exists_mem_ker_tmul_D_ne_zero K K
      (A := Γ(Spec (CommRingCat.of A), ⊤)) (B := Γ(Spec (CommRingCat.of A'), ⊤)) hπR
      (by rw [hrank, hrank']; omega)
    refine ⟨t, ht, ?_⟩
    dsimp only [DifferentialsIndependentAt]
    rw [linearIndependent_unique_iff]
    exact ht0
  -- coordinates through t, étale on a basic open
  obtain ⟨u, hu⟩ := exists_differentialsIndependentAt_cons (N := N + d)
    (isAffineOpen_top (Spec (CommRingCat.of A))) (specAlgHomPoint (χ.comp π)) trivial χR hptA t htD
  obtain ⟨b, hb, hφ⟩ := exists_away_formallyEtale_of_differentialsIndependentAt (N := N + d + 1)
    (specAlgHomPoint (χ.comp π)) χR hptA _ hu
  -- transport to A
  refine ⟨e.symm t, e.symm b, fun l => e.symm (u l), ?_, ?_, ?_⟩
  · have h1 : π (e.symm t) = e'.symm (πR t) := by
      change π (e.symm t) = e'.symm (e' (π (e.symm t)))
      rw [AlgEquiv.symm_apply_apply]
    rw [h1, ht, map_zero]
  · exact hb
  · let Φr : Localization.Away b ≃+* Localization.Away (e.symm b) :=
      IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers b)
        (T := Submonoid.powers (e.symm b)) (Localization.Away b) (Localization.Away (e.symm b))
        e.symm.toRingEquiv (by rw [Submonoid.map_powers]; rfl)
    have hΦr : ∀ r, Φr (algebraMap _ (Localization.Away b) r) =
        algebraMap A (Localization.Away (e.symm b)) (e.symm r) :=
      fun r => IsLocalization.ringEquivOfRingEquiv_eq _ r
    let Φ : Localization.Away b ≃ₐ[K] Localization.Away (e.symm b) :=
      AlgEquiv.ofRingEquiv (f := Φr) (fun k => by
        rw [IsScalarTower.algebraMap_apply K Γ(Spec (CommRingCat.of A), ⊤) (Localization.Away b),
          hΦr, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply])
    have heq : MvPolynomial.aeval (R := K) (fun l => algebraMap A (Localization.Away (e.symm b))
        ((Fin.cons (e.symm t) (fun l => e.symm (u l)) : Fin (N + d + 1) → A) l)) =
        Φ.toAlgHom.comp (MvPolynomial.aeval (R := K) (fun l => algebraMap _ (Localization.Away b)
          ((Fin.cons t u : Fin (N + d + 1) → Γ(Spec (CommRingCat.of A), ⊤)) l))) := by
      apply MvPolynomial.algHom_ext
      intro l
      rw [MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.aeval_X]
      change _ = Φr (algebraMap _ (Localization.Away b) _)
      rw [hΦr]
      congr 1
      cases l using Fin.cases with
      | zero => rfl
      | succ l => rfl
    rw [heq]
    exact formallyEtale_comp _ (ringHom_formallyEtale_of_etale _
      (RingHom.Etale.of_bijective Φ.bijective)) _ hφ

end RingCoordinates

end MixedFujita

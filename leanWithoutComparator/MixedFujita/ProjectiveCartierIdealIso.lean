/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierRestriction
public import MixedFujita.ProjectiveEffectiveCartier

/-!
The actual O(-D) -> O_X inclusion has the existing hypersurface ideal as
its image on every affine open. This gives a linear equivalence of sections
with that ideal, preserving multiplicities.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} (R : Type u) [CommRing R] [IsDomain R]

theorem projectiveHomogeneousCartier_inclusion_range
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (W : (polynomialProjectiveScheme n R).affineOpens) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    Set.range (Scheme.Modules.Hom.app
      (negativeCartierToUnit (polynomialProjectiveScheme n R)
        (projectiveHomogeneousCartier R k₀ d f hf h0)
        (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0)) W.1) =
      ((projectiveHypersurfaceIdealSheaf f d hf).ideal W :
        Set Γ(polynomialProjectiveScheme n R, W.1)) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  ext a
  rw [negativeCartierToUnit_range_iff,
    projectiveHomogeneousCartier_negativeSection_mem_hypersurface_ideal_iff]
  rfl

noncomputable def projectiveHomogeneousCartier_idealLinearEquiv
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (W : (polynomialProjectiveScheme n R).affineOpens) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    Γ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf, W.1)
      ≃ₗ[Γ(polynomialProjectiveScheme n R, W.1)]
        (projectiveHypersurfaceIdealSheaf f d hf).ideal W := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  let D := projectiveHomogeneousCartier R k₀ d f hf h0
  have hD : D.IsEffective := projectiveHomogeneousCartier_isEffective R k₀ d f hf h0
  have hr := projectiveHomogeneousCartier_inclusion_range R k₀ d f hf h0 W
  let ψ : Γ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf, W.1)
      →ₗ[Γ(polynomialProjectiveScheme n R, W.1)]
        (projectiveHypersurfaceIdealSheaf f d hf).ideal W :=
    { toFun s := ⟨negativeCartierRegularSection (polynomialProjectiveScheme n R) D hD W.1 s,
        (Set.ext_iff.mp hr _).mp ⟨s, rfl⟩⟩
      map_add' s t := Subtype.ext
        (negativeCartierRegularSection_add (polynomialProjectiveScheme n R) D hD W.1 s t)
      map_smul' r s := Subtype.ext
        (negativeCartierRegularSection_smul (polynomialProjectiveScheme n R) D hD W.1 r s) }
  exact LinearEquiv.ofBijective ψ ⟨
    fun s t h => negativeCartierToUnit_app_injective
      (polynomialProjectiveScheme n R) D hD W.1 (congrArg Subtype.val h),
    fun a => by
      obtain ⟨s, hs⟩ := (Set.ext_iff.mp hr _).mpr a.2
      exact ⟨s, Subtype.ext hs⟩⟩

theorem projectiveHomogeneousCartier_idealLinearEquiv_apply_coe
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (W : (polynomialProjectiveScheme n R).affineOpens) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    ∀ s : Γ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf, W.1),
      (projectiveHomogeneousCartier_idealLinearEquiv R k₀ d f hf h0 W s :
        Γ(polynomialProjectiveScheme n R, W.1)) =
      Scheme.Modules.Hom.app (negativeCartierToUnit (polynomialProjectiveScheme n R)
        (projectiveHomogeneousCartier R k₀ d f hf h0)
        (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0)) W.1 s := by
  intro s
  rfl

theorem projectiveHomogeneousCartier_idealLinearEquiv_map
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    (U V : (polynomialProjectiveScheme n R).affineOpens) (h : V.1 ≤ U.1) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    ∀ s : Γ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf, U.1),
      (projectiveHomogeneousCartier_idealLinearEquiv R k₀ d f hf h0 V
        ((-(projectiveHomogeneousCartier R k₀ d f hf h0)).sheaf.presheaf.map
          (homOfLE h).op s) : Γ(polynomialProjectiveScheme n R, V.1)) =
      (polynomialProjectiveScheme n R).presheaf.map (homOfLE h).op
        (projectiveHomogeneousCartier_idealLinearEquiv R k₀ d f hf h0 U s :
          Γ(polynomialProjectiveScheme n R, U.1)) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  intro s
  rw [projectiveHomogeneousCartier_idealLinearEquiv_apply_coe,
    projectiveHomogeneousCartier_idealLinearEquiv_apply_coe]
  exact negativeCartierRegularSection_map (polynomialProjectiveScheme n R)
    (projectiveHomogeneousCartier R k₀ d f hf h0)
    (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0) (homOfLE h) s

theorem projectiveHomogeneousCartier_openInclusion_range
    (k₀ : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) (h0 : f ≠ 0)
    {Y : Scheme.{u}} (j : Y ⟶ polynomialProjectiveScheme n R) [IsOpenImmersion j]
    (U : Y.affineOpens) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    Set.range (Scheme.Modules.Hom.app
      (negativeCartierToOpenUnit (polynomialProjectiveScheme n R)
        (projectiveHomogeneousCartier R k₀ d f hf h0)
        (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0) j) U.1) =
      (((projectiveHypersurfaceIdealSheaf f d hf).comap j).ideal U : Set Γ(Y, U.1)) := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  ext a
  rw [negativeCartierToOpenUnit_range_iff,
    projectiveHomogeneousCartier_negativeSection_mem_hypersurface_ideal_iff
      R k₀ d f hf h0 ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rfl

end MixedFujita

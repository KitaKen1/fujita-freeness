/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionsAtlas
public import MixedFujita.VeryAmpleNumericalBound

/-!
A criterion for very ampleness from actual sections (steps 1 and 4). Let t_q, q < M, be global
sections of a Cartier divisor D on an integral scheme X proper over a field, and let a subfamily
of nonzero sections t_β have generating opens V_β which cover X, are affine, and whose rings of
functions are generated over the base field by the ratios t_q/t_β. Then the morphism to the
projective space with M coordinates defined by the sections is a closed immersion over the base
field, the chart equation of the coordinate X_q on V_β pulls back to the ratio t_q/t_β, and the
hyperplane divisor of a coordinate X_β is D + div(τ_β), where τ_β is the rational function of t_β.
So D is very ample in the projective sense. The closed immersion is checked on the charts V_β by
the criterion of the pinned openai/math; the pull-back of chart functions is computed through the
chart isomorphism of Proj.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open OAI.PiExponentSeshadri.Projective

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section ChartPullback

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Z : Scheme.{u}} (s : A) {m : ℕ} (hs : s ∈ 𝒜 m) (hm : 0 < m)

/-- A morphism through the affine chart of s lands in the basic open of s. -/
theorem proj_awayι_comp_top_le
    (h : Z ⟶ Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 s))) :
    (⊤ : Z.Opens) ≤ (h ≫ Proj.awayι 𝒜 s hs hm) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
  intro p _
  have hp : (Proj.awayι 𝒜 s hs hm) (h p) ∈ (Proj.awayι 𝒜 s hs hm).opensRange := ⟨h p, rfl⟩
  rw [Proj.opensRange_awayι] at hp
  exact hp

/-- The section map of an open subscheme onto its global sections is the inverse of the
identification of global sections. -/
theorem opens_topIso_inv_eq_appLE {X : Scheme.{u}} (U : X.Opens) :
    U.topIso.inv = U.ι.appLE U ⊤ U.ι_preimage_self.ge :=
  (show U.topIso.inv = X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op from rfl).trans
    (U.ι_appLE U ⊤ U.ι_preimage_self.ge).symm

/-- A morphism defined through the affine chart of s by a ring homomorphism from the degree-zero
localization pulls the chart functions back by that homomorphism. -/
theorem proj_awayι_appLE_awayToSection
    (ev : HomogeneousLocalization.Away 𝒜 s →+* Γ(Z, ⊤))
    (z : HomogeneousLocalization.Away 𝒜 s)
    (e : (⊤ : Z.Opens) ≤
      (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ Proj.awayι 𝒜 s hs hm) ⁻¹ᵁ
        Proj.basicOpen 𝒜 s) :
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ Proj.awayι 𝒜 s hs hm).appLE
      (Proj.basicOpen 𝒜 s) ⊤ e (Proj.awayToSection 𝒜 s z) = ev z := by
  have hφ : Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ Proj.awayι 𝒜 s hs hm =
      (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hm).inv) ≫
        (Proj.basicOpen 𝒜 s).ι := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Category.assoc, Category.assoc]
  have h1 := Scheme.Hom.appLE_comp_appLE
    (Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hm).inv)
    (Proj.basicOpen 𝒜 s).ι (Proj.basicOpen 𝒜 s) ⊤ ⊤ (Proj.basicOpen 𝒜 s).ι_preimage_self.ge
    (fun _ _ => trivial)
  rw [schemeHom_appLE_top_top] at h1
  have e' : (⊤ : Z.Opens) ≤
      ((Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hm).inv) ≫
        (Proj.basicOpen 𝒜 s).ι) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
    rw [← hφ]
    exact e
  have h2 := schemeHom_appLE_congr_hom hφ (Proj.basicOpen 𝒜 s) ⊤ e e'
  have h3 := ConcreteCategory.congr_hom (h2.trans h1.symm) (Proj.awayToSection 𝒜 s z)
  rw [CommRingCat.comp_apply] at h3
  rw [h3, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply]
  have h4 : (Proj.basicOpen 𝒜 s).ι.appLE (Proj.basicOpen 𝒜 s) ⊤
        (Proj.basicOpen 𝒜 s).ι_preimage_self.ge (Proj.awayToSection 𝒜 s z) =
      (Proj.basicOpenIsoSpec 𝒜 s hs hm).hom.appTop ((Scheme.ΓSpecIso _).inv z) := by
    have h := ConcreteCategory.congr_hom (Proj.basicOpenToSpec_app_top 𝒜 s)
      ((Scheme.ΓSpecIso _).inv z)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h
    rw [← opens_topIso_inv_eq_appLE]
    exact h.symm
  have h5 : (Proj.basicOpenIsoSpec 𝒜 s hs hm).inv.appTop
        ((Proj.basicOpenIsoSpec 𝒜 s hs hm).hom.appTop ((Scheme.ΓSpecIso _).inv z)) =
      (Scheme.ΓSpecIso _).inv z := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  have h6 := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ev)) z
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h6
  rw [h4, h5]
  have h7 : Z.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv (ev z)) = ev z := by
    rw [Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_apply (C := CommRingCat) _ _
  exact (congrArg (fun y => Z.toSpecΓ.appTop y) h6.symm).trans h7

end ChartPullback

section ChartFunctions

variable {K : Type u} [CommRing K] {M : ℕ} {X : Scheme.{u}} [IsIntegral X]

/-- If a morphism to projective space is given on an open V through the affine chart of X_j by a
ring homomorphism, then the pull-back of a chart function has the rational function of its image
under that homomorphism. -/
theorem germToFunctionField_app_awayToSection_of_chart
    (ψ : X ⟶ polynomialProjectiveScheme M K) (V : X.Opens) [Nonempty V] (j : Fin M)
    [Nonempty (projectivePullbackCoordinateOpen ψ j)]
    (ev : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X j) →+* Γ(V.toScheme, ⊤))
    (hloc : V.ι ≫ ψ = V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X K j) Nat.zero_lt_one)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X j)) (r : Γ(X, V)) (hz : ev z = opensSectionToTop V r) :
    X.germToFunctionField (projectivePullbackCoordinateOpen ψ j)
        (ψ.app _ (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
          (MvPolynomial.X j) z)) =
      X.germToFunctionField V r := by
  have hne' : Nonempty (ψ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X j) : X.Opens) :=
    inferInstanceAs (Nonempty (projectivePullbackCoordinateOpen ψ j))
  have hle' : (⊤ : V.toScheme.Opens) ≤
      (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X K j) Nat.zero_lt_one) ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j) :=
    proj_awayι_comp_top_le _ _ _ _ (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev))
  have hle : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ ψ) ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j) := by
    rw [hloc]
    exact hle'
  have h1 := proj_awayι_appLE_awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
    (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) Nat.zero_lt_one ev z hle'
  have h2 := schemeHom_appLE_congr_hom hloc
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)) ⊤ hle hle'
  have h3 := Scheme.Hom.comp_appLE V.ι ψ
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)) ⊤ hle
  have h4 := ConcreteCategory.congr_hom (h3.symm.trans h2)
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j) z)
  rw [CommRingCat.comp_apply] at h4
  have hVU : V ≤ ψ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X j) := fun x hx =>
    hle (show (⟨x, hx⟩ : V.toScheme) ∈ (⊤ : V.toScheme.Opens) from trivial)
  have h₁ : V.ι ''ᵁ ⊤ ≤ ψ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X j) := by
    rw [Scheme.Opens.ι_image_top]
    exact hVU
  have h₂ : V.ι ''ᵁ ⊤ ≤ V := (Scheme.Opens.ι_image_top V).le
  have : Nonempty (V.ι ''ᵁ ⊤ : X.Opens) := by
    rw [Scheme.Opens.ι_image_top]
    infer_instance
  have hA : V.ι.appLE (ψ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K)
        (MvPolynomial.X j)) ⊤ hle
        (ψ.app _ (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
          (MvPolynomial.X j) z)) =
      X.presheaf.map (homOfLE h₁).op
        (ψ.app _ (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
          (MvPolynomial.X j) z)) := by
    exact congrArg (fun f : Γ(X, ψ ⁻¹ᵁ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)) ⟶ Γ(V.toScheme, ⊤) =>
      f.hom (ψ.app _ (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
        (MvPolynomial.X j) z))) (V.ι_appLE (ψ ⁻¹ᵁ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X j)) ⊤ hle)
  have hB : opensSectionToTop V r = X.presheaf.map (homOfLE h₂).op r :=
    congrArg (fun f : Γ(X, V) ⟶ Γ(V.toScheme, ⊤) => f.hom r)
      (V.ι_appLE V ⊤ V.ι_preimage_self.ge)
  have h5 : X.presheaf.map (homOfLE h₁).op
        (ψ.app _ (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin M) K)
          (MvPolynomial.X j) z)) = X.presheaf.map (homOfLE h₂).op r :=
    hA.symm.trans ((h4.trans (h1.trans hz)).trans hB)
  exact (germToFunctionField_restrict X h₁ _).symm.trans
    ((congrArg (X.germToFunctionField (V.ι ''ᵁ ⊤)) h5).trans (germToFunctionField_restrict X h₂ r))

end ChartFunctions

section Scalars

variable {K : Type u} [CommRing K] {M : ℕ} {X : Scheme.{u}}

theorem opensSectionToTop_bijective (V : X.Opens) : Function.Bijective (opensSectionToTop V) :=
  ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ V.ι_preimage_self.ge)

theorem opensSectionToTop_comp_restrict_top (V : X.Opens) :
    (opensSectionToTop V).comp (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom =
      V.ι.appTop.hom := by
  have h := Scheme.Hom.map_appLE V.ι V.ι_preimage_self.ge (homOfLE (le_top : V ≤ ⊤)).op
  rw [schemeHom_appLE_top_top] at h
  exact congrArg CommRingCat.Hom.hom h

/-- Generation of the functions on an open by coordinates, read on the open subscheme. -/
theorem eval₂Hom_opensSectionToTop_surjective (V : X.Opens) (k : K →+* Γ(X, ⊤))
    (a : Fin M → Γ(X, V))
    (h : Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp k) a)) :
    Function.Surjective (MvPolynomial.eval₂Hom (V.ι.appTop.hom.comp k)
      (fun q => opensSectionToTop V (a q))) := by
  have hcomp : (opensSectionToTop V).comp (MvPolynomial.eval₂Hom
        ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp k) a) =
      MvPolynomial.eval₂Hom (V.ι.appTop.hom.comp k) (fun q => opensSectionToTop V (a q)) := by
    rw [coordinates_eval_natural, ← RingHom.comp_assoc, opensSectionToTop_comp_restrict_top]
  rw [← hcomp]
  exact (opensSectionToTop_bijective V).surjective.comp h

end Scalars

section Embedding

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X)
  {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
  (hne : ∀ β, t (idx β) ≠ 0)
  (hcover : (⨆ β, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- The coordinate open of X_q pulls back to a nonempty open when t_q is nonzero. -/
theorem cartierSectionsMap_coordinateOpen_nonempty (q : Fin M) (hq : t q ≠ 0) :
    Nonempty (projectivePullbackCoordinateOpen (cartierSectionsMap K D t idx hne hcover) q) := by
  unfold projectivePullbackCoordinateOpen
  rw [cartierSectionsMap_preimage]
  exact (cartierSectionNonvanishingOpen_nonempty_iff D (t q)).mpr hq

/-- The chart equation of the coordinate X_q on the chart of X_β pulls back to the ratio
t_q/t_β. -/
theorem cartierSectionsMap_equation_germToFunctionField (β : ι) (q : Fin M)
    [Nonempty (projectivePullbackCoordinateOpen (cartierSectionsMap K D t idx hne hcover) (idx β))] :
    X.germToFunctionField
        (projectivePullbackCoordinateOpen (cartierSectionsMap K D t idx hne hcover) (idx β))
        (projectivePullbackHomogeneousEquation (cartierSectionsMap K D t idx hne hcover) (idx β) 1
          (MvPolynomial.X q) (MvPolynomial.isHomogeneous_X K q)) =
      (cartierSectionRational D (t (idx β)))⁻¹ * cartierSectionRational D (t q) := by
  have hV := (cartierSectionNonvanishingOpen_nonempty_iff D (t (idx β))).mpr (hne β)
  have hu : IsUnit ((MvPolynomial.eval₂Hom
      ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp (schemeBaseScalars K X))
      (fun q => opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q))))
      (MvPolynomial.X (idx β))) := by
    simpa only [MvPolynomial.eval₂Hom_X', opensSectionToTop_cartierSectionRatio_self] using
      (isUnit_one : IsUnit (1 : Γ((cartierSectionNonvanishingOpen D (t (idx β))).toScheme, ⊤)))
  have hmem : MvPolynomial.X q ∈ MvPolynomial.homogeneousSubmodule (Fin M) K (1 • 1) := by
    simpa using MvPolynomial.isHomogeneous_X K q
  have H := evalAway_mk_clear
    (MvPolynomial.eval₂Hom
      ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp (schemeBaseScalars K X))
      (fun q => opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q))))
    (coordinates_X_mem (K := K) (idx β)) hu 1 (MvPolynomial.X q) hmem
  refine (germToFunctionField_app_awayToSection_of_chart
    (cartierSectionsMap K D t idx hne hcover) (cartierSectionNonvanishingOpen D (t (idx β)))
    (idx β) _ (cartierSectionsMap_ι D t idx hne hcover β) _
    (cartierSectionRatio D (t (idx β)) (hne β) (t q)) ?_).trans
    (cartierSectionRatio_germToFunctionField D (t (idx β)) (hne β) (t q))
  simpa only [MvPolynomial.eval₂Hom_X', opensSectionToTop_cartierSectionRatio_self, one_pow,
    mul_one] using H

/-- The hyperplane divisor of a coordinate is the divisor of zeros of the corresponding section:
D is the hyperplane divisor of X_β minus the principal divisor of τ_β. -/
theorem cartierSectionsMap_hyperplane (β₀ : ι)
    (hggen : MvPolynomial.X (idx β₀) ∉
      ((cartierSectionsMap K D t idx hne hcover) (genericPoint X)).asHomogeneousIdeal) :
    D = projectiveHyperplaneCartier (cartierSectionsMap K D t idx hne hcover)
        (MvPolynomial.X (idx β₀)) (MvPolynomial.isHomogeneous_X K (idx β₀)) hggen +
      principalCartierDivisor X (cartierSectionUnit D (t (idx β₀)) (hne β₀))⁻¹ := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  have hx : x ∈ ⨆ β, cartierSectionNonvanishingOpen D (t (idx β)) := by
    rw [hcover]
    trivial
  obtain ⟨β, hβ⟩ := Opens.mem_iSup.mp hx
  have hne' := cartierSectionsMap_coordinateOpen_nonempty (K := K) D t idx hne hcover (idx β)
    (hne β)
  have hxβ : x ∈ projectivePullbackCoordinateOpen (cartierSectionsMap K D t idx hne hcover)
      (idx β) := by
    unfold projectivePullbackCoordinateOpen
    rw [cartierSectionsMap_preimage]
    exact hβ
  refine ⟨(cartierSectionUnit D (t (idx β)) (hne β))⁻¹,
    isLocalEquationAt_inv_cartierSectionUnit D (t (idx β)) (hne β) x hβ, ?_⟩
  have h1 := (projectiveHyperplane_isLocalEquationAt (cartierSectionsMap K D t idx hne hcover)
    (MvPolynomial.X (idx β₀)) (MvPolynomial.isHomogeneous_X K (idx β₀)) hggen
    ⟨idx β, hne'⟩ x hxβ).mul
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor x
      (cartierSectionUnit D (t (idx β₀)) (hne β₀))⁻¹)
  have hu : projectiveHyperplaneUnit (cartierSectionsMap K D t idx hne hcover)
        (MvPolynomial.X (idx β₀)) (MvPolynomial.isHomogeneous_X K (idx β₀)) hggen ⟨idx β, hne'⟩ *
      (cartierSectionUnit D (t (idx β₀)) (hne β₀))⁻¹ =
      (cartierSectionUnit D (t (idx β)) (hne β))⁻¹ := by
    apply Units.ext
    have hval : ((projectiveHyperplaneUnit (cartierSectionsMap K D t idx hne hcover)
        (MvPolynomial.X (idx β₀)) (MvPolynomial.isHomogeneous_X K (idx β₀)) hggen
        ⟨idx β, hne'⟩ : X.functionFieldˣ) : X.functionField) =
        (cartierSectionRational D (t (idx β)))⁻¹ * cartierSectionRational D (t (idx β₀)) :=
      cartierSectionsMap_equation_germToFunctionField D t idx hne hcover β (idx β₀)
    have h0 : cartierSectionRational D (t (idx β₀)) ≠ 0 := fun h =>
      hne β₀ (cartierSectionRational_injective D (h.trans (map_zero _).symm))
    rw [Units.val_mul, hval, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      cartierSectionUnit_val, cartierSectionUnit_val, mul_assoc, mul_inv_cancel₀ h0, mul_one]
  rw [hu] at h1
  exact h1

/-- The morphism defined by sections is proper when the scheme is proper over the base field. -/
theorem cartierSectionsMap_isProper [IsProper (X ↘ Spec (CommRingCat.of K))] :
    IsProper (cartierSectionsMap K D t idx hne hcover) := by
  have h : IsProper (cartierSectionsMap K D t idx hne hcover ≫
      projectiveBase (K := K) (σ := Fin M)) := by
    rw [← polynomialProjectiveToBase_eq_projectiveBase, cartierSectionsMap_over]
    infer_instance
  exact IsProper.of_comp _ (projectiveBase (K := K) (σ := Fin M))

/-- The morphism defined by sections is a closed immersion when the generating opens of the
chosen sections are affine with functions generated by the ratios. -/
theorem cartierSectionsMap_isClosedImmersion [IsProper (X ↘ Spec (CommRingCat.of K))]
    (haff : ∀ β, IsAffineOpen (cartierSectionNonvanishingOpen D (t (idx β))))
    (hgen : ∀ β, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top :
        cartierSectionNonvanishingOpen D (t (idx β)) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (fun q => cartierSectionRatio D (t (idx β)) (hne β) (t q)))) :
    IsClosedImmersion (cartierSectionsMap K D t idx hne hcover) := by
  have := cartierSectionsMap_isProper (K := K) D t idx hne hcover
  let g (β : ι) := (cartierSectionNonvanishingOpen D (t (idx β))).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (evalAway (𝒜 := MvPolynomial.homogeneousSubmodule (Fin M) K)
        (MvPolynomial.eval₂Hom
          ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp
            (schemeBaseScalars K X))
          (fun q => opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q))))
        (MvPolynomial.X (idx β))
        (by simpa only [MvPolynomial.eval₂Hom_X', opensSectionToTop_cartierSectionRatio_self]
          using (isUnit_one :
            IsUnit (1 : Γ((cartierSectionNonvanishingOpen D (t (idx β))).toScheme, ⊤))))))
  let ep (β : ι) := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin M) K)
    (MvPolynomial.X (idx β)) (MvPolynomial.isHomogeneous_X K (idx β)) (by decide : 0 < (1 : ℕ))
  apply OAI.PiExponentSeshadri.Geometry.closedImmersion_of_source_charts
    (cartierSectionsMap K D t idx hne hcover)
    (fun β => cartierSectionNonvanishingOpen D (t (idx β)))
    (fun β => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K)
      (MvPolynomial.X (idx β))) hcover (fun β => g β ≫ (ep β).inv)
  · intro β
    have : IsAffine (cartierSectionNonvanishingOpen D (t (idx β))).toScheme := haff β
    have : IsClosedImmersion (g β) := normalized_coordinates_closed
      ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp (schemeBaseScalars K X))
      (fun q => opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q)))
      (idx β) (opensSectionToTop_cartierSectionRatio_self D (t (idx β)) (hne β))
      (eval₂Hom_opensSectionToTop_surjective _ _ _ (hgen β))
    infer_instance
  · intro β
    rw [cartierSectionsMap_ι]
    rfl
  · intro β
    exact cartierSectionsMap_preimage D t idx hne hcover (idx β)

include hcover in
/-- Very ampleness from sections: nonzero sections whose generating opens cover, are affine, and
have functions generated by the ratios of the given sections. -/
theorem cartierIsVeryAmpleProj_of_sections [IsProper (X ↘ Spec (CommRingCat.of K))]
    (haff : ∀ β, IsAffineOpen (cartierSectionNonvanishingOpen D (t (idx β))))
    (hgen : ∀ β, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top :
        cartierSectionNonvanishingOpen D (t (idx β)) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (fun q => cartierSectionRatio D (t (idx β)) (hne β) (t q)))) :
    CartierIsVeryAmpleProj K D := by
  have hx : genericPoint X ∈ ⨆ β, cartierSectionNonvanishingOpen D (t (idx β)) := by
    rw [hcover]
    trivial
  obtain ⟨β₀, -⟩ := Opens.mem_iSup.mp hx
  have hgenpt : genericPoint X ∈ cartierSectionsMap K D t idx hne hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X (idx β₀)) := by
    rw [cartierSectionsMap_preimage]
    exact (cartierSectionNonvanishingOpen_genericPoint_iff D (t (idx β₀))).mpr (hne β₀)
  have hggen : MvPolynomial.X (idx β₀) ∉
      ((cartierSectionsMap K D t idx hne hcover) (genericPoint X)).asHomogeneousIdeal := hgenpt
  exact ⟨M, cartierSectionsMap K D t idx hne hcover,
    cartierSectionsMap_isClosedImmersion D t idx hne hcover haff hgen,
    cartierSectionsMap_over D t idx hne hcover, MvPolynomial.X (idx β₀),
    MvPolynomial.isHomogeneous_X K (idx β₀), hggen, _,
    cartierSectionsMap_hyperplane D t idx hne hcover β₀ hggen⟩

end Embedding

end MixedFujita

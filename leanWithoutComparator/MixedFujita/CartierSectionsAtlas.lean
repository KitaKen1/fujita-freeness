/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionRatios
public import MixedFujita.PolynomialProjectiveScheme
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveEmbeddingCharts

/-!
The morphism to projective space defined by finitely many actual sections of a Cartier divisor
(steps 1 and 4). Let t_q, q < M, be global sections of a Cartier divisor D on an integral scheme
over a field, and let a subfamily of nonzero sections have generating opens covering the scheme.
On the generating open V_β of t_β the ratios t_q/t_β are regular functions, equal to 1 for q = β,
and on overlaps the two families of ratios differ by the unit t_β/t_γ. These are the data of a
coordinate atlas, which glues to a morphism to the projective space with M homogeneous
coordinates. The preimage of the coordinate open of X_q is the generating open of t_q, and the
morphism commutes with the structure morphisms to the base field. The gluing of the local maps is
the coordinate atlas of the pinned openai/math; the compatibility on overlaps is the cocycle
identity for ratios of sections, transported to the fibre products of the open subschemes. The
index type of the chosen sections lies in the universe of the scheme, as that atlas requires.
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

section OpenSubschemes

variable {X Y : Scheme.{u}}

/-- The section map over the whole source is the map on global sections. -/
theorem schemeHom_appLE_top_top (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop :=
  Scheme.Hom.appLE_eq_app f (U := ⊤)

/-- Equal morphisms have equal section maps. -/
theorem schemeHom_appLE_congr_hom {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- A point of an open subscheme lies in the open. -/
theorem opens_ι_apply_mem (V : X.Opens) (y : V.toScheme) : V.ι y ∈ V := by
  have h : y ∈ V.ι ⁻¹ᵁ V := by
    rw [V.ι_preimage_self]
    trivial
  exact h

variable (V W : X.Opens)

/-- Sections on an open, as global sections of the open subscheme. -/
noncomputable def opensSectionToTop : Γ(X, V) →+* Γ(V.toScheme, ⊤) :=
  (V.ι.appLE V ⊤ V.ι_preimage_self.ge).hom

/-- The fibre product of two open subschemes maps into their intersection. -/
theorem pullbackOpens_top_le :
    (⊤ : (pullback V.ι W.ι).Opens) ≤ (pullback.fst V.ι W.ι ≫ V.ι) ⁻¹ᵁ (V ⊓ W) := by
  intro p _
  have h : (pullback.fst V.ι W.ι ≫ V.ι) p = (pullback.snd V.ι W.ι ≫ W.ι) p :=
    congrArg (fun f : pullback V.ι W.ι ⟶ X => f p) (pullback.condition (f := V.ι) (g := W.ι))
  have h1 : (pullback.fst V.ι W.ι ≫ V.ι) p ∈ V := opens_ι_apply_mem V (pullback.fst V.ι W.ι p)
  have h2 : (pullback.snd V.ι W.ι ≫ W.ι) p ∈ W := opens_ι_apply_mem W (pullback.snd V.ι W.ι p)
  rw [← h] at h2
  exact ⟨h1, h2⟩

/-- Sections on the intersection of two opens, as global sections of the fibre product of the
two open subschemes. -/
noncomputable def opensInterSectionToPullback : Γ(X, V ⊓ W) →+* Γ(pullback V.ι W.ι, ⊤) :=
  ((pullback.fst V.ι W.ι ≫ V.ι).appLE (V ⊓ W) ⊤ (pullbackOpens_top_le V W)).hom

theorem pullback_fst_appTop_opensSectionToTop (r : Γ(X, V)) :
    (pullback.fst V.ι W.ι).appTop (opensSectionToTop V r) =
      opensInterSectionToPullback V W
        (X.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op r) := by
  have h1 := Scheme.Hom.appLE_comp_appLE (pullback.fst V.ι W.ι) V.ι V ⊤ ⊤ V.ι_preimage_self.ge
    (fun _ _ => trivial)
  rw [schemeHom_appLE_top_top] at h1
  have h2 := Scheme.Hom.map_appLE (pullback.fst V.ι W.ι ≫ V.ι) (pullbackOpens_top_le V W)
    (homOfLE (inf_le_left : V ⊓ W ≤ V)).op
  have h3 := ConcreteCategory.congr_hom (h1.trans h2.symm) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h3
  exact h3

theorem pullback_snd_appTop_opensSectionToTop (r : Γ(X, W)) :
    (pullback.snd V.ι W.ι).appTop (opensSectionToTop W r) =
      opensInterSectionToPullback V W
        (X.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op r) := by
  have h1 := Scheme.Hom.appLE_comp_appLE (pullback.snd V.ι W.ι) W.ι W ⊤ ⊤ W.ι_preimage_self.ge
    (fun _ _ => trivial)
  rw [schemeHom_appLE_top_top] at h1
  have h2 := Scheme.Hom.map_appLE (pullback.fst V.ι W.ι ≫ V.ι) (pullbackOpens_top_le V W)
    (homOfLE (inf_le_right : V ⊓ W ≤ W)).op
  have e1 : (⊤ : (pullback V.ι W.ι).Opens) ≤ (pullback.fst V.ι W.ι ≫ V.ι) ⁻¹ᵁ W := by
    intro p hp
    obtain ⟨-, h⟩ := pullbackOpens_top_le V W hp
    exact h
  have e2 : (⊤ : (pullback V.ι W.ι).Opens) ≤ (pullback.snd V.ι W.ι ≫ W.ι) ⁻¹ᵁ W := by
    intro p _
    exact opens_ι_apply_mem W (pullback.snd V.ι W.ι p)
  have h4 := schemeHom_appLE_congr_hom (pullback.condition (f := V.ι) (g := W.ι)) W ⊤ e1 e2
  have h3 := ConcreteCategory.congr_hom (h1.trans (h4.symm.trans h2.symm)) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h3
  exact h3

/-- Constants pulled back to the fibre product of two open subschemes through either factor
agree. -/
theorem pullbackOpens_scalars_comp {K : Type u} [CommRing K] (k : K →+* Γ(X, ⊤)) :
    (pullback.fst V.ι W.ι).appTop.hom.comp (V.ι.appTop.hom.comp k) =
      (pullback.snd V.ι W.ι).appTop.hom.comp (W.ι.appTop.hom.comp k) := by
  rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    congrArg (fun f : pullback V.ι W.ι ⟶ X => f.appTop.hom)
      (pullback.condition (f := V.ι) (g := W.ι))

end OpenSubschemes

section Atlas

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X)

/-- On the fibre product of two generating opens, the ratios with denominators t_j and t_i
differ by the unit t_i/t_j. -/
theorem cartierSectionRatio_pullback_overlap (ti tj : Γ(D.sheaf, ⊤)) (hi : ti ≠ 0)
    (hj : tj ≠ 0) :
    ∃ c : Γ(pullback (cartierSectionNonvanishingOpen D ti).ι
        (cartierSectionNonvanishingOpen D tj).ι, ⊤)ˣ,
      ∀ tq : Γ(D.sheaf, ⊤),
        (pullback.snd (cartierSectionNonvanishingOpen D ti).ι
            (cartierSectionNonvanishingOpen D tj).ι).appTop
          (opensSectionToTop _ (cartierSectionRatio D tj hj tq)) =
        (c : Γ(pullback (cartierSectionNonvanishingOpen D ti).ι
            (cartierSectionNonvanishingOpen D tj).ι, ⊤)) *
          (pullback.fst (cartierSectionNonvanishingOpen D ti).ι
              (cartierSectionNonvanishingOpen D tj).ι).appTop
            (opensSectionToTop _ (cartierSectionRatio D ti hi tq)) := by
  have hone : opensInterSectionToPullback (cartierSectionNonvanishingOpen D ti)
        (cartierSectionNonvanishingOpen D tj)
        (X.presheaf.map (homOfLE (inf_le_right :
          cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
            cartierSectionNonvanishingOpen D tj)).op (cartierSectionRatio D tj hj ti)) *
      opensInterSectionToPullback (cartierSectionNonvanishingOpen D ti)
        (cartierSectionNonvanishingOpen D tj)
        (X.presheaf.map (homOfLE (inf_le_left :
          cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
            cartierSectionNonvanishingOpen D ti)).op (cartierSectionRatio D ti hi tj)) = 1 := by
    rw [← map_mul, ← cartierSectionRatio_cocycle D ti tj tj hi hj, cartierSectionRatio_self,
      map_one, map_one]
  refine ⟨Units.mkOfMulEqOne _ _ hone, fun tq => ?_⟩
  rw [pullback_snd_appTop_opensSectionToTop, pullback_fst_appTop_opensSectionToTop,
    Units.val_mkOfMulEqOne, ← map_mul, ← cartierSectionRatio_cocycle D ti tj tq hi hj]

/-- The coordinate of a section with itself as denominator is 1. -/
theorem opensSectionToTop_cartierSectionRatio_self (t₀ : Γ(D.sheaf, ⊤)) (h : t₀ ≠ 0) :
    opensSectionToTop _ (cartierSectionRatio D t₀ h t₀) = 1 := by
  rw [cartierSectionRatio_self, map_one]

variable (K) in
/-- The base field as global constants of a scheme over it. -/
noncomputable def schemeBaseScalars (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] :
    K →+* Γ(X, ⊤) :=
  (X ↘ Spec (CommRingCat.of K)).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

variable {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
  (hne : ∀ β, t (idx β) ≠ 0)
  (hcover : (⨆ β, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤)

variable (K) in
/-- The coordinate atlas of a family of sections: on the generating open of a chosen nonzero
section the coordinates are the ratios with that section as denominator. -/
noncomputable def cartierSectionsAtlas :=
  ({ cover := X.openCoverOfIsOpenCover
        (fun β : ι => cartierSectionNonvanishingOpen D (t (idx β))) (IsOpenCover.mk hcover)
     scalars := fun β : ι => (cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp
        (schemeBaseScalars K X)
     coordinates := fun (β : ι) (q : Fin M) =>
        opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q))
     index := idx
     normalized := fun β : ι =>
        opensSectionToTop_cartierSectionRatio_self D (t (idx β)) (hne β)
     scalarOverlap := fun β γ : ι =>
        pullbackOpens_scalars_comp (cartierSectionNonvanishingOpen D (t (idx β)))
          (cartierSectionNonvanishingOpen D (t (idx γ))) (schemeBaseScalars K X)
     coordinateOverlap := fun β γ : ι => by
        obtain ⟨c, hc⟩ := cartierSectionRatio_pullback_overlap D (t (idx β)) (t (idx γ))
          (hne β) (hne γ)
        exact ⟨c, fun q => hc (t q)⟩ } :
    CoordinateAtlas (K := K) (σ := Fin M) X)

variable (K) in
/-- The morphism to projective space defined by a family of sections. -/
noncomputable def cartierSectionsMap : X ⟶ polynomialProjectiveScheme M K :=
  (cartierSectionsAtlas K D t idx hne hcover).morphism

/-- On the generating open of a chosen section the morphism is given by the ratios. -/
theorem cartierSectionsMap_ι (β : ι) :
    (cartierSectionNonvanishingOpen D (t (idx β))).ι ≫ cartierSectionsMap K D t idx hne hcover =
      coordinatesMap (cartierSectionNonvanishingOpen D (t (idx β))).toScheme
        ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appTop.hom.comp (schemeBaseScalars K X))
        (fun q => opensSectionToTop _ (cartierSectionRatio D (t (idx β)) (hne β) (t q)))
        (idx β) (opensSectionToTop_cartierSectionRatio_self D (t (idx β)) (hne β)) :=
  CoordinateAtlas.cover_morphism (cartierSectionsAtlas K D t idx hne hcover) β

/-- The preimage of a coordinate open is the generating open of the corresponding section. -/
theorem cartierSectionsMap_preimage (q : Fin M) :
    cartierSectionsMap K D t idx hne hcover ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X q) =
      cartierSectionNonvanishingOpen D (t q) := by
  ext x
  have hx : x ∈ ⨆ β, cartierSectionNonvanishingOpen D (t (idx β)) := by
    rw [hcover]
    trivial
  obtain ⟨β, hβ⟩ := Opens.mem_iSup.mp hx
  have H : (cartierSectionNonvanishingOpen D (t (idx β))).ι ⁻¹ᵁ
        (cartierSectionsMap K D t idx hne hcover ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X q)) =
      (cartierSectionNonvanishingOpen D (t (idx β))).ι ⁻¹ᵁ
        cartierSectionNonvanishingOpen D (t q) := by
    rw [← Scheme.Hom.comp_preimage, cartierSectionsMap_ι, coordinatesMap_preimage]
    change (cartierSectionNonvanishingOpen D (t (idx β))).toScheme.basicOpen
      ((cartierSectionNonvanishingOpen D (t (idx β))).ι.appLE
        (cartierSectionNonvanishingOpen D (t (idx β))) ⊤
        (cartierSectionNonvanishingOpen D (t (idx β))).ι_preimage_self.ge
        (cartierSectionRatio D (t (idx β)) (hne β) (t q))) = _
    rw [Scheme.basicOpen_appLE, basicOpen_cartierSectionRatio, Scheme.Hom.preimage_inf,
      Scheme.Opens.ι_preimage_self, top_inf_eq, top_inf_eq]
  exact Set.ext_iff.mp (congrArg SetLike.coe H)
    (⟨x, hβ⟩ : (cartierSectionNonvanishingOpen D (t (idx β))).toScheme)

/-- The structure morphism of the polynomial projective scheme is the one of the pinned
coordinate-atlas library. -/
theorem polynomialProjectiveToBase_eq_projectiveBase :
    polynomialProjectiveToBase M K = projectiveBase (K := K) (σ := Fin M) := rfl

/-- The morphism defined by sections is a morphism over the base field. -/
theorem cartierSectionsMap_over :
    cartierSectionsMap K D t idx hne hcover ≫ polynomialProjectiveToBase M K =
      X ↘ Spec (CommRingCat.of K) := by
  rw [polynomialProjectiveToBase_eq_projectiveBase]
  refine Eq.trans ?_ (toSpec_scalarMap (X ↘ Spec (CommRingCat.of K)))
  apply (X.openCoverOfIsOpenCover
    (fun β : ι => cartierSectionNonvanishingOpen D (t (idx β))) (IsOpenCover.mk hcover)).hom_ext
  intro β
  change (cartierSectionNonvanishingOpen D (t (idx β))).ι ≫ _ =
    (cartierSectionNonvanishingOpen D (t (idx β))).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, cartierSectionsMap_ι, coordinatesMap_over]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end Atlas

end MixedFujita

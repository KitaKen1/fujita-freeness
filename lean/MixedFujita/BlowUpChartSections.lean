/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Hironaka.Scheme.BlowUp.Glue.GlobalCharts

/-!
Functions on the charts of a blow-up. For an affine open U of a scheme and an element a of the
centre ideal on U, the chart of a is an affine open of the blow-up over U, and its ring of
functions is the affine blow-up algebra Γ(U)[I(U)/a]. Under this identification the constants are
the pulled back functions of U, the fraction b/a times the pull-back of a is the pull-back of b,
the fraction b/a does not vanish exactly on the chart of b, and the ring is generated over the
pulled back functions by the fractions of any generating family of the ideal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData

namespace MixedFujita

universe u

section OpenImmersion

theorem openImmersion_top_le_preimage_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : (⊤ : X.Opens) ≤ f ⁻¹ᵁ f.opensRange :=
  fun x _ => ⟨x, rfl⟩

/-- Functions on the image of an open immersion, restricted to the source, are the global
functions of the source. -/
theorem openImmersion_ΓIsoTop_hom_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).hom ≫
        f.appLE f.opensRange ⊤ (openImmersion_top_le_preimage_opensRange f) = 𝟙 _ := by
  have h : f.opensRange = f ''ᵁ ⊤ := f.image_top_eq_opensRange.symm
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ f ''ᵁ ⊤ := by rw [f.preimage_image_eq]
  have h1 : (IsOpenImmersion.ΓIsoTop f).hom =
      (f.appIso ⊤).inv ≫ Y.presheaf.map (eqToHom h).op := rfl
  rw [h1, Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appIso_inv_appLE f e]
  exact X.presheaf.map_id _

theorem openImmersion_ΓIsoTop_inv_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv =
      f.appLE f.opensRange ⊤ (openImmersion_top_le_preimage_opensRange f) := by
  rw [← cancel_epi (IsOpenImmersion.ΓIsoTop f).hom, Iso.hom_inv_id,
    openImmersion_ΓIsoTop_hom_appLE]

/-- A global function of the source of an open immersion, read on the image, does not vanish
exactly on the image of its basic open. -/
theorem openImmersion_basicOpen_ΓIsoTop_hom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (r : Γ(X, ⊤)) :
    Y.basicOpen ((IsOpenImmersion.ΓIsoTop f).hom r) = f ''ᵁ X.basicOpen r := by
  rw [Scheme.image_basicOpen]
  exact Scheme.basicOpen_res_eq _ _ _

theorem affineOpen_fromSpec_appLE_self {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  have h : (Scheme.ΓSpecIso Γ(X, U)).hom ≫ hU.fromSpec.appLE U ⊤ e = 𝟙 _ := by
    rw [Scheme.Hom.appLE, ← Category.assoc, hU.ΓSpecIso_hom_fromSpec_app, ← Functor.map_comp]
    exact (Spec Γ(X, U)).presheaf.map_id _
  rw [← cancel_epi (Scheme.ΓSpecIso Γ(X, U)).hom, h, Iso.hom_inv_id]

/-- The functions of an affine open, pulled back along the spectrum of a ring map from them, are
the images under the ring map. -/
theorem affineOpen_appLE_Spec_map_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {B : CommRingCat.{u}} (φ : Γ(X, U) ⟶ B)
    (e : (⊤ : (Spec B).Opens) ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ e = φ ≫ (Scheme.ΓSpecIso B).inv := by
  have e1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
  have e2 : (⊤ : (Spec B).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h := Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec U ⊤ ⊤ e1 e2
  rw [← h, affineOpen_fromSpec_appLE_self, Scheme.ΓSpecIso_inv_naturality]
  congr 1

theorem schemeHom_appLE_comp_of_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (hfg : f ≫ g = h) (U : Z.Opens) (V : Y.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) :
    g.appLE U V e₁ ≫ f.appLE V W e₂ = h.appLE U W e₃ := by
  subst hfg
  exact Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂

end OpenImmersion

section SpecChart

variable {B : CommRingCat.{u}} {Y : Scheme.{u}} (f : Spec B ⟶ Y) [IsOpenImmersion f]

/-- Elements of a ring, as functions on the image of an open immersion of its spectrum. -/
noncomputable def specChartSection : B →+* Γ(Y, f.opensRange) :=
  (IsOpenImmersion.ΓIsoTop f).hom.hom.comp (Scheme.ΓSpecIso B).inv.hom

theorem specChartSection_bijective : Function.Bijective (specChartSection f) :=
  (ConcreteCategory.bijective_of_isIso (IsOpenImmersion.ΓIsoTop f).hom).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv)

/-- Restricting a function of the image to the spectrum recovers the element. -/
theorem specChart_appLE_section (b : B) :
    f.appLE f.opensRange ⊤ (openImmersion_top_le_preimage_opensRange f)
        (specChartSection f b) = (Scheme.ΓSpecIso B).inv b := by
  have h := ConcreteCategory.congr_hom (openImmersion_ΓIsoTop_hom_appLE f)
    ((Scheme.ΓSpecIso B).inv b)
  rw [CommRingCat.comp_apply, CommRingCat.id_apply] at h
  exact h

theorem specChart_appLE_injective :
    Function.Injective (f.appLE f.opensRange ⊤ (openImmersion_top_le_preimage_opensRange f)) := by
  rw [← openImmersion_ΓIsoTop_inv_eq]
  exact (ConcreteCategory.bijective_of_isIso (IsOpenImmersion.ΓIsoTop f).inv).injective

/-- If the chart lies over an affine open through a ring map, the images under the ring map are
the functions pulled back from the affine open. -/
theorem specChartSection_eq_appLE {X : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) (φ : Γ(X, U) ⟶ B) (hfg : f ≫ g = Spec.map φ ≫ hU.fromSpec)
    (e : f.opensRange ≤ g ⁻¹ᵁ U) (r : Γ(X, U)) :
    specChartSection f (φ r) = g.appLE U f.opensRange e r := by
  apply specChart_appLE_injective f
  rw [specChart_appLE_section]
  have e3 : (⊤ : (Spec B).Opens) ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro x _
    rw [← hfg]
    exact e ⟨x, rfl⟩
  have h1 := schemeHom_appLE_comp_of_eq f g _ hfg U f.opensRange ⊤ e
    (openImmersion_top_le_preimage_opensRange f) e3
  rw [affineOpen_appLE_Spec_map_fromSpec] at h1
  have h2 := ConcreteCategory.congr_hom h1 r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
  exact h2.symm

/-- An element does not vanish, as a function on the image, exactly on the image of its basic
open. -/
theorem basicOpen_specChartSection (b : B) :
    Y.basicOpen (specChartSection f b) =
      f ''ᵁ (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv b) :=
  openImmersion_basicOpen_ΓIsoTop_hom f _

/-- If the preimage of an open under the chart is the basic open of an element, the element does
not vanish, as a function on the image, exactly on that open. -/
theorem basicOpen_specChartSection_of_preimage (b : B) (W : Y.Opens)
    (h : f ⁻¹ᵁ W = PrimeSpectrum.basicOpen b) :
    Y.basicOpen (specChartSection f b) = f.opensRange ⊓ W := by
  have h1 := basicOpen_specChartSection f b
  have h2 : (Spec B).basicOpen ((Scheme.ΓSpecIso B).inv b) = f ⁻¹ᵁ W :=
    (basicOpen_eq_of_affine b).trans h.symm
  rw [h2, Scheme.Hom.image_preimage_eq_opensRange_inf] at h1
  exact h1

end SpecChart

section Algebra

variable {R : Type u} [CommRing R] {J : Ideal R} {a : R}

open IsLocalization.Away

/-- The fraction x/a times a is x. -/
theorem affineBlowUpAlgebra_frac_mul {x : R} (hx : x ∈ J) :
    affineBlowUpAlgebra.frac (a := a) hx * algebraMap R (affineBlowUpAlgebra J a) a =
      algebraMap R (affineBlowUpAlgebra J a) x := by
  apply Subtype.ext
  change algebraMap R (Localization.Away a) x * invSelf a * algebraMap R (Localization.Away a) a =
    algebraMap R (Localization.Away a) x
  rw [mul_assoc, mul_comm (invSelf a), mul_invSelf, mul_one]

/-- The fraction a/a is 1. -/
theorem affineBlowUpAlgebra_frac_self (ha : a ∈ J) :
    affineBlowUpAlgebra.frac (a := a) ha = 1 := by
  apply Subtype.ext
  change algebraMap R (Localization.Away a) a * invSelf a = 1
  exact mul_invSelf a

theorem affineBlowUpAlgebra_frac_add {x y : R} (hx : x ∈ J) (hy : y ∈ J) :
    affineBlowUpAlgebra.frac (a := a) (J.add_mem hx hy) =
      affineBlowUpAlgebra.frac hx + affineBlowUpAlgebra.frac hy := by
  apply Subtype.ext
  change algebraMap R (Localization.Away a) (x + y) * invSelf a =
    algebraMap R (Localization.Away a) x * invSelf a +
      algebraMap R (Localization.Away a) y * invSelf a
  rw [map_add, add_mul]

theorem affineBlowUpAlgebra_frac_mul_left (r : R) {x : R} (hx : x ∈ J) :
    affineBlowUpAlgebra.frac (a := a) (J.mul_mem_left r hx) =
      algebraMap R (affineBlowUpAlgebra J a) r * affineBlowUpAlgebra.frac hx := by
  apply Subtype.ext
  change algebraMap R (Localization.Away a) (r * x) * invSelf a =
    algebraMap R (Localization.Away a) r * (algebraMap R (Localization.Away a) x * invSelf a)
  rw [map_mul, mul_assoc]

/-- A ring map from the affine blow-up algebra sends everything into a subring that contains
the images of the constants and of the fractions of a generating family of the ideal. -/
theorem affineBlowUpAlgebra_map_mem_subring {C : Type*} [CommRing C] {m : ℕ} (g : Fin m → R)
    (hg : Ideal.span (Set.range g) = J) (ψ : affineBlowUpAlgebra J a →+* C) (S : Subring C)
    (hR : ∀ r, ψ (algebraMap R (affineBlowUpAlgebra J a) r) ∈ S)
    (hG : ∀ l, ψ (affineBlowUpAlgebra.frac (a := a)
      (hg ▸ Ideal.subset_span (Set.mem_range_self l) : g l ∈ J)) ∈ S)
    (b : affineBlowUpAlgebra J a) : ψ b ∈ S := by
  have hfrac : ∀ y (_ : y ∈ Ideal.span (Set.range g)), ∀ hy : y ∈ J,
      ψ (affineBlowUpAlgebra.frac (a := a) hy) ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      intro _
      exact hG l
    | zero =>
      intro h0J
      have h0 : affineBlowUpAlgebra.frac (a := a) h0J = 0 := by
        apply Subtype.ext
        change algebraMap R (Localization.Away a) 0 * invSelf a = 0
        rw [map_zero, zero_mul]
      rw [h0, map_zero]
      exact zero_mem S
    | add y z hy hz ihy ihz =>
      intro hyz
      have hyJ : y ∈ J := hg ▸ hy
      have hzJ : z ∈ J := hg ▸ hz
      have h : affineBlowUpAlgebra.frac (a := a) hyz =
          affineBlowUpAlgebra.frac hyJ + affineBlowUpAlgebra.frac hzJ :=
        affineBlowUpAlgebra_frac_add hyJ hzJ
      rw [h, map_add]
      exact add_mem (ihy hyJ) (ihz hzJ)
    | smul r y hy ih =>
      intro hry
      have hyJ : y ∈ J := hg ▸ hy
      have h : affineBlowUpAlgebra.frac (a := a) hry =
          algebraMap R (affineBlowUpAlgebra J a) r * affineBlowUpAlgebra.frac hyJ :=
        affineBlowUpAlgebra_frac_mul_left r hyJ
      rw [h, map_mul]
      exact mul_mem (hR r) (ih hyJ)
  obtain ⟨y, hy⟩ := b
  induction hy using affineBlowUpAlgebra.induction_on with
  | mem x hx => exact hfrac x (hg ▸ hx) hx
  | algebraMap r => exact hR r
  | add y z hy hz ihy ihz =>
    have h : (⟨y + z, add_mem hy hz⟩ : affineBlowUpAlgebra J a) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [h, map_add]
    exact add_mem ihy ihz
  | mul y z hy hz ihy ihz =>
    have h : (⟨y * z, mul_mem hy hz⟩ : affineBlowUpAlgebra J a) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [h, map_mul]
    exact mul_mem ihy ihz

/-- A subring of the target of a surjective ring map from the affine blow-up algebra is
everything if it contains the images of the constants and of the fractions of a generating family
of the ideal. -/
theorem affineBlowUpAlgebra_subring_eq_top {C : Type*} [CommRing C] {m : ℕ} (g : Fin m → R)
    (hg : Ideal.span (Set.range g) = J) (ψ : affineBlowUpAlgebra J a →+* C)
    (hψ : Function.Surjective ψ) (S : Subring C)
    (hR : ∀ r, ψ (algebraMap R (affineBlowUpAlgebra J a) r) ∈ S)
    (hG : ∀ l, ψ (affineBlowUpAlgebra.frac (a := a)
      (hg ▸ Ideal.subset_span (Set.mem_range_self l) : g l ∈ J)) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, rfl⟩ := hψ x
  exact affineBlowUpAlgebra_map_mem_subring g hg ψ S hR hG b

end Algebra

section Chart

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- The open of the blow-up covered by the chart of a. -/
noncomputable def blowUpChartOpen : (blowUp I).Opens := (blowUp.chart I U a).opensRange

theorem blowUpChartOpen_le_preimage : blowUpChartOpen I U a ≤ blowUpπ I ⁻¹ᵁ U.1 :=
  fun _ hx => blowUp.range_chart_subset I U a hx

theorem isAffineOpen_blowUpChartOpen : IsAffineOpen (blowUpChartOpen I U a) :=
  isAffineOpen_opensRange (blowUp.chart I U a)

/-- Elements of the affine blow-up algebra, as functions on the chart. -/
noncomputable def blowUpChartSection :
    affineBlowUpAlgebra (I.ideal U) a →+* Γ(blowUp I, blowUpChartOpen I U a) :=
  specChartSection (blowUp.chart I U a)

theorem blowUpChartSection_bijective : Function.Bijective (blowUpChartSection I U a) :=
  specChartSection_bijective (blowUp.chart I U a)

/-- Constants of the chart are the functions pulled back from the affine open. -/
theorem blowUpChartSection_algebraMap (r : Γ(X, U)) :
    blowUpChartSection I U a (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a) r) =
      (blowUpπ I).appLE U.1 (blowUpChartOpen I U a) (blowUpChartOpen_le_preimage I U a) r :=
  specChartSection_eq_appLE (blowUp.chart I U a) (blowUpπ I) (affineOpens_isAffineOpen U)
    (CommRingCat.ofHom (algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a)))
    (by rw [blowUp.chart_π, IsAffineOpen.isoSpec_inv_ι]) (blowUpChartOpen_le_preimage I U a) r

/-- The fraction b/a of the affine blow-up algebra is the generator named ratio. -/
theorem affineBlowUpAlgebra_ratio_eq_frac (b : I.ideal U) :
    affineBlowUpAlgebra.ratio (I.ideal U) a b =
      affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2 :=
  Subtype.ext (affineBlowUpAlgebra.coe_frac_eq_awayFrac _).symm

/-- The fraction b/a does not vanish exactly on the chart of b, inside the chart of a. -/
theorem basicOpen_blowUpChartSection_frac (b : I.ideal U) :
    (blowUp I).basicOpen (blowUpChartSection I U a
        (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2)) =
      blowUpChartOpen I U a ⊓ blowUpChartOpen I U b :=
  basicOpen_specChartSection_of_preimage (blowUp.chart I U a)
    (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2) (blowUp.chart I U b).opensRange
    (affineBlowUpAlgebra_ratio_eq_frac I U a b ▸ blowUp.chart_preimage_chart I U a b)

/-- The fraction b/a times the pull-back of a is the pull-back of b. -/
theorem blowUpChartSection_frac_mul (b : I.ideal U) :
    blowUpChartSection I U a (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) b.2) *
        (blowUpπ I).appLE U.1 (blowUpChartOpen I U a) (blowUpChartOpen_le_preimage I U a)
          (a : Γ(X, U)) =
      (blowUpπ I).appLE U.1 (blowUpChartOpen I U a) (blowUpChartOpen_le_preimage I U a)
        (b : Γ(X, U)) := by
  rw [← blowUpChartSection_algebraMap, ← map_mul, affineBlowUpAlgebra_frac_mul,
    blowUpChartSection_algebraMap]

/-- The fraction a/a is the function 1. -/
theorem blowUpChartSection_frac_self :
    blowUpChartSection I U a (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) a.2) = 1 := by
  rw [affineBlowUpAlgebra_frac_self, map_one]

/-- The pull-back of a is not zero on a chart with nonzero ring of functions. -/
theorem blowUpπ_appLE_chart_ne_zero [Nontrivial Γ(blowUp I, blowUpChartOpen I U a)] :
    (blowUpπ I).appLE U.1 (blowUpChartOpen I U a) (blowUpChartOpen_le_preimage I U a)
      (a : Γ(X, U)) ≠ 0 := by
  rw [← blowUpChartSection_algebraMap]
  intro h
  have h0 : algebraMap Γ(X, U) (affineBlowUpAlgebra (I.ideal U) a) (a : Γ(X, U)) = 0 :=
    (blowUpChartSection_bijective I U a).injective (h.trans (map_zero _).symm)
  have h1 : (1 : affineBlowUpAlgebra (I.ideal U) a) = 0 := by
    have hz := affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors
      (I := I.ideal U) (a := (a : Γ(X, U)))
    rw [h0] at hz
    exact (mem_nonZeroDivisors_iff.mp hz).2 1 (mul_zero 1)
  have h2 : (1 : Γ(blowUp I, blowUpChartOpen I U a)) = 0 := by
    rw [← map_one (blowUpChartSection I U a), h1, map_zero]
  exact one_ne_zero h2

/-- A subring of the functions of a chart containing the pulled back functions and the fractions
of a generating family of the ideal is everything. -/
theorem blowUpChart_subring_eq_top {m : ℕ} (g : Fin m → I.ideal U)
    (hg : Ideal.span (Set.range fun l => (g l : Γ(X, U))) = I.ideal U)
    (S : Subring Γ(blowUp I, blowUpChartOpen I U a))
    (hR : ∀ r : Γ(X, U), (blowUpπ I).appLE U.1 (blowUpChartOpen I U a)
      (blowUpChartOpen_le_preimage I U a) r ∈ S)
    (hG : ∀ l, blowUpChartSection I U a
      (affineBlowUpAlgebra.frac (a := (a : Γ(X, U))) (g l).2) ∈ S) : S = ⊤ :=
  affineBlowUpAlgebra_subring_eq_top (fun l => (g l : Γ(X, U))) hg (blowUpChartSection I U a)
    (blowUpChartSection_bijective I U a).surjective S
    (fun r => by rw [blowUpChartSection_algebraMap]; exact hR r) hG

end Chart

end MixedFujita

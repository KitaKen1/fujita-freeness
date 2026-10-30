/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionsTrivialization
public import SGA.Foundations.Cohomology.BaseChangeSections
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
Base change of functions on affine opens (step 10, R4).

For a scheme `X` over `Spec A`, an `A`-algebra `L` and the pullback `Y = X ×_A L`, the functions on
the inverse image of an affine open `V ⊆ X` are `L ⊗_A Γ(X, V)` (`sectionsBaseChangeEquiv`, from
SGA's affine base change), as an `L`-algebra, with `l ⊗ a ↦ l · a|_Y`
(`sectionsBaseChangeEquiv_tmul`), compatibly with restrictions
(`sectionsBaseChangeEquiv_restrict`). This is the base change of the Čech cochains of a model
to its fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The algebra structure on the functions of a scheme over `Spec A`. -/
@[instance_reducible]
noncomputable def structureSectionsAlgebra (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] (V : X.Opens) : Algebra A Γ(X, V) :=
  ((X.baseRingToStructurePresheaf A).app (op V)).hom.toAlgebra

attribute [local instance] structureSectionsAlgebra

theorem structureSections_algebraMap (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] (V : X.Opens) :
    CommRingCat.ofHom (algebraMap A Γ(X, V)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (X ↘ Spec (CommRingCat.of A)).appLE ⊤ V le_top := by
  rw [← Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  rfl

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of L))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A L))))

/-- The restriction of functions as an algebra map over the base. -/
noncomputable def structureRestrictAlgHom (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] {V W : X.Opens} (h : W ≤ V) : Γ(X, V) →ₐ[A] Γ(X, W) where
  toRingHom := (X.presheaf.map (homOfLE h).op).hom
  commutes' a := by
    have hnat := (X.baseRingToStructurePresheaf A).naturality (homOfLE h).op
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hnat
    change (X.presheaf.map (homOfLE h).op).hom
      (((X.baseRingToStructurePresheaf A).app (op V)).hom a) =
        ((X.baseRingToStructurePresheaf A).app (op W)).hom a
    rw [hnat]
    rfl

theorem structureRestrictAlgHom_apply (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] {V W : X.Opens} (h : W ≤ V) (a : Γ(X, V)) :
    structureRestrictAlgHom A X h a = X.presheaf.map (homOfLE h).op a :=
  rfl

include H in
/-- **Affine base change of functions as an `L`-algebra isomorphism**. -/
noncomputable def sectionsBaseChangeEquiv {V : X.Opens} (hV : IsAffineOpen V) :
    L ⊗[A] Γ(X, V) ≃ₐ[L] Γ(Y, g ⁻¹ᵁ V) :=
  letI : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  letI : Algebra A Γ(Y, g ⁻¹ᵁ V) :=
    (CommRingCat.ofHom (algebraMap A Γ(X, V)) ≫ g.appLE V (g ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  haveI : IsScalarTower A Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A L Γ(Y, g ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun a => by
    have hsq := CohomologyAux.isPushout_baseChange H hV
    rw [← structureSections_algebraMap, ← structureSections_algebraMap] at hsq
    exact ConcreteCategory.congr_hom hsq.w a
  haveI : Algebra.IsPushout A Γ(X, V) L Γ(Y, g ⁻¹ᵁ V) := by
    have hsq := CohomologyAux.isPushout_baseChange H hV
    rw [← structureSections_algebraMap, ← structureSections_algebraMap] at hsq
    exact CommRingCat.isPushout_iff_isPushout.mp hsq
  haveI : Algebra.IsPushout A L Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := Algebra.IsPushout.symm inferInstance
  Algebra.IsPushout.equiv A L Γ(X, V) Γ(Y, g ⁻¹ᵁ V)

/-- **The base change of `l ⊗ a` is `l · a|_Y`.** -/
theorem sectionsBaseChangeEquiv_tmul {V : X.Opens} (hV : IsAffineOpen V) (l : L) (a : Γ(X, V)) :
    sectionsBaseChangeEquiv H hV (l ⊗ₜ a) =
      algebraMap L Γ(Y, g ⁻¹ᵁ V) l * g.appLE V (g ⁻¹ᵁ V) le_rfl a := by
  let _ : Algebra Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := (g.appLE V (g ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  let _ : Algebra A Γ(Y, g ⁻¹ᵁ V) :=
    (CommRingCat.ofHom (algebraMap A Γ(X, V)) ≫ g.appLE V (g ⁻¹ᵁ V) le_rfl).hom.toAlgebra
  have _ : IsScalarTower A Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A L Γ(Y, g ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun a => by
    have hsq := CohomologyAux.isPushout_baseChange H hV
    rw [← structureSections_algebraMap, ← structureSections_algebraMap] at hsq
    exact ConcreteCategory.congr_hom hsq.w a
  have _ : Algebra.IsPushout A Γ(X, V) L Γ(Y, g ⁻¹ᵁ V) := by
    have hsq := CohomologyAux.isPushout_baseChange H hV
    rw [← structureSections_algebraMap, ← structureSections_algebraMap] at hsq
    exact CommRingCat.isPushout_iff_isPushout.mp hsq
  have _ : Algebra.IsPushout A L Γ(X, V) Γ(Y, g ⁻¹ᵁ V) := Algebra.IsPushout.symm inferInstance
  exact Algebra.IsPushout.equiv_tmul (R := A) (S := L) (R' := Γ(X, V)) (S' := Γ(Y, g ⁻¹ᵁ V)) l a

/-- **Base change commutes with restriction.** -/
theorem sectionsBaseChangeEquiv_restrict {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) (t : L ⊗[A] Γ(X, V)) :
    sectionsBaseChangeEquiv H hW ((structureRestrictAlgHom A X h).toLinearMap.lTensor L t) =
      Y.presheaf.map (homOfLE ((Opens.map g.base).monotone h)).op (sectionsBaseChangeEquiv H hV t) := by
  induction t using TensorProduct.inductionOn with
  | tmul l a =>
    rw [LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, structureRestrictAlgHom_apply,
      sectionsBaseChangeEquiv_tmul, sectionsBaseChangeEquiv_tmul, map_mul]
    congr 1
    · exact (AlgHom.commutes (structureRestrictAlgHom L Y ((Opens.map g.base).monotone h)) l).symm
    · rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
        Scheme.Hom.appLE_map]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

end MixedFujita

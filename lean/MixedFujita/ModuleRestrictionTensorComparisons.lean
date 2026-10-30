/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePullbackRestriction
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
The actual scheme pushforward comparison in pullback/restriction is monoidal.
Restriction receives the canonical oplax structure induced by its actual
adjunction. The constructed pullback/restriction natural isomorphism is
conjugate to the inverse pushforward comparison, as proved from actual unit
compatibility. This yields tensor compatibility for these actual functors,
including an explicit formula for their canonical tensor comparisons.
No invertibility of the open-restriction tensor comparison, global Cartier
tensor comparison or compatible all-graded pullback presentation is supplied
or asserted here. These are separate subsequent proof obligations.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}

theorem modulePushforwardCongr_isMonoidal {φ ψ : Y ⟶ X} (h : φ = ψ) :
    NatTrans.IsMonoidal (Scheme.Modules.pushforwardCongr h).hom := by
  subst ψ
  have he : (Scheme.Modules.pushforwardCongr (rfl : φ = φ)).hom =
      𝟙 (Scheme.Modules.pushforward φ) := by
    ext M U x
    simp
  rw [he]
  infer_instance

theorem modulePullbackRestrictionPushforwardIso_isMonoidal (φ : Y ⟶ X) (U : X.Opens) :
    NatTrans.IsMonoidal (modulePullbackRestrictionPushforwardIso φ U).hom := by
  unfold modulePullbackRestrictionPushforwardIso
  have := modulePushforwardCongr_isMonoidal (morphismRestrict_ι φ U).symm
  simp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

@[instance_reducible]
noncomputable def moduleRestrictOplaxMonoidal (φ : Y ⟶ X) [IsOpenImmersion φ] :
    (Scheme.Modules.restrictFunctor φ).OplaxMonoidal :=
  (Scheme.Modules.restrictAdjunction φ).leftAdjointOplaxMonoidal

open CategoryTheory.Adjunction
universe v₁ v₂ u₁ u₂

theorem adjunctionConjugate_eq_of_unit_compatibility
    {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]
    {F₁ F₂ : C ⥤ B} {G₁ G₂ : B ⥤ C} (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂)
    (σ : F₂ ⟶ F₁) (τ : G₁ ⟶ G₂)
    (h : ∀ M, a₂.unit.app M ≫ G₂.map (σ.app M) = a₁.unit.app M ≫ τ.app (F₁.obj M)) :
    conjugateEquiv a₁ a₂ σ = τ := by
  apply (conjugateEquiv a₁ a₂).symm.injective
  simp only [Equiv.symm_apply_apply]
  ext M
  apply (a₂.homEquiv M (F₁.obj M)).injective
  simp only [homEquiv_unit]
  exact (h M).trans (unit_conjugateEquiv_symm a₁ a₂ τ M)

variable {X Y : Scheme.{u}}
attribute [local instance] moduleRestrictOplaxMonoidal

theorem moduleRestrictAdjunction_isMonoidal (φ : Y ⟶ X) [IsOpenImmersion φ] :
    (Scheme.Modules.restrictAdjunction φ).IsMonoidal := by
  exact inferInstanceAs (letI := (Scheme.Modules.restrictAdjunction φ).leftAdjointOplaxMonoidal
    (Scheme.Modules.restrictAdjunction φ).IsMonoidal)

attribute [local instance] moduleRestrictAdjunction_isMonoidal

noncomputable def modulePullbackRestrictionNatIso (φ : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback φ ⋙ Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (φ ∣_ U) :=
  (modulePullbackRestrictionAdjunction φ U).leftAdjointUniq
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)))

theorem modulePullbackRestrictionNatIso_app (φ : Y ⟶ X) (U : X.Opens) (M : X.Modules) :
    (modulePullbackRestrictionNatIso φ U).app M = modulePullbackRestrictionIso φ U M := rfl

theorem modulePullbackRestrictionNatIso_conjugate (φ : Y ⟶ X) (U : X.Opens) :
    conjugateEquiv
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U)))
      ((Scheme.Modules.pullbackPushforwardAdjunction φ).comp
        (Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι))
      (modulePullbackRestrictionNatIso φ U).hom =
    (modulePullbackRestrictionPushforwardIso φ U).inv := by
  apply adjunctionConjugate_eq_of_unit_compatibility
  intro M
  let A := (Scheme.Modules.pullbackPushforwardAdjunction φ).comp
    (Scheme.Modules.restrictAdjunction (φ ⁻¹ᵁ U).ι)
  let B := (Scheme.Modules.restrictAdjunction U.ι).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (φ ∣_ U))
  let C := modulePullbackRestrictionPushforwardIso φ U
  let σ := (modulePullbackRestrictionIso φ U M).hom
  change A.unit.app M ≫
      (Scheme.Modules.pushforward (φ ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward φ).map σ =
    B.unit.app M ≫ C.inv.app _
  apply (cancel_mono (C.hom.app ((Scheme.Modules.restrictFunctor U.ι ⋙
    Scheme.Modules.pullback (φ ∣_ U)).obj M))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact (congrArg (A.unit.app M ≫ ·) (C.hom.naturality σ)).trans
    (by
      dsimp only [A, B, C, σ, Functor.comp_map, Functor.comp_obj]
      rw [Category.comp_id]
      simpa only [Adjunction.comp_unit_app, Category.assoc] using
        modulePullbackRestrictionIso_unit_explicit φ U M)

theorem modulePullbackRestrictionNatIso_tensor (φ : Y ⟶ X) (U : X.Opens)
    (M N : X.Modules) :
    (modulePullbackRestrictionNatIso φ U).hom.app (M ⊗ N) ≫
      Functor.OplaxMonoidal.δ
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (φ ∣_ U)) M N =
    Functor.OplaxMonoidal.δ
        (Scheme.Modules.pullback φ ⋙ Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι) M N ≫
      ((modulePullbackRestrictionNatIso φ U).hom.app M ⊗ₘ
        (modulePullbackRestrictionNatIso φ U).hom.app N) := by
  have := modulePullbackRestrictionPushforwardIso_isMonoidal φ U
  exact Adjunction.app_tensor_comp_δ_of_conjugateEquiv _ _
    (modulePullbackRestrictionNatIso_conjugate φ U) M N

theorem modulePullbackRestrictionIso_tensor_explicit (φ : Y ⟶ X) (U : X.Opens)
    (M N : X.Modules) :
    (modulePullbackRestrictionIso φ U (M ⊗ N)).hom ≫
      (Scheme.Modules.pullback (φ ∣_ U)).map
        (Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor U.ι) M N) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
        (M.restrict U.ι) (N.restrict U.ι) =
    (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι).map
        (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) ≫
      Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι)
        ((Scheme.Modules.pullback φ).obj M) ((Scheme.Modules.pullback φ).obj N) ≫
      ((modulePullbackRestrictionIso φ U M).hom ⊗ₘ
        (modulePullbackRestrictionIso φ U N).hom) := by
  have h := modulePullbackRestrictionNatIso_tensor φ U M N
  change (modulePullbackRestrictionIso φ U (M ⊗ N)).hom ≫
      Functor.OplaxMonoidal.δ
        (Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (φ ∣_ U)) M N =
    Functor.OplaxMonoidal.δ
        (Scheme.Modules.pullback φ ⋙ Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι) M N ≫
      ((modulePullbackRestrictionIso φ U M).hom ⊗ₘ
        (modulePullbackRestrictionIso φ U N).hom) at h
  simpa only [Functor.OplaxMonoidal.comp_δ, Functor.comp_obj, Category.assoc] using h

end MixedFujita

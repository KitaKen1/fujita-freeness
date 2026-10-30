/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePullbackTensorFrames
public import MixedFujita.ModulePushforwardSheafification
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
The actual tensor map for restriction of module scalars along a ring
isomorphism is an isomorphism. The balanced tensor equivalence is identified
with the existing canonical map on pure tensors. The corresponding
presheaf pushforward unit and tensor maps are isomorphisms for an actual
coefficient-presheaf isomorphism.
For actual continuous and cocontinuous site pushforward, the canonical
sheaf tensor map is an isomorphism when the coefficient-sheaf map is an
isomorphism. Sheafification/pushforward commutation is proved with the
actual coefficient map; the inclusion of sheaves into presheaves is not
assumed to preserve tensor isomorphisms before sheafification.
For an actual scheme open immersion, its coefficient-map isomorphism,
canonical lax tensor/unit isomorphisms and a strong monoidal structure
extending this lax structure are constructed. The inverse of this tensor
map is not yet identified with the oplax tensor comparison induced by the
separate restriction/pushforward adjunction. Consequently global Cartier
pullback tensor gluing and all-graded pullback representations remain
subsequent proof obligations, not conclusions of this module. A general
monoidal-adjunction compatibility theorem is proved from monoidality of the
actual adjunction unit; this property of the scheme restriction unit under
the newly constructed strong structure remains a separate obligation.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

theorem moduleRestrictScalars_tensor_isIso_of_ringEquiv
    (e : R ≃+* S) (M N : ModuleCat S) :
    IsIso (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N) := by
  let : Module R M := Module.compHom M e.toRingHom
  let : Module R N := Module.compHom N e.toRingHom
  let : SMulCommClass S R M := ⟨fun s r m ↦ by
    change s • (e r • m) = e r • (s • m)
    exact smul_comm s (e r) m⟩
  let : TensorProduct.CompatibleSMul S R M N := ⟨fun r m n ↦ by
    change (e r • m) ⊗ₜ[S] n = m ⊗ₜ[S] (e r • n)
    exact TensorProduct.smul_tmul (e r) m n⟩
  let : TensorProduct.CompatibleSMul R S M N := ⟨fun s m n ↦ by
    obtain ⟨r, rfl⟩ := e.surjective s
    change (r • m) ⊗ₜ[R] n = m ⊗ₜ[R] (r • n)
    exact TensorProduct.smul_tmul r m n⟩
  let L := TensorProduct.equivOfCompatibleSMul S R R M N
  have h : Functor.LaxMonoidal.μ (ModuleCat.restrictScalars e.toRingHom) M N =
      L.toModuleIso.hom := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rw [ModuleCat.restrictScalars_μ_tmul]
    rfl
  rw [h]
  infer_instance

universe v₁ v₂ u₁ u₂

theorem modulePresheafHom_isIso_of_app_isIso
    {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : PresheafOfModules.{u} R} (f : M ⟶ N) (h : ∀ X, IsIso (f.app X)) : IsIso f := by
  let e : M ≅ N := PresheafOfModules.isoMk (fun X ↦ by
    let := h X
    exact asIso (f.app X)) (by
      intro X Y g
      exact f.naturality g)
  have he : e.hom = f := rfl
  rw [← he]
  infer_instance

theorem modulePresheafPushforward_tensor_isIso_of_coefficientIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) [IsIso α]
    (M N : PresheafOfModulesOfCommRing.{u} R) :
    IsIso (Functor.LaxMonoidal.μ (PresheafOfModulesOfCommRing.pushforward.{u} α) M N) := by
  apply modulePresheafHom_isIso_of_app_isIso
  intro X
  have he : (Functor.LaxMonoidal.μ (PresheafOfModulesOfCommRing.pushforward.{u} α)
      M N).app X =
      Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app X).hom)
        (M.obj (F.op.obj X)) (N.obj (F.op.obj X)) := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    erw [TauCeti.PresheafOfModules.pushforward_μ_app_tmul,
      ModuleCat.restrictScalars_μ_tmul]
    rfl
  rw [he]
  exact moduleRestrictScalars_tensor_isIso_of_ringEquiv
    ((asIso (α.app X)).commRingCatIsoToRingEquiv) _ _

theorem modulePresheafPushforward_unit_isIso_of_coefficientIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {R : Dᵒᵖ ⥤ CommRingCat.{u}} {S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : S ⟶ F.op ⋙ R) [IsIso α] :
    IsIso (Functor.LaxMonoidal.ε (PresheafOfModulesOfCommRing.pushforward.{u} α)) := by
  apply modulePresheafHom_isIso_of_app_isIso
  intro X
  rw [ConcreteCategory.isIso_iff_bijective]
  have he : ((Functor.LaxMonoidal.ε
      (PresheafOfModulesOfCommRing.pushforward.{u} α)).app X : _ → _) =
      (α.app X : _ → _) := by
    funext r
    exact TauCeti.PresheafOfModules.pushforward_ε_app_apply F α X r
  rw [he]
  exact ((asIso (α.app X)).commRingCatIsoToRingEquiv).bijective

section SheafPushforward
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  (F : C ⥤ D) [F.IsContinuous J K]
  {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
  (φ : TauCeti.SheafOfModules.ringCatSheaf S ⟶
    (F.sheafPushforwardContinuous RingCat.{u} J K).obj
      (TauCeti.SheafOfModules.ringCatSheaf R))

noncomputable def moduleCommRingPushforwardHom : S.obj ⟶ F.op ⋙ R.obj where
  app U := CommRingCat.ofHom (φ.hom.app U).hom
  naturality _ _ f := by
    ext x
    exact congr($(φ.hom.naturality f).hom x)

theorem moduleCommRingPushforwardHom_isIso [IsIso φ] :
    IsIso (moduleCommRingPushforwardHom F φ) := by
  have : IsIso φ.hom := inferInstanceAs
    (IsIso ((sheafToPresheaf J RingCat.{u}).map φ))
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  have : IsIso ((forget₂ CommRingCat RingCat).map
      ((moduleCommRingPushforwardHom F φ).app U)) := by
    change IsIso (φ.hom.app U)
    infer_instance
  exact isIso_of_reflects_iso _ (forget₂ CommRingCat RingCat)

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
theorem moduleSheafPushforward_presheafTensor_isIso [IsIso φ]
    (M N : PresheafOfModulesOfCommRing.{u} R.obj) :
    IsIso (Functor.LaxMonoidal.μ (TauCeti.SheafOfModules.presheafPushforward φ) M N) := by
  let α := moduleCommRingPushforwardHom F φ
  have : IsIso α := moduleCommRingPushforwardHom_isIso F φ
  have he : Functor.LaxMonoidal.μ (TauCeti.SheafOfModules.presheafPushforward φ) M N =
      Functor.LaxMonoidal.μ (PresheafOfModulesOfCommRing.pushforward.{u} α) M N := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    erw [TauCeti.SheafOfModules.presheafPushforward_μ_app_tmul,
      TauCeti.PresheafOfModules.pushforward_μ_app_tmul]
    rfl
  rw [he]
  exact modulePresheafPushforward_tensor_isIso_of_coefficientIso F α M N

variable [F.IsCocontinuous J K]

theorem moduleSheafPushforward_forgetTensor_sheafification_isIso
    (M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).map
        ((TauCeti.SheafOfModules.presheafPushforward φ).map
          (Functor.LaxMonoidal.μ
            (SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf R)) M N))) := by
  have ha : TauCeti.SheafOfModules.sheafificationForgetAdjunction R =
      PresheafOfModules.sheafificationAdjunction
        (𝟙 (TauCeti.SheafOfModules.ringCatSheaf R).obj) := by
    apply Adjunction.ext_counit
    apply NatTrans.ext
    funext P
    exact (TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app R P).trans
      (TauCeti.SheafOfModules.sheafificationIso_hom _ _)
  rw [TauCeti.SheafOfModules.forget_μ, ha, Functor.map_comp, Functor.map_comp]
  have : IsIso ((PresheafOfModules.sheafification
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).map
        (modulePushforwardSheafificationUnit F φ (M.val ⊗ N.val))) :=
    modulePushforwardSheafificationUnit_sheafification_isIso F φ (M.val ⊗ N.val)
  have : IsIso (((SheafOfModules.pushforward φ).map (M.tensorUnderlyingIso N).inv).val) :=
    inferInstanceAs (IsIso ((SheafOfModules.forget
      (TauCeti.SheafOfModules.ringCatSheaf S)).map
        ((SheafOfModules.pushforward φ).map (M.tensorUnderlyingIso N).inv)))
  change IsIso ((PresheafOfModules.sheafification
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).map
        (modulePushforwardSheafificationUnit F φ (M.val ⊗ N.val)) ≫
    (PresheafOfModules.sheafification
      (𝟙 (TauCeti.SheafOfModules.ringCatSheaf S).obj)).map
        ((SheafOfModules.pushforward φ).map (M.tensorUnderlyingIso N).inv).val)
  infer_instance

theorem moduleSheafPushforward_tensor_isIso_of_coefficientIso [IsIso φ]
    (M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)) :
    IsIso (Functor.LaxMonoidal.μ (SheafOfModules.pushforward φ) M N) := by
  have := moduleSheafPushforward_presheafTensor_isIso F φ M.val N.val
  have := moduleSheafPushforward_forgetTensor_sheafification_isIso F φ M N
  rw [TauCeti.SheafOfModules.pushforward_μ, Functor.map_comp]
  infer_instance

omit [F.IsCocontinuous J K] in
theorem moduleSheafPushforward_unit_isIso_of_coefficientIso [IsIso φ] :
    IsIso (Functor.LaxMonoidal.ε (SheafOfModules.pushforward φ)) := by
  have : IsIso φ.hom := inferInstanceAs
    (IsIso ((sheafToPresheaf J RingCat.{u}).map φ))
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf S))]
  apply modulePresheafHom_isIso_of_app_isIso
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have he : (((SheafOfModules.forget (TauCeti.SheafOfModules.ringCatSheaf S)).map
      (Functor.LaxMonoidal.ε (SheafOfModules.pushforward φ))).app U : _ → _) =
      (φ.hom.app U : _ → _) := by
    funext r
    rw [TauCeti.SheafOfModules.pushforward_ε]
    rfl
  rw [he]
  exact (asIso (φ.hom.app U)).ringCatIsoToRingEquiv.bijective

end SheafPushforward

open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{u}}

theorem moduleOpenRestrictionRingHom_isIso (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (moduleOpenRestrictionRingHom f) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{u})]
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  change IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv)
  infer_instance

@[instance_reducible]
noncomputable def moduleOpenRestrictionLaxMonoidal (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).LaxMonoidal :=
  TauCeti.SheafOfModules.pushforwardLaxMonoidal (moduleOpenRestrictionRingHom f)

attribute [local instance] moduleOpenRestrictionLaxMonoidal

theorem moduleOpenRestrictionLaxTensor_isIso (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    IsIso (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N) := by
  have := moduleOpenRestrictionRingHom_isIso f
  exact moduleSheafPushforward_tensor_isIso_of_coefficientIso
    (R := Y.sheaf) (S := X.sheaf) f.opensFunctor (moduleOpenRestrictionRingHom f) M N

theorem moduleOpenRestrictionLaxUnit_isIso (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (Functor.LaxMonoidal.ε (Scheme.Modules.restrictFunctor f)) := by
  have := moduleOpenRestrictionRingHom_isIso f
  exact moduleSheafPushforward_unit_isIso_of_coefficientIso
    (R := Y.sheaf) (S := X.sheaf) f.opensFunctor (moduleOpenRestrictionRingHom f)

noncomputable def moduleOpenRestrictionTensorIso (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    M.restrict f ⊗ N.restrict f ≅ (M ⊗ N).restrict f := by
  let : IsIso (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N) :=
    moduleOpenRestrictionLaxTensor_isIso f M N
  exact asIso (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N)

theorem moduleOpenRestrictionTensorIso_hom (f : X ⟶ Y) [IsOpenImmersion f]
    (M N : Y.Modules) :
    (moduleOpenRestrictionTensorIso f M N).hom =
      Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N := rfl

@[instance_reducible]
noncomputable def moduleOpenRestrictionMonoidal (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).Monoidal := by
  let : IsIso (Functor.LaxMonoidal.ε (Scheme.Modules.restrictFunctor f)) :=
    moduleOpenRestrictionLaxUnit_isIso f
  let : ∀ M N, IsIso (Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N) :=
    moduleOpenRestrictionLaxTensor_isIso f
  exact Functor.Monoidal.ofLaxMonoidal (Scheme.Modules.restrictFunctor f)

universe v

theorem adjunction_isMonoidal_of_monoidal_unit
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {B : Type u} [Category.{v} B] [MonoidalCategory B]
    {F : C ⥤ B} {G : B ⥤ C} (a : F ⊣ G) [F.Monoidal] [G.LaxMonoidal]
    [NatTrans.IsMonoidal a.unit] : a.IsMonoidal := by
  constructor
  · have h := NatTrans.IsMonoidal.unit (τ := a.unit)
    simp only [Functor.LaxMonoidal.id_ε, Functor.LaxMonoidal.comp_ε,
      Category.id_comp] at h
    rw [h, Category.assoc, ← Functor.map_comp, Functor.Monoidal.ε_η,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · intro X Y
    have h := NatTrans.IsMonoidal.tensor (τ := a.unit) (G.obj X) (G.obj Y)
    simp only [Functor.LaxMonoidal.id_μ, Functor.LaxMonoidal.comp_μ,
      Functor.comp_obj, Category.id_comp] at h
    rw [h, Functor.map_comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Functor.LaxMonoidal.μ_natural,
      tensorHom_comp_tensorHom_assoc, a.right_triangle_components,
      a.right_triangle_components, id_tensorHom_id (G.obj X) (G.obj Y)]
    simpa only [CategoryTheory.Functor.id_obj] using
      (Category.id_comp (Functor.LaxMonoidal.μ G X Y)).symm

end MixedFujita

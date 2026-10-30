/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePushforwardTensorComparisons

/-!
The actual restriction/pushforward adjunction for a scheme open immersion
is compatible with the canonical lax restriction structure. Its unit is
proved monoidal on actual sections and pure tensors. Adjunction uniqueness
then identifies the earlier induced oplax unit and tensor maps with the
inverses of the canonical lax maps. Both comparisons are therefore actual
isomorphisms, with both inverse identities proved. No global Cartier
pullback tensor gluing or all-graded representation is asserted here.
-/

@[expose] public section
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}
attribute [local instance] moduleOpenRestrictionLaxMonoidal

set_option maxHeartbeats 600000 in
theorem moduleOpenRestrictionAdjunctionUnit_isMonoidal (f : X ⟶ Y) [IsOpenImmersion f] :
    NatTrans.IsMonoidal (Scheme.Modules.restrictAdjunction f).unit := by
  constructor
  · simp only [Functor.LaxMonoidal.id_ε, Functor.LaxMonoidal.comp_ε, Category.id_comp]
    have he : Functor.LaxMonoidal.ε (Scheme.Modules.restrictFunctor f) =
        SheafOfModules.unitToPushforwardObjUnit (moduleOpenRestrictionRingHom f) :=
      TauCeti.SheafOfModules.pushforward_ε (R := Y.sheaf) (S := X.sheaf)
        (moduleOpenRestrictionRingHom f)
    rw [Scheme.Modules.pushforward_ε, he]
    ext U r
    exact congr($(f.app_appIso_inv U).hom r).symm
  · intro M N
    simp only [Functor.LaxMonoidal.id_μ, Functor.LaxMonoidal.comp_μ,
      Functor.comp_obj, Category.id_comp]
    apply TauCeti.SheafOfModules.tensor_hom_ext
    simp only [Functor.map_comp,
      ← Functor.LaxMonoidal.μ_natural_assoc]
    erw [TauCeti.SheafOfModules.forget_μ_comp_map_pushforward_μ_assoc
        (R := X.sheaf) (S := Y.sheaf) f.toRingCatSheafHom (M.restrict f) (N.restrict f),
      TauCeti.SheafOfModules.forget_map_pushforward_map
        (R := X.sheaf) (S := Y.sheaf) f.toRingCatSheafHom]
    simp only [Category.assoc]
    rw [← Functor.map_comp]
    erw [TauCeti.SheafOfModules.forget_μ_comp_map_pushforward_μ
      (R := Y.sheaf) (S := X.sheaf) (moduleOpenRestrictionRingHom f) M N]
    simp only [Functor.map_comp]
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorHom_app,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    let g := (homOfLE (f.image_preimage_le U.unop)).op
    let m' : (M.restrict f).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) := M.val.map g m
    let n' : (N.restrict f).val.obj (Opposite.op (f ⁻¹ᵁ U.unop)) := N.val.map g n
    erw [TauCeti.SheafOfModules.presheafPushforward_μ_app_tmul
      (R := X.sheaf) (S := Y.sheaf) f.toRingCatSheafHom
        (M.restrict f).val (N.restrict f).val U m' n']
    change (M ⊗ N).val.map g
        ((Functor.LaxMonoidal.μ (SheafOfModules.forget Y.ringCatSheaf) M N).app U
          (m ⊗ₜ[Y.presheaf.obj U] n)) =
      (Functor.LaxMonoidal.μ (SheafOfModules.forget Y.ringCatSheaf) M N).app
        (Opposite.op (f ''ᵁ (f ⁻¹ᵁ U.unop)))
          ((Functor.LaxMonoidal.μ
            (TauCeti.SheafOfModules.presheafPushforward
              (F := f.opensFunctor) (R := Y.sheaf) (S := X.sheaf)
                (moduleOpenRestrictionRingHom f))
              M.val N.val).app (Opposite.op (f ⁻¹ᵁ U.unop))
                (m' ⊗ₜ[X.presheaf.obj (Opposite.op (f ⁻¹ᵁ U.unop))] n'))
    erw [TauCeti.SheafOfModules.presheafPushforward_μ_app_tmul
      (R := Y.sheaf) (S := X.sheaf) (moduleOpenRestrictionRingHom f)
        M.val N.val (Opposite.op (f ⁻¹ᵁ U.unop)) m' n']
    exact (PresheafOfModules.naturality_apply
      (Functor.LaxMonoidal.μ (SheafOfModules.forget Y.ringCatSheaf) M N) g
        (m ⊗ₜ[Y.presheaf.obj U] n)).symm

universe v

theorem adjunctionInducedOplaxTensor_eq
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {B : Type u} [Category.{v} B] [MonoidalCategory B]
    {F : C ⥤ B} {G : B ⥤ C} (a : F ⊣ G) [F.OplaxMonoidal] [G.LaxMonoidal]
    [a.IsMonoidal] (M N : C) :
    a.leftAdjointOplaxMonoidal.δ M N = Functor.OplaxMonoidal.δ F M N := by
  apply (a.homEquiv (M ⊗ N) (F.obj M ⊗ F.obj N)).injective
  change (a.homEquiv (M ⊗ N) (F.obj M ⊗ F.obj N))
      ((a.homEquiv (M ⊗ N) (F.obj M ⊗ F.obj N)).symm
        ((a.unit.app M ⊗ₘ a.unit.app N) ≫ Functor.LaxMonoidal.μ G (F.obj M) (F.obj N))) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, a.unit_app_tensor_comp_map_δ]

theorem adjunctionInducedOplaxUnit_eq
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {B : Type u} [Category.{v} B] [MonoidalCategory B]
    {F : C ⥤ B} {G : B ⥤ C} (a : F ⊣ G) [F.OplaxMonoidal] [G.LaxMonoidal]
    [a.IsMonoidal] :
    a.leftAdjointOplaxMonoidal.η = Functor.OplaxMonoidal.η F := by
  apply (a.homEquiv (𝟙_ C) (𝟙_ B)).injective
  change (a.homEquiv (𝟙_ C) (𝟙_ B))
      ((a.homEquiv (𝟙_ C) (𝟙_ B)).symm (Functor.LaxMonoidal.ε G)) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, a.unit_app_unit_comp_map_η]

attribute [local instance] moduleOpenRestrictionMonoidal

theorem moduleOpenRestrictionAdjunction_canonical_isMonoidal
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).IsMonoidal := by
  have := moduleOpenRestrictionAdjunctionUnit_isMonoidal f
  exact adjunction_isMonoidal_of_monoidal_unit (Scheme.Modules.restrictAdjunction f)

attribute [local instance] moduleOpenRestrictionAdjunction_canonical_isMonoidal

theorem moduleOpenRestrictionInducedOplaxTensor_eq_inv
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (moduleRestrictOplaxMonoidal f).δ M N = (moduleOpenRestrictionTensorIso f M N).inv := by
  have h := adjunctionInducedOplaxTensor_eq (Scheme.Modules.restrictAdjunction f) M N
  exact h

theorem moduleOpenRestrictionInducedOplaxUnit_eq_inv
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (moduleRestrictOplaxMonoidal f).η =
      inv (Functor.LaxMonoidal.ε (Scheme.Modules.restrictFunctor f)) := by
  have h := adjunctionInducedOplaxUnit_eq (Scheme.Modules.restrictAdjunction f)
  exact h

theorem moduleOpenRestrictionInducedOplaxTensor_isIso
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    IsIso ((moduleRestrictOplaxMonoidal f).δ M N) := by
  rw [moduleOpenRestrictionInducedOplaxTensor_eq_inv]
  infer_instance

theorem moduleOpenRestrictionInducedOplaxUnit_isIso
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso ((moduleRestrictOplaxMonoidal f).η) := by
  rw [moduleOpenRestrictionInducedOplaxUnit_eq_inv]
  infer_instance

theorem moduleOpenRestrictionInducedOplaxTensor_comp_laxTensor
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (moduleRestrictOplaxMonoidal f).δ M N ≫
      Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N = 𝟙 _ := by
  rw [moduleOpenRestrictionInducedOplaxTensor_eq_inv,
    ← moduleOpenRestrictionTensorIso_hom]
  exact (moduleOpenRestrictionTensorIso f M N).inv_hom_id

theorem moduleOpenRestrictionLaxTensor_comp_inducedOplaxTensor
    (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.restrictFunctor f) M N ≫
      (moduleRestrictOplaxMonoidal f).δ M N = 𝟙 _ := by
  rw [moduleOpenRestrictionInducedOplaxTensor_eq_inv,
    ← moduleOpenRestrictionTensorIso_hom]
  exact (moduleOpenRestrictionTensorIso f M N).hom_inv_id

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleLocalPullbackCoefficients
public import TauCeti.CategoryTheory.Monoidal.Functor

/-!
The actual canonical oplax tensor map of module pullback is an isomorphism
when one source factor has an actual unit frame. Its coefficient in the
pulled frames agrees with the coefficient of the pulled tensor frame.
The local comparison uses actual scheme preimage opens and the constructed
pullback/restriction isomorphisms. Its source is the pullback of the tensor
of the restricted factors. Identifying this source with the restriction
of the global tensor pullback, gluing to a global tensor comparison for
line bundles, and compatible all-graded Cartier representations remain
separate steps; none is assumed proved by this local theorem.
-/

@[expose] public section
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {B : Type u} [Category.{v} B] [MonoidalCategory B]

theorem oplaxTensorComparison_isIso_of_left_frame
    (F : C ⥤ B) [F.OplaxMonoidal] [IsIso (Functor.OplaxMonoidal.η F)]
    (M N : C) (e : M ≅ 𝟙_ C) :
    IsIso (Functor.OplaxMonoidal.δ F M N) := by
  have := Functor.OplaxMonoidal.isIso_δ_tensorUnit_left F N
  have h := Functor.OplaxMonoidal.δ_natural_left F e.hom N
  have : IsIso (Functor.OplaxMonoidal.δ F M N ≫ F.map e.hom ▷ F.obj N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (Functor.OplaxMonoidal.δ F M N)
    (F.map e.hom ▷ F.obj N)

theorem oplaxTensorComparison_isIso_of_right_frame
    (F : C ⥤ B) [F.OplaxMonoidal] [IsIso (Functor.OplaxMonoidal.η F)]
    (M N : C) (a : N ≅ 𝟙_ C) :
    IsIso (Functor.OplaxMonoidal.δ F M N) := by
  have := Functor.OplaxMonoidal.isIso_δ_tensorUnit_right F M
  have h := Functor.OplaxMonoidal.δ_natural_right F M a.hom
  have : IsIso (Functor.OplaxMonoidal.δ F M N ≫ F.obj M ◁ F.map a.hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right (Functor.OplaxMonoidal.δ F M N)
    (F.obj M ◁ F.map a.hom)

theorem oplaxTensorComparison_comp_frames
    (F : C ⥤ B) [F.OplaxMonoidal] (M N : C) (e : M ≅ 𝟙_ C) (a : N ≅ 𝟙_ C) :
    Functor.OplaxMonoidal.δ F M N ≫
      ((F.map e.hom ≫ Functor.OplaxMonoidal.η F) ⊗ₘ
        (F.map a.hom ≫ Functor.OplaxMonoidal.η F)) ≫ (λ_ (𝟙_ B)).hom =
    F.map ((e.hom ⊗ₘ a.hom) ≫ (λ_ (𝟙_ C)).hom) ≫ Functor.OplaxMonoidal.η F := by
  have hη : Functor.OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C) ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (λ_ (𝟙_ B)).hom =
      F.map (λ_ (𝟙_ C)).hom ≫ Functor.OplaxMonoidal.η F := by
    rw [tensorHom_def]
    simp only [Category.assoc]
    rw [leftUnitor_naturality]
    exact Functor.OplaxMonoidal.left_unitality_hom_assoc F (𝟙_ C)
      (Functor.OplaxMonoidal.η F)
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_assoc, hη]
  simp only [Functor.map_comp, Category.assoc]

noncomputable def moduleTensorFrameIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    M ⊗ N ≅ SheafOfModules.unit X.ringCatSheaf :=
  tensorIso e a ≪≫ λ_ (𝟙_ X.Modules)

variable {X Y : Scheme.{u}}

theorem modulePullbackTensorComparison_isIso_of_frame (φ : Y ⟶ X) (M N : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) :=
  oplaxTensorComparison_isIso_of_left_frame (Scheme.Modules.pullback φ) M N e

theorem modulePullbackTensorComparison_isIso_of_right_frame
    (φ : Y ⟶ X) (M N : X.Modules)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) :=
  oplaxTensorComparison_isIso_of_right_frame (Scheme.Modules.pullback φ) M N a

noncomputable def modulePullbackTensorIsoOfFrame (φ : Y ⟶ X) (M N : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (Scheme.Modules.pullback φ).obj (M ⊗ N) ≅
      (Scheme.Modules.pullback φ).obj M ⊗ (Scheme.Modules.pullback φ).obj N := by
  let : IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) :=
    modulePullbackTensorComparison_isIso_of_frame φ M N e
  exact asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N)

theorem modulePullbackTensorIsoOfFrame_hom (φ : Y ⟶ X) (M N : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (modulePullbackTensorIsoOfFrame φ M N e).hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N := rfl

theorem modulePullbackTensorFrameIso_hom (φ : Y ⟶ X) (M N : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N ≫
      ((modulePullbackFrameIso φ e).hom ⊗ₘ (modulePullbackFrameIso φ a).hom) ≫
        (λ_ (𝟙_ Y.Modules)).hom =
    (modulePullbackFrameIso φ (moduleTensorFrameIso e a)).hom := by
  have h := oplaxTensorComparison_comp_frames (Scheme.Modules.pullback φ) M N e a
  simpa only [Scheme.Modules.pullback_η, modulePullbackFrameIso, moduleTensorFrameIso,
    Iso.trans_hom, Functor.mapIso_hom, tensorIso_hom] using h

theorem modulePullbackTensorIsoOfFrame_comp_frames (φ : Y ⟶ X) (M N : X.Modules)
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf)
    (a : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    modulePullbackTensorIsoOfFrame φ M N e ≪≫
      moduleTensorFrameIso (modulePullbackFrameIso φ e) (modulePullbackFrameIso φ a) =
    modulePullbackFrameIso φ (moduleTensorFrameIso e a) := by
  apply Iso.ext
  simpa only [Iso.trans_hom, modulePullbackTensorIsoOfFrame_hom, moduleTensorFrameIso,
    tensorIso_hom] using modulePullbackTensorFrameIso_hom φ M N e a

noncomputable def moduleLocalPullbackTensorIso (φ : Y ⟶ X) (U : X.Opens)
    (M N : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (Scheme.Modules.pullback (φ ∣_ U)).obj (M.restrict U.ι ⊗ N.restrict U.ι) ≅
      ((Scheme.Modules.pullback φ).obj M).restrict (φ ⁻¹ᵁ U).ι ⊗
        ((Scheme.Modules.pullback φ).obj N).restrict (φ ⁻¹ᵁ U).ι :=
  modulePullbackTensorIsoOfFrame (φ ∣_ U) (M.restrict U.ι) (N.restrict U.ι) e ≪≫
    tensorIso (modulePullbackRestrictionIso φ U M).symm
      (modulePullbackRestrictionIso φ U N).symm

theorem moduleLocalPullbackTensorIso_hom (φ : Y ⟶ X) (U : X.Opens) (M N : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (moduleLocalPullbackTensorIso φ U M N e).hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U)) (M.restrict U.ι) (N.restrict U.ι) ≫
        ((modulePullbackRestrictionIso φ U M).inv ⊗ₘ
          (modulePullbackRestrictionIso φ U N).inv) := rfl

theorem moduleLocalPullbackTensorIso_comp_frames (φ : Y ⟶ X) (U : X.Opens)
    (M N : X.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (a : N.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    moduleLocalPullbackTensorIso φ U M N e ≪≫
      moduleTensorFrameIso (moduleLocalPullbackFrameIso φ M U e)
        (moduleLocalPullbackFrameIso φ N U a) =
    modulePullbackFrameIso (φ ∣_ U) (moduleTensorFrameIso e a) := by
  apply Iso.ext
  simp only [Iso.trans_hom, moduleLocalPullbackTensorIso_hom, moduleTensorFrameIso,
    tensorIso_hom, moduleLocalPullbackFrameIso]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id_assoc]
  exact modulePullbackTensorFrameIso_hom (φ ∣_ U) (M.restrict U.ι) (N.restrict U.ι) e a


open TauCeti.AlgebraicGeometry.Scheme

theorem cartierPullbackTensorComparison_isIso_on_equation_open [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) (N : X.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
      (D.sheaf.restrict U.ι) (N.restrict U.ι)) :=
  modulePullbackTensorComparison_isIso_of_frame (φ ∣_ U) _ _
    (cartierOpenRestrictFrameIso D U f hf)

theorem cartierPullbackTensorComparison_exists_point_local_iso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (y : Y) (N : X.Modules) :
    ∃ U : X.Opens, φ y ∈ U ∧
      IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
        (D.sheaf.restrict U.ι) (N.restrict U.ι)) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  exact ⟨U, hy, cartierPullbackTensorComparison_isIso_on_equation_open D φ U f hU N⟩

end MixedFujita

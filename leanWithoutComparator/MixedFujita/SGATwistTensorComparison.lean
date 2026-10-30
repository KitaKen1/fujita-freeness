/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Cohomology.Twist
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-! The cocycle-defined SGA twist is canonically isomorphic to the actual sheafified tensor product of the same integer line-bundle power with an arbitrary module. Multiplication on sections is locally bijective in the original unit frames; sheafification therefore gives the isomorphism. No coherence, noetherianity or positivity is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules) (n : ℤ)

noncomputable def sgaTwistTensorSection (V : X.Opens)
    (s : L.sectionsAddSubgroup n V) (t : Γ(M, V)) : L.twistAddSubgroup M n V := by
  refine ⟨fun i => s.1 i • M.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
  intro i j
  simp only [Scheme.Modules.map_smul, s.2 i j, mul_smul,
    TopCat.Presheaf.map_map_apply]

noncomputable def sgaTwistTensorBilinear (V : X.Opens) :
    L.sectionsAddSubgroup n V →ₗ[Γ(X, V)] Γ(M, V) →ₗ[Γ(X, V)]
      L.twistAddSubgroup M n V :=
  LinearMap.mk₂ Γ(X, V) (sgaTwistTensorSection L M n V)
    (fun s s' t => by ext i; exact add_smul _ _ _)
    (fun r s t => by ext i; exact mul_smul _ _ _)
    (fun s t t' => by ext i; simp [sgaTwistTensorSection, smul_add])
    (fun r s t => by
      ext i
      change s.1 i • M.presheaf.map (homOfLE inf_le_left).op (r • t) = _
      rw [Scheme.Modules.map_smul]
      exact smul_comm _ _ _)

noncomputable def sgaTwistTensorLinear (V : X.Opens) :
    TensorProduct Γ(X, V) Γ(L.toModules n, V) Γ(M, V) →ₗ[Γ(X, V)]
      Γ(L.twist M n, V) :=
  TensorProduct.lift (sgaTwistTensorBilinear L M n V)

theorem sgaTwistTensorSection_restrict {V W : X.Opens} (h : W ≤ V)
    (s : L.sectionsAddSubgroup n V) (t : Γ(M, V)) :
    sgaTwistTensorSection L M n W (L.resHom n h s)
        (M.presheaf.map (homOfLE h).op t) =
      L.twistResHom M n h (sgaTwistTensorSection L M n V s t) := by
  ext i
  simp only [sgaTwistTensorSection, Scheme.LineBundle.resHom_apply,
    Scheme.LineBundle.twistResHom_apply, Scheme.Modules.map_smul,
    TopCat.Presheaf.map_map_apply]

noncomputable def sgaTwistTensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj)
      (L.toModules n).val M.val ⟶ (L.twist M n).val where
  app V := by
    letI : CommRing (X.ringCatSheaf.obj.obj V) :=
      inferInstanceAs (CommRing Γ(X, V.unop))
    letI : Module (X.sheaf.obj.obj V) ((L.twistPresheaf M n).obj V) :=
      inferInstanceAs (Module Γ(X, V.unop) (L.twistAddSubgroup M n V.unop))
    exact ModuleCat.ofHom (sgaTwistTensorLinear L M n V.unop)
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    change sgaTwistTensorSection L M n W.unop (L.resHom n f.unop.le s)
        (M.presheaf.map f t) =
      L.twistResHom M n f.unop.le (sgaTwistTensorSection L M n V.unop s t)
    exact sgaTwistTensorSection_restrict L M n f.unop.le s t

theorem sgaTwistTensorSection_toModule (k : L.ι) {V : X.Opens} (hV : V ≤ L.U k)
    (s : L.sectionsAddSubgroup n V) (t : Γ(M, V)) :
    L.twistToModule k hV (sgaTwistTensorSection L M n V s t) =
      L.toUnit k hV s • t := by
  rw [Scheme.LineBundle.twistToModule_apply, Scheme.LineBundle.toUnit_apply]
  change M.presheaf.map _ (s.1 k • M.presheaf.map _ t) = _
  rw [Scheme.Modules.map_smul, TopCat.Presheaf.map_map_apply,
    CohomologyAux.modules_map_self]

theorem sgaTwistTensorLinear_bijective_on_frame (k : L.ι) {V : X.Opens}
    (hV : V ≤ L.U k) : Function.Bijective (sgaTwistTensorLinear L M n V) := by
  let e : TensorProduct Γ(X, V) Γ(L.toModules n, V) Γ(M, V) ≃ₗ[Γ(X, V)]
      Γ(L.twist M n, V) :=
    (TensorProduct.congr (L.unitEquiv (n := n) k hV) (LinearEquiv.refl _ _)).trans
      ((TensorProduct.lid Γ(X, V) Γ(M, V)).trans
        (L.twistEquiv (M := M) (n := n) k hV).symm)
  have h : sgaTwistTensorLinear L M n V = e.toLinearMap := by
    apply TensorProduct.ext'
    intro s t
    apply (L.twistEquiv (M := M) (n := n) k hV).injective
    change L.twistToModule k hV (sgaTwistTensorSection L M n V s t) = _
    rw [sgaTwistTensorSection_toModule]
    exact (LinearEquiv.apply_symm_apply (L.twistEquiv (M := M) (n := n) k hV) _).symm
  rw [h]
  exact e.bijective

theorem sgaTwistTensorPresheafHom_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (sgaTwistTensorPresheafHom L M n)) where
  imageSieve_mem {V} s x hx := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (L.iSup_eq_top ▸ Opens.mem_top x)
    let W := V ⊓ L.U k
    obtain ⟨t, ht⟩ := (sgaTwistTensorLinear_bijective_on_frame L M n k
      (V := W) inf_le_right).surjective
        ((L.twist M n).presheaf.map (homOfLE (show W ≤ V from inf_le_left)).op s)
    exact ⟨W, homOfLE inf_le_left, ⟨t, ht⟩, ⟨hx, hk⟩⟩

theorem sgaTwistTensorPresheafHom_isLocallyInjective :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (sgaTwistTensorPresheafHom L M n)) where
  equalizerSieve_mem {V} s t h x hx := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (L.iSup_eq_top ▸ Opens.mem_top x)
    let W := V.unop ⊓ L.U k
    refine ⟨W, homOfLE inf_le_left,
      (sgaTwistTensorLinear_bijective_on_frame L M n k
        (V := W) inf_le_right).injective ?_, ⟨hx, hk⟩⟩
    exact (PresheafOfModules.naturality_apply (sgaTwistTensorPresheafHom L M n)
      (homOfLE inf_le_left).op s).trans
        ((congrArg ((L.twist M n).val.map (homOfLE inf_le_left).op) h).trans
          (PresheafOfModules.naturality_apply (sgaTwistTensorPresheafHom L M n)
            (homOfLE inf_le_left).op t).symm)

theorem sgaTwistTensorPresheafHom_sheafification_isIso :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (sgaTwistTensorPresheafHom L M n)) := by
  letI := sgaTwistTensorPresheafHom_isLocallySurjective L M n
  letI := sgaTwistTensorPresheafHom_isLocallyInjective L M n
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (sgaTwistTensorPresheafHom L M n)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

noncomputable def sgaTwistTensorIso : L.toModules n ⊗ M ≅ L.twist M n := by
  letI := sgaTwistTensorPresheafHom_sheafification_isIso L M n
  exact (L.toModules n).tensorUnderlyingIso M ≪≫
    asIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (sgaTwistTensorPresheafHom L M n)) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (L.twist M n)

noncomputable def sgaTwistUnitIso :
    L.twist (SheafOfModules.unit X.ringCatSheaf) n ≅ L.toModules n :=
  Iso.refl _

end MixedFujita

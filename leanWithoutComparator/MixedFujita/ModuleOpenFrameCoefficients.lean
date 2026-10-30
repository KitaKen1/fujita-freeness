/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierLocalPullbackFrame

/-!
Evaluate actual module frames on opens as linear equivalences over the
actual regular-function ring. The transition between any two such frames
is multiplication by an actual unit, constructed from the linear
automorphism and its inverse. Transporting an actual frame across an
actual module isomorphism therefore gives a unit comparison with the
intrinsic Cartier coefficient, without supplying that comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : Scheme.{u}}

noncomputable def moduleRestrictFrameOverIso (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)

noncomputable def moduleOverFrameCoefficient (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : X.Opens) (hWU : W ≤ U) : Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) :=
  ((PresheafOfModules.evaluation _ (op (Over.mk (homOfLE hWU)))).mapIso
    ((SheafOfModules.forget _).mapIso e)).toLinearEquiv

theorem moduleOverFrameCoefficient_apply (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    moduleOverFrameCoefficient M U e W hWU s =
      e.hom.val.app (op (Over.mk (homOfLE hWU))) s := rfl

theorem moduleOverFrameCoefficient_restrict (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    {W V : X.Opens} (hWU : W ≤ U) (i : V ⟶ W) (s : Γ(M, W)) :
    moduleOverFrameCoefficient M U e V (i.le.trans hWU) (M.presheaf.map i.op s) =
      X.presheaf.map i.op (moduleOverFrameCoefficient M U e W hWU s) :=
  PresheafOfModules.naturality_apply e.hom.val
    (Over.homMk i : Over.mk (homOfLE (i.le.trans hWU)) ⟶ Over.mk (homOfLE hWU)).op s

noncomputable def linearSelfFrameUnit {R : Type u} [CommRing R] (a : R ≃ₗ[R] R) : Rˣ where
  val := a 1
  inv := a.symm 1
  val_inv := by
    have h := a.map_smul (a.symm 1) (1 : R)
    simpa [smul_eq_mul, mul_comm] using h.symm
  inv_val := by
    have h := a.symm.map_smul (a 1) (1 : R)
    simpa [smul_eq_mul, mul_comm] using h.symm

theorem linearSelfFrameUnit_mul {R : Type u} [CommRing R] (a : R ≃ₗ[R] R) (r : R) :
    (linearSelfFrameUnit a : R) * r = a r := by
  simpa [linearSelfFrameUnit, smul_eq_mul, mul_comm] using (a.map_smul r (1 : R)).symm

theorem moduleOverFrameCoefficient_change_frame (M : X.Modules) (U : X.Opens)
    (e d : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : X.Opens) (hWU : W ≤ U) :
    ∃ v : Γ(X, W)ˣ, ∀ s : Γ(M, W),
      moduleOverFrameCoefficient M U e W hWU s =
        (v : Γ(X, W)) * moduleOverFrameCoefficient M U d W hWU s := by
  let a := (moduleOverFrameCoefficient M U d W hWU).symm.trans
    (moduleOverFrameCoefficient M U e W hWU)
  refine ⟨linearSelfFrameUnit a, fun s => ?_⟩
  rw [linearSelfFrameUnit_mul]
  exact (moduleOverFrameCoefficient M U e W hWU).congr_arg
    ((moduleOverFrameCoefficient M U d W hWU).symm_apply_apply s).symm

theorem moduleRestrictFrameOverIso_roundTrip (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    moduleRestrictFrameOverIso M U
      (((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
        (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
          U.sheafOfModulesEquivOverUnit X.ringCatSheaf) = e := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.map_injective
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimage _) = _
  rw [Functor.FullyFaithful.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact (congrArg ((Scheme.Modules.overEquiv U).functor.map e.hom ≫ ·)
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom_inv_id).trans (Category.comp_id _)

noncomputable def moduleOverFrameRestrictIso (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) : M.over V ≅ SheafOfModules.unit (X.ringCatSheaf.over V) :=
  ((SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE hVU)).app M).symm ≪≫
    (SheafOfModules.overMap X.ringCatSheaf (homOfLE hVU)).mapIso e ≪≫
      SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) (homOfLE hVU)

theorem moduleOverFrameRestrictIso_coefficient (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (hVU : V ≤ U) (W : X.Opens) (hWV : W ≤ V) (s : Γ(M, W)) :
    moduleOverFrameCoefficient M V (moduleOverFrameRestrictIso M U e V hVU) W hWV s =
      moduleOverFrameCoefficient M U e W (hWV.trans hVU) s := rfl

noncomputable def moduleOverFrameViaIso {M N : X.Modules} (U : X.Opens)
    (a : M ≅ N) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso a.symm ≪≫ e

theorem moduleOverFrameViaIso_coefficient {M N : X.Modules} (U : X.Opens)
    (a : M ≅ N) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : X.Opens) (hWU : W ≤ U) (s : Γ(M, W)) :
    moduleOverFrameCoefficient N U (moduleOverFrameViaIso U a e) W hWU
      (Scheme.Modules.Hom.app a.hom W s) = moduleOverFrameCoefficient M U e W hWU s := by
  change e.hom.val.app (op (Over.mk (homOfLE hWU)))
    (Scheme.Modules.Hom.app a.inv W (Scheme.Modules.Hom.app a.hom W s)) = _
  have h : Scheme.Modules.Hom.app a.inv W (Scheme.Modules.Hom.app a.hom W s) = s :=
    ConcreteCategory.congr_hom (congrArg (fun b => Scheme.Modules.Hom.app b W) a.hom_inv_id) s
  rw [h]
  rfl

end MixedFujita

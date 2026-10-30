/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafModuleFunctor
public import MixedFujita.ModulePullbackRestriction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Construct the canonical global map from the pullback of an actual ideal
module to the actual comap ideal module, using the ideal-sheaf Galois
connection and preservation of kernels by pushforward. No quasi-coherence,
dominance, integrality or flatness input is needed for this construction. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B B' : Scheme.{u}}

theorem idealSheaf_comap_unit_quotient_comp_zero (I : B.IdealSheafData) (β : B' ⟶ B) :
    (idealSheafDataModuleInclusion I ≫ schemeUnitToPushforwardUnit β) ≫
      (Scheme.Modules.pushforward β).map
        (schemeUnitToPushforwardUnit (I.comap β).subschemeι) = 0 := by
  apply (cancel_mono ((Scheme.Modules.pushforwardComp (I.comap β).subschemeι β).hom.app
    (SheafOfModules.unit (I.comap β).subscheme.ringCatSheaf))).mp
  rw [zero_comp]
  apply moduleHom_ext_affine
  intro U
  ext s
  let a := Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1 s
  have ha : a ∈ I.ideal U :=
    (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image I U) a).mp ⟨s, rfl⟩
  have hb : a ∈ (((I.comap β).subschemeι ≫ β).ker).ideal U :=
    (Scheme.IdealSheafData.le_map_comap I β) U ha
  have hz := RingHom.mem_ker.mp (((I.comap β).subschemeι ≫ β).ideal_ker_le U hb)
  change ((I.comap β).subschemeι ≫ β).app U.1 a = 0
  exact hz

/-- The canonical adjoint map into the pushforward of the actual comap ideal
module. The kernel lift exists globally, before choosing any affine charts. -/
noncomputable def idealSheafComapModuleAdjoint (I : B.IdealSheafData) (β : B' ⟶ B) :
    idealSheafDataModule I ⟶
      (Scheme.Modules.pushforward β).obj (idealSheafDataModule (I.comap β)) :=
  kernel.lift ((Scheme.Modules.pushforward β).map
      (schemeUnitToPushforwardUnit (I.comap β).subschemeι))
      (idealSheafDataModuleInclusion I ≫ schemeUnitToPushforwardUnit β)
      (idealSheaf_comap_unit_quotient_comp_zero I β) ≫
    (PreservesKernel.iso (Scheme.Modules.pushforward β)
      (schemeUnitToPushforwardUnit (I.comap β).subschemeι)).inv

@[reassoc (attr := simp)]
theorem idealSheafComapModuleAdjoint_inclusion (I : B.IdealSheafData) (β : B' ⟶ B) :
    idealSheafComapModuleAdjoint I β ≫
      (Scheme.Modules.pushforward β).map (idealSheafDataModuleInclusion (I.comap β)) =
        idealSheafDataModuleInclusion I ≫ schemeUnitToPushforwardUnit β := by
  unfold idealSheafComapModuleAdjoint idealSheafDataModuleInclusion
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- The genuine global ideal-comap comparison, with the canonical kernel
modules on both sides. Its epimorphism and factorization properties require
additional verification; they are not built into this definition. -/
noncomputable def idealSheafComapModuleMap (I : B.IdealSheafData) (β : B' ⟶ B) :
    (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      idealSheafDataModule (I.comap β) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction β).homEquiv _ _).symm
    (idealSheafComapModuleAdjoint I β)

theorem idealSheafComapModuleMap_adjoint (I : B.IdealSheafData) (β : B' ⟶ B) :
    (Scheme.Modules.pullbackPushforwardAdjunction β).unit.app (idealSheafDataModule I) ≫
      (Scheme.Modules.pushforward β).map (idealSheafComapModuleMap I β) =
        idealSheafComapModuleAdjoint I β :=
  ((Scheme.Modules.pullbackPushforwardAdjunction β).homEquiv _ _).apply_symm_apply _

@[reassoc]
theorem idealSheafComapModuleMap_inclusion (I : B.IdealSheafData) (β : B' ⟶ B) :
    idealSheafComapModuleMap I β ≫ idealSheafDataModuleInclusion (I.comap β) =
      modulePullbackCoefficientHom β (idealSheafDataModuleInclusion I) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction β).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [idealSheafComapModuleMap, Equiv.apply_symm_apply]
  rw [idealSheafComapModuleAdjoint_inclusion]
  exact (modulePullbackCoefficientHom_adjoint β (idealSheafDataModuleInclusion I)).symm

end MixedFujita

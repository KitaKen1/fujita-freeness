/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalRoundupDirectImageCoherence
public import MixedFujita.QuasicoherentImageIdealSheaf
public import MixedFujita.CartierProjectionFormula
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-! An actual monomorphism into a Cartier sheaf gives an actual image ideal
after tensoring by the inverse Cartier sheaf. The source is identified with
the Cartier twist of the actual ideal module. Neither the source nor the
ideal module is assumed invertible or reflexive. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {B : Scheme.{u}} [IsIntegral B] {M : B.Modules}

/-- Tensor an actual Cartier-target map by O(-C) and cancel the Cartier sum. -/
noncomputable def cartierTargetImageStructureHom (C : CartierDivisor B)
    (α : M ⟶ C.sheaf) : (-C).sheaf ⊗ M ⟶ SheafOfModules.unit B.ringCatSheaf :=
  (cartierTwistFunctor (-C)).map α ≫
    (cartierTensorSheafIso (-C) C ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (neg_add_cancel C)) ≪≫ cartierZeroSheafIso B).hom

theorem cartierTargetImageStructureHom_mono (C : CartierDivisor B)
    (α : M ⟶ C.sheaf) [Mono α] : Mono (cartierTargetImageStructureHom C α) := by
  dsimp only [cartierTargetImageStructureHom]
  infer_instance

/-- The actual affine image ideals glue by quasicoherent denominator clearing. -/
noncomputable def cartierTargetImageIdealSheaf [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) : B.IdealSheafData := by
  letI := (-C).isInvertible_sheaf
  exact quasicoherentModuleImageIdealSheaf ((-C).sheaf ⊗ M) (cartierTargetImageStructureHom C α)

theorem cartierTargetImageIdealSheaf_affine_image [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) (U : B.affineOpens) :
    Set.range (Scheme.Modules.Hom.app (cartierTargetImageStructureHom C α) U.1) =
      ((cartierTargetImageIdealSheaf C α).ideal U : Set Γ(B, U.1)) := by
  letI := (-C).isInvertible_sheaf
  exact quasicoherentModuleImageIdealSheaf_affine_image _ U

/-- The inverse Cartier twist of the source is the actual ideal module. -/
noncomputable def cartierTargetImageIdealModuleIso [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) [Mono α] :
    (-C).sheaf ⊗ M ≅ idealSheafDataModule (cartierTargetImageIdealSheaf C α) := by
  letI := (-C).isInvertible_sheaf
  letI := cartierTargetImageStructureHom_mono C α
  exact quasicoherentImageIdealModuleIso (cartierTargetImageStructureHom C α)

@[reassoc (attr := simp)]
theorem cartierTargetImageIdealModuleIso_hom_inclusion [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) [Mono α] :
    (cartierTargetImageIdealModuleIso C α).hom ≫
      idealSheafDataModuleInclusion (cartierTargetImageIdealSheaf C α) =
      cartierTargetImageStructureHom C α := by
  letI := (-C).isInvertible_sheaf
  letI := cartierTargetImageStructureHom_mono C α
  exact quasicoherentImageIdealModuleIso_hom_inclusion (cartierTargetImageStructureHom C α)

/-- Recover the source itself as O(C) tensored with its actual image ideal. -/
noncomputable def cartierTargetImageSourceIso [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) [Mono α] :
    M ≅ C.sheaf ⊗ idealSheafDataModule (cartierTargetImageIdealSheaf C α) :=
  ((cartierTwistCancelIso (-C) C (add_neg_cancel C)).app M).symm ≪≫
    (cartierTwistFunctor C).mapIso (cartierTargetImageIdealModuleIso C α)

theorem cartierTargetImageIdealModule_isCoherent [IsLocallyNoetherian B] [M.IsQuasicoherent]
    (C : CartierDivisor B) (α : M ⟶ C.sheaf) [Mono α] :
    (idealSheafDataModule (cartierTargetImageIdealSheaf C α)).IsCoherent := by
  letI := (-C).isInvertible_sheaf
  letI := cartierTargetImageStructureHom_mono C α
  letI := invertible_module_sheaf_isFiniteType (SheafOfModules.unit B.ringCatSheaf)
  have hc := quasicoherent_module_isCoherent_of_mono (cartierTargetImageStructureHom C α)
  letI := hc.isFiniteType
  let e := cartierTargetImageIdealModuleIso C α
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso e, Scheme.Modules.isFiniteType_of_iso e⟩

end MixedFujita

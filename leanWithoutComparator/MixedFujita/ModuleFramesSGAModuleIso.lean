/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleFramesToSGALineBundle
public import MixedFujita.SGALineBundleCartierRepresentation
public import MixedFujita.ModuleOpenCoverIsomorphisms
public import MixedFujita.ModuleAffineExactness

/-!
The SGA module sheaf of the line bundle constructed from actual module unit frames is
isomorphic to the original module sheaf. Construct the comparison on every open using frame
coefficients, prove naturality and linearity, and detect its isomorphism on the actual unit
frame cover. This is an isomorphism of sheaves of modules, not just of global section sets.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
  (hU : ⨆ i, U i = ⊤)

/-- The comparison on an arbitrary open: take the actual frame coefficients on its overlaps
with the frame cover. -/
noncomputable def moduleFramesSGAModuleSection (W : X.Opens) (s : Γ(M, W)) :
    Γ((moduleFramesSGALineBundle M U e hU).toModules 1, W) := by
  change (moduleFramesSGALineBundle M U e hU).sectionsAddSubgroup 1 W
  refine ⟨fun i => moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
    (M.presheaf.map (homOfLE inf_le_left).op s), ?_⟩
  intro i j
  change ι at i j
  change X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
      W ⊓ (U i ⊓ U j) ≤ W ⊓ U i)).op
      (moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
        (M.presheaf.map (homOfLE inf_le_left).op s)) =
    X.presheaf.map (homOfLE (inf_le_right : W ⊓ (U i ⊓ U j) ≤ U i ⊓ U j)).op
      ((moduleFrameTransitionUnit M U e i j (U i ⊓ U j) inf_le_left inf_le_right ^
        (1 : ℤ) : Γ(X, U i ⊓ U j)ˣ) : Γ(X, U i ⊓ U j)) *
      X.presheaf.map (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        W ⊓ (U i ⊓ U j) ≤ W ⊓ U j)).op
        (moduleOverFrameCoefficient M (U j) (e j) (W ⊓ U j) inf_le_right
          (M.presheaf.map (homOfLE inf_le_left).op s))
  rw [zpow_one,
    ← moduleOverFrameCoefficient_restrict M (U i) (e i) inf_le_right
      (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_left))),
    ← moduleOverFrameCoefficient_restrict M (U j) (e j) inf_le_right
      (homOfLE (le_inf inf_le_left (inf_le_right.trans inf_le_right))),
    moduleFrameTransitionUnit_restrict, moduleFrameTransitionUnit_mul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

noncomputable def moduleFramesSGAModuleLinear (W : X.Opens) :
    Γ(M, W) →ₗ[Γ(X, W)] Γ((moduleFramesSGALineBundle M U e hU).toModules 1, W) where
  toFun := moduleFramesSGAModuleSection M U e hU W
  map_add' s t := by
    apply Subtype.ext
    funext i
    change ι at i
    change moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
      (M.presheaf.map (homOfLE inf_le_left).op (s + t)) = _
    rw [map_add, map_add]
    rfl
  map_smul' r s := by
    dsimp only [moduleFramesSGALineBundle]
    apply Subtype.ext
    funext i
    change ι at i
    change moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
      (M.presheaf.map (homOfLE inf_le_left).op (r • s)) =
      X.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r *
        moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
          (M.presheaf.map (homOfLE inf_le_left).op s)
    have hh : M.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op (r • s) =
        X.presheaf.map (homOfLE inf_le_left).op r •
          M.presheaf.map (homOfLE inf_le_left).op s :=
      M.val.map_smul (homOfLE inf_le_left).op r s
    rw [hh, LinearEquiv.map_smul, smul_eq_mul]

theorem moduleFramesSGAModuleSection_restrict {W V : X.Opens} (hVW : V ≤ W) (s : Γ(M, W)) :
    moduleFramesSGAModuleSection M U e hU V (M.presheaf.map (homOfLE hVW).op s) =
      ((moduleFramesSGALineBundle M U e hU).toModules 1).presheaf.map (homOfLE hVW).op
        (moduleFramesSGAModuleSection M U e hU W s) := by
  apply Subtype.ext
  funext i
  change moduleOverFrameCoefficient M (U i) (e i) (V ⊓ U i) inf_le_right
    (M.presheaf.map (homOfLE inf_le_left).op (M.presheaf.map (homOfLE hVW).op s)) =
    X.presheaf.map (homOfLE (inf_le_inf_right (U i) hVW)).op
      (moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
        (M.presheaf.map (homOfLE inf_le_left).op s))
  rw [← moduleOverFrameCoefficient_restrict M (U i) (e i) inf_le_right
    (homOfLE (inf_le_inf_right (U i) hVW))]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The actual comparison morphism of module sheaves, with proved restriction naturality. -/
noncomputable def moduleFramesToSGAModuleHom :
    M ⟶ (moduleFramesSGALineBundle M U e hU).toModules 1 where
  val :=
    { app := fun W => ModuleCat.ofHom (moduleFramesSGAModuleLinear M U e hU W.unop)
      naturality := by
        intro W V f
        ext s
        exact moduleFramesSGAModuleSection_restrict M U e hU f.unop.le s }

/-- In a unit frame the sheaf comparison has exactly the original frame coefficient. -/
theorem moduleFramesSGAModuleSection_toUnit (i : ι) (W : X.Opens) (hWi : W ≤ U i)
    (s : Γ(M, W)) :
    (moduleFramesSGALineBundle M U e hU).toUnit i hWi
        (moduleFramesSGAModuleSection M U e hU W s) =
      moduleOverFrameCoefficient M (U i) (e i) W hWi s := by
  change X.presheaf.map (homOfLE (le_inf le_rfl hWi)).op
    (moduleOverFrameCoefficient M (U i) (e i) (W ⊓ U i) inf_le_right
      (M.presheaf.map (homOfLE inf_le_left).op s)) = _
  rw [← moduleOverFrameCoefficient_restrict M (U i) (e i) inf_le_right
    (homOfLE (le_inf le_rfl hWi))]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact M.presheaf.map_id_apply (op W) s

theorem moduleFramesSGAModuleLinear_bijective_on_frame (i : ι) (W : X.Opens)
    (hWi : W ≤ U i) : Function.Bijective (moduleFramesSGAModuleLinear M U e hU W) := by
  let a := (moduleOverFrameCoefficient M (U i) (e i) W hWi).trans
    ((moduleFramesSGALineBundle M U e hU).unitEquiv (n := 1) i hWi).symm
  have he : moduleFramesSGAModuleLinear M U e hU W = a.toLinearMap := by
    ext s
    apply ((moduleFramesSGALineBundle M U e hU).unitEquiv (n := 1) i hWi).injective
    change (moduleFramesSGALineBundle M U e hU).toUnit i hWi
      (moduleFramesSGAModuleSection M U e hU W s) = _
    rw [moduleFramesSGAModuleSection_toUnit]
    exact (LinearEquiv.apply_symm_apply _ _).symm
  rw [he]
  exact a.bijective

theorem moduleFramesToSGAModuleHom_isIso : IsIso (moduleFramesToSGAModuleHom M U e hU) := by
  apply moduleHom_isIso_of_openCover U (IsOpenCover.mk hU)
  intro i
  apply moduleHom_isIso_of_affine_app_bijective
  intro V
  change Function.Bijective (moduleFramesSGAModuleLinear M U e hU ((U i).ι ''ᵁ V.1))
  exact moduleFramesSGAModuleLinear_bijective_on_frame M U e hU i _ ((U i).ι_image_le V.1)

noncomputable def moduleFramesSGAModuleIso :
    M ≅ (moduleFramesSGALineBundle M U e hU).toModules 1 :=
  letI := moduleFramesToSGAModuleHom_isIso M U e hU
  asIso (moduleFramesToSGAModuleHom M U e hU)

end MixedFujita

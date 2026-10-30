/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleAffineExactness
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Local injectivity on nonempty subopens of a cover detects global module
injectivity. The point-indexed refinement has no empty opens to check.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : Scheme.{u}} {M N : X.Modules}

theorem moduleHom_app_injective_of_nonempty_cover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (f : M ⟶ N)
    (h : ∀ (i : ι) (V : X.Opens) [Nonempty V], V ≤ U i →
      Function.Injective (Scheme.Modules.Hom.app f V)) (W : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app f W) := by
  classical
  intro s t hst
  have hx : ∀ x : W, ∃ i, x.val ∈ U i := fun x =>
    Opens.mem_iSup.mp (hU.ge (Opens.mem_top x.val))
  choose i hi using hx
  let V : W → X.Opens := fun x => W ⊓ U (i x)
  have hcover : W ≤ iSup V := by
    intro x hxW
    exact Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hxW, hi ⟨x, hxW⟩⟩
  let F : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply F.eq_of_locally_eq' V W
    (fun x : W => homOfLE (show V x ≤ W from inf_le_left)) hcover s t
  intro x
  let : Nonempty (V x) := ⟨⟨x.val, x.property, hi x⟩⟩
  apply h (i x) (V x) inf_le_right
  change Scheme.Modules.Hom.app f (V x)
      (M.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op s) =
    Scheme.Modules.Hom.app f (V x)
      (M.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op t)
  have hs := f.mapPresheaf.naturality_apply (homOfLE (show V x ≤ W from inf_le_left)).op s
  have ht := f.mapPresheaf.naturality_apply (homOfLE (show V x ≤ W from inf_le_left)).op t
  change Scheme.Modules.Hom.app f (V x)
    (M.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op s) =
      N.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op
        (Scheme.Modules.Hom.app f W s) at hs
  change Scheme.Modules.Hom.app f (V x)
    (M.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op t) =
      N.presheaf.map (homOfLE (show V x ≤ W from inf_le_left)).op
        (Scheme.Modules.Hom.app f W t) at ht
  rw [hs, ht, hst]

theorem moduleHom_mono_of_nonempty_cover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (f : M ⟶ N)
    (h : ∀ (i : ι) (V : X.Opens) [Nonempty V], V ≤ U i →
      Function.Injective (Scheme.Modules.Hom.app f V)) : Mono f :=
  moduleHom_mono_of_affine_app_injective f fun W =>
    moduleHom_app_injective_of_nonempty_cover U hU f h W.val

end MixedFujita

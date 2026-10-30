/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChangedRoundupPrincipalizedComparison
public import MixedFujita.ModuleNonemptyCoverInjection
public import MixedFujita.ModulePullbackFrameGenerators
public import TauCeti.AlgebraicGeometry.LineBundle.Germ

/-! A nonzero map from an invertible module to a dominant Cartier direct
image is monic. Restriction injectivity and torsion-free sections are derived
from the actual Cartier source and dominance; no supplied generic-injectivity,
coherence or rank-one condition on the target is required. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T)

theorem cartier_direct_image_restriction_injective {U V : B.Opens}
    [Nonempty U] (i : U ⟶ V) :
    Function.Injective (((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map i.op) := by
  letI := dominant_preimage_nonempty q U
  exact InvertibleSheaf.map_injective_of_isIntegral ⟨E.sheaf, E.isInvertible_sheaf⟩
    ((Opens.map q.base).map i)

theorem moduleHom_to_cartier_direct_image_eq_zero_of_on_nonempty_open
    {M : B.Modules} (f : M ⟶ (Scheme.Modules.pushforward q).obj E.sheaf)
    (U : B.Opens) [Nonempty U]
    (hf : ∀ (V : B.Opens), V ≤ U → Scheme.Modules.Hom.app f V = 0) : f = 0 := by
  apply moduleHom_ext_affine
  intro W
  ext s
  rcases isEmpty_or_nonempty W.1 with hW | hW
  · have hbot : W.1 = ⊥ := Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hW)
    letI : Subsingleton Γ((Scheme.Modules.pushforward q).obj E.sheaf, W.1) :=
      abelianSheaf_empty_sections_subsingleton
      ((SheafOfModules.toSheaf B.ringCatSheaf).obj ((Scheme.Modules.pushforward q).obj E.sheaf)) hbot
    exact Subsingleton.elim _ _
  · let V := W.1 ⊓ U
    letI : Nonempty V := ⟨⟨genericPoint B, genericPoint_mem W.1, genericPoint_mem U⟩⟩
    apply cartier_direct_image_restriction_injective q E (homOfLE (show V ≤ W.1 from inf_le_left))
    have hn := f.mapPresheaf.naturality_apply (homOfLE (show V ≤ W.1 from inf_le_left)).op s
    change Scheme.Modules.Hom.app f V (M.presheaf.map (homOfLE inf_le_left).op s) =
      ((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map (homOfLE inf_le_left).op
        (Scheme.Modules.Hom.app f W.1 s) at hn
    change ((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map
      (homOfLE (show V ≤ W.1 from inf_le_left)).op (Scheme.Modules.Hom.app f W.1 s) =
        ((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map
          (homOfLE (show V ≤ W.1 from inf_le_left)).op 0
    rw [← hn, hf V inf_le_right, map_zero]
    rfl

theorem nonzero_frame_generator_image_to_cartier_direct_image
    {M : B.Modules} (f : M ⟶ (Scheme.Modules.pushforward q).obj E.sheaf) (hf : f ≠ 0)
    (U : B.Opens) [Nonempty U]
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Scheme.Modules.Hom.app f U (moduleOpenFrameGenerator M U e) ≠ 0 := by
  intro ht
  apply hf
  apply moduleHom_to_cartier_direct_image_eq_zero_of_on_nonempty_open q E f U
  intro V hVU
  ext s
  conv_lhs => rw [moduleOpenFrameGenerator_generates M U e V hVU s]
  rw [Scheme.Modules.Hom.app_smul]
  have hn := f.mapPresheaf.naturality_apply (homOfLE hVU).op (moduleOpenFrameGenerator M U e)
  change Scheme.Modules.Hom.app f V
    (M.presheaf.map (homOfLE hVU).op (moduleOpenFrameGenerator M U e)) =
      ((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map (homOfLE hVU).op
        (Scheme.Modules.Hom.app f U (moduleOpenFrameGenerator M U e)) at hn
  rw [hn, ht, map_zero, smul_zero]
  rfl

theorem nonzero_frame_map_to_cartier_direct_image_app_injective
    {M : B.Modules} (f : M ⟶ (Scheme.Modules.pushforward q).obj E.sheaf) (hf : f ≠ 0)
    (U : B.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (V : B.Opens) [Nonempty V] (hVU : V ≤ U) :
    Function.Injective (Scheme.Modules.Hom.app f V) := by
  letI : Nonempty U := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact ⟨⟨v.1, hVU v.property⟩⟩
  letI := cartier_direct_image_sections_noZeroSMulDivisors q E V
  have htU := nonzero_frame_generator_image_to_cartier_direct_image q E f hf U e
  have hn := f.mapPresheaf.naturality_apply (homOfLE hVU).op (moduleOpenFrameGenerator M U e)
  change Scheme.Modules.Hom.app f V
    (M.presheaf.map (homOfLE hVU).op (moduleOpenFrameGenerator M U e)) =
      ((Scheme.Modules.pushforward q).obj E.sheaf).presheaf.map (homOfLE hVU).op
        (Scheme.Modules.Hom.app f U (moduleOpenFrameGenerator M U e)) at hn
  have htV : Scheme.Modules.Hom.app f V
      (M.presheaf.map (homOfLE hVU).op (moduleOpenFrameGenerator M U e)) ≠ 0 := by
    rw [hn]
    intro hz
    apply htU
    apply cartier_direct_image_restriction_injective q E (homOfLE hVU)
    simpa only [map_zero] using hz
  have hker : ∀ s : Γ(M, V), Scheme.Modules.Hom.app f V s = 0 → s = 0 := by
    intro s hs
    have he := moduleOpenFrameGenerator_generates M U e V hVU s
    have hz : moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) V hVU s •
        Scheme.Modules.Hom.app f V
          (M.presheaf.map (homOfLE hVU).op (moduleOpenFrameGenerator M U e)) = 0 := by
      rw [← Scheme.Modules.Hom.app_smul, ← he, hs]
    have hr := (eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_right htV
    rw [he, hr, zero_smul]
  intro s t hst
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hst, sub_self]

theorem nonzero_invertible_to_cartier_direct_image_mono
    {M : B.Modules} (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible B M)
    (f : M ⟶ (Scheme.Modules.pushforward q).obj E.sheaf) (hf : f ≠ 0) : Mono f := by
  obtain ⟨ι, U, hU, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  apply moduleHom_mono_of_nonempty_cover U hU.iSup_eq_top f
  intro i V _ hVU
  exact nonzero_frame_map_to_cartier_direct_image_app_injective q E f hf (U i)
    (Classical.choice (e i)).symm V hVU

theorem nonzero_cartier_to_cartier_direct_image_mono
    (D : CartierDivisor B) (f : D.sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf)
    (hf : f ≠ 0) : Mono f :=
  nonzero_invertible_to_cartier_direct_image_mono q E D.isInvertible_sheaf f hf

end MixedFujita

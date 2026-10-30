/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Cohomology.CechComparison
public import Mathlib.Algebra.Category.Grp.Zero

/-! 局所acyclicity不要の大域H1消滅から有限Čech次数1完全性。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite Limits
open TopCat.Presheaf TopCat.Sheaf
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

/-- Vanishing of actual first sheaf cohomology implies exactness of the
first Cech differential for EVERY finite open family. No acyclicity on the
members or their intersections is required. -/
theorem sheaf_cech_exactAt_one_of_H1_subsingleton
    {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} (U : Fin n → Opens X)
    (hvan : Subsingleton (F.H' 1 (⨆ i, U i))) :
    (cechComplex U F.obj).ExactAt 1 := by
  let S := injSeq F
  have hS : S.ShortExact := injSeq_shortExact F
  have hI := cechComplex_exactAt_of_injective S.X₂ U 0
  have hW : Function.Surjective (S.g.hom.app (op (⨆ i, U i))) :=
    surjective_app_of_subsingleton_H'_one hS _ hvan
  rw [cechComplex_exactAt_succ_iff] at hI ⊢
  intro φ hφ
  obtain ⟨i, hi⟩ := hI (cechCochainMap U S.f.hom 1 φ)
    (by rw [cechD_cechCochainMap, hφ, map_zero])
  have hgi : cechD U S.X₃.obj 0 (cechCochainMap U S.g.hom 0 i) = 0 := by
    rw [cechD_cechCochainMap, hi, cechCochainMap_g_f]
  obtain ⟨s, hs⟩ := exists_cechAugmentation_eq U S.X₃ _ hgi
  obtain ⟨t, rfl⟩ := hW s
  have e : cechAugmentation U S.X₃.obj (S.g.hom.app _ t) =
      cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t) :=
    funext fun z => (NatTrans.naturality_apply S.g.hom _ t).symm
  obtain ⟨ψ, hψ⟩ := exists_cechCochainMap_eq hS U 0 (i - cechAugmentation U S.X₂.obj t) (by
    rw [map_sub, ← e, hs, sub_self])
  refine ⟨ψ, cechCochainMap_injective hS U 1 ?_⟩
  rw [← cechD_cechCochainMap, hψ, map_sub, cechD_cechAugmentation, sub_zero, hi]


/-- First Cech homology is zero for any finite open family whenever first
sheaf cohomology on its union is zero. Local higher cohomology is unrestricted. -/
theorem sheaf_cech_homology_one_subsingleton_of_H1_subsingleton
    {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} (U : Fin n → Opens X)
    (hvan : Subsingleton (F.H' 1 (⨆ i, U i))) :
    Subsingleton ((cechComplex U F.obj).homology 1) :=
  AddCommGrpCat.subsingleton_of_isZero
    (sheaf_cech_exactAt_one_of_H1_subsingleton F U hvan).isZero_homology

end MixedFujita

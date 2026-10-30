/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors and Kenta Kitamura.
The gluing proof is adapted from SGA/Foundations/Cohomology/Leray.lean,
released under the MIT license; see vendor/SlopdeGeometrieAlgebrique-LICENSE.
-/
module
public import MixedFujita.SheafCechOneVanishing

/-! Degree-one gluing needs H¹ only on the individual cover members.
No higher cohomology or cohomology on their intersections is assumed. -/

@[expose] public section
open CategoryTheory TopologicalSpace Topology Opposite Limits
open TopCat.Presheaf TopCat.Sheaf
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Local lifts on cover members and Čech exactness in degree one glue
to a global lift. Surjectivity on intersections is unnecessary. -/
theorem sheaf_sections_surjective_of_cech_one_and_member_surjective
    {X : TopCat.{u}}
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) {n : ℕ} (U : Fin n → Opens X)
    (hlocal : ∀ i, Function.Surjective (S.g.hom.app (op (U i))))
    (hcech : (cechComplex U S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op (⨆ i, U i))) := by
  classical
  have hsurj (x : Fin 1 → Fin n) :
      Function.Surjective (S.g.hom.app (op (cechOpen U x))) := by
    have he : cechOpen U x = U (x 0) :=
      le_antisymm (cechOpen_le U x 0)
        (le_iInf fun a => (show a = 0 from Fin.fin_one_eq_zero a) ▸ le_rfl)
    rw [he]
    exact hlocal (x 0)
  rw [cechComplex_exactAt_succ_iff] at hcech
  intro s
  choose t ht using fun x : Fin 1 → Fin n =>
    hsurj x (cechAugmentation U S.X₃.obj s x)
  have hgt : cechCochainMap U S.g.hom 0 t = cechAugmentation U S.X₃.obj s := funext ht
  have hdt : cechCochainMap U S.g.hom 1 (cechD U S.X₂.obj 0 t) = 0 := by
    rw [← cechD_cechCochainMap, hgt, cechD_cechAugmentation]
  obtain ⟨f, hf⟩ := exists_cechCochainMap_eq hS U 1 _ hdt
  have hdf : cechD U S.X₁.obj 1 f = 0 := by
    apply cechCochainMap_injective hS U 2
    rw [← cechD_cechCochainMap, hf, cechD_cechD, map_zero]
  obtain ⟨b, hb⟩ := hcech f hdf
  obtain ⟨t', ht'⟩ := exists_cechAugmentation_eq U S.X₂
    (t - cechCochainMap U S.f.hom 0 b)
    (by rw [map_sub, cechD_cechCochainMap, hb, hf, sub_self])
  refine ⟨t', cechAugmentation_injective U S.X₃ ?_⟩
  have he : cechAugmentation U S.X₃.obj (S.g.hom.app _ t') =
      cechCochainMap U S.g.hom 0 (cechAugmentation U S.X₂.obj t') :=
    funext fun z => (NatTrans.naturality_apply S.g.hom _ t').symm
  rw [← hgt, he, ht', map_sub, cechCochainMap_g_f, sub_zero]

/-- First cohomology vanishes on the union if it vanishes on each member
and the Čech complex is exact in degree one. -/
theorem sheaf_H1_subsingleton_of_cech_one_and_member_H1
    {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} (U : Fin n → Opens X)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hcech : (cechComplex U F.obj).ExactAt 1) :
    Subsingleton (F.H' 1 (⨆ i, U i)) := by
  let S := injSeq F
  have hS : S.ShortExact := injSeq_shortExact F
  exact subsingleton_H'_one_of_surjective hS _
    (sheaf_sections_surjective_of_cech_one_and_member_surjective hS U
      (fun i => surjective_app_of_subsingleton_H'_one hS _ (hlocal i)) hcech)

/-- Under memberwise H¹ vanishing, Čech exactness in degree one is
equivalent to H¹ vanishing on the union. -/
theorem sheaf_cech_exactAt_one_iff_H1_of_member_H1
    {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    {n : ℕ} (U : Fin n → Opens X)
    (hlocal : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (cechComplex U F.obj).ExactAt 1 ↔ Subsingleton (F.H' 1 (⨆ i, U i)) :=
  ⟨sheaf_H1_subsingleton_of_cech_one_and_member_H1 F U hlocal,
    sheaf_cech_exactAt_one_of_H1_subsingleton F U⟩

end MixedFujita

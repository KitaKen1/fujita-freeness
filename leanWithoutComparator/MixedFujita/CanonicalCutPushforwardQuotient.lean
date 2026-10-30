/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalSubcutUnitInclusion
public import MixedFujita.QuasicoherentImageIdealSheaf
public import SGA.Foundations.Cohomology.QuasiCoherentLocal

/-! 標準臨界商の順像と実像イデアル閉部分源構造層の同型。 check-272：高次ample捻りの実大域切断全射と有限生成から、対象層だけの連接性で実層写像の全射性を検出。実射影公式の自然性を写像で証明し、引き戻したample捻りの全大H1消滅からproper順像の商全射・短完全性を内部構成。通常の絶対H1版KVを明示した入力として、元の孤立lc中心から実SNCモデル・例外roundup E・非零臨界Cartier切断Sを内部構成し、内在商 O(E)/O(E-S) の順像を正確な被約中心構造層と、元の単位写像を保って同定。さらに正常源上のCartier格子の交わりをDVR次数で制御し、共通成分のないE/Sについて、実際の未捻り切断Sの構造層から内在商への標準単射を構成。通常KVによる商全射性でこの写像の順像が同型となるため、元の孤立lc中心について実際の未捻り臨界切断の構造層順像＝被約中心構造層まで、モデル・相対消滅・中心正規性を追加仮定せず接続。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Once the ACTUAL canonical cut sequence stays exact under direct image,
its direct-image quotient is the structure module of its actual image-ideal
subscheme. The isomorphism preserves the canonical map from O_X. -/
theorem canonical_cut_cokernel_pushforward_iso_image_subscheme
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (p : T ⟶ X) (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    [((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsQuasicoherent]
    (hpush : ((ShortComplex.cokernelSequence (cartierEffectiveInclusion E S hS)).map
      (Scheme.Modules.pushforward p)).ShortExact) :
    let j := cartierSubcutPushforwardUnitInclusion p E S hE hS
    let I := quasicoherentModuleImageIdealSheaf _ j
    ∃ a : (Scheme.Modules.pushforward p).obj (cokernel (cartierEffectiveInclusion E S hS)) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj (CohomologyAux.unitModule I.subscheme),
      effectiveCartierPushforwardUnitMap p E hE ≫
        (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS)) ≫ a.hom =
          schemeUnitToPushforwardUnit I.subschemeι := by
  dsimp only
  let j := cartierSubcutPushforwardUnitInclusion p E S hE hS
  let I := quasicoherentModuleImageIdealSheaf _ j
  let := cartierSubcutPushforwardUnitInclusion_mono p E S hE hS
  let c := asIso (effectiveCartierPushforwardUnitMap p E hE)
  let V := (ShortComplex.cokernelSequence (cartierEffectiveInclusion E S hS)).map
    (Scheme.Modules.pushforward p)
  let U : ShortComplex X.Modules := ShortComplex.mk j
    (c.hom ≫ (Scheme.Modules.pushforward p).map (cokernel.π (cartierEffectiveInclusion E S hS))) (by
      dsimp [j, cartierSubcutPushforwardUnitInclusion, c]
      simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
        cokernel.condition, Functor.map_zero])
  let e : V ≅ U := ShortComplex.isoMk (Iso.refl _) c.symm (Iso.refl _)
    (by simp only [V, U, ShortComplex.cokernelSequence, ShortComplex.map_f,
      Iso.refl_hom, Category.id_comp]; rfl)
    (by simp only [V, U, ShortComplex.cokernelSequence, ShortComplex.map_g,
      Iso.refl_hom, Category.comp_id, Iso.symm_hom, Iso.inv_hom_id_assoc])
  have hU : U.ShortExact := ShortComplex.shortExact_of_iso e hpush
  have hI := quasicoherentImageIdealShortComplex_shortExact j
  let a := hU.gIsCokernel.coconePointUniqueUpToIso hI.gIsCokernel
  refine ⟨a, ?_⟩
  change U.g ≫ a.hom = (quasicoherentImageIdealShortComplex j).g
  exact IsColimit.comp_coconePointUniqueUpToIso_hom hU.gIsCokernel hI.gIsCokernel WalkingParallelPair.one

end MixedFujita

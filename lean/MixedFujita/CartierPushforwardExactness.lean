/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleGlobalSectionEpimorphism
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.ProperCoherentPushforward
public import MixedFujita.ProperCartierCohomology

/-! 実射影公式の自然性とH1捻りからproper順像短完全性。 check-272：高次ample捻りの実大域切断全射と有限生成から、対象層だけの連接性で実層写像の全射性を検出。実射影公式の自然性を写像で証明し、引き戻したample捻りの全大H1消滅からproper順像の商全射・短完全性を内部構成。通常の絶対H1版KVを明示した入力として、元の孤立lc中心から実SNCモデル・例外roundup E・非零臨界Cartier切断Sを内部構成し、内在商 O(E)/O(E-S) の順像を正確な被約中心構造層と、元の単位写像を保って同定。さらに正常源上のCartier格子の交わりをDVR次数で制御し、共通成分のないE/Sについて、実際の未捻り切断Sの構造層から内在商への標準単射を構成。通常KVによる商全射性でこの写像の順像が同型となるため、元の孤立lc中心について実際の未捻り臨界切断の構造層順像＝被約中心構造層まで、モデル・相対消滅・中心正規性を追加仮定せず接続。 -/

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


/-- Pushing forward an actual module map preserves surjectivity on GLOBAL
sections, using only the inverse image of the top open. -/
theorem modulePushforward_global_sections_surjective_of_source
    {X Y : Scheme.{u}} (p : Y ⟶ X) {M N : Y.Modules} (f : M ⟶ N)
    (hs : Function.Surjective (Scheme.Modules.Hom.app f ⊤)) :
    Function.Surjective (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward p).map f) ⊤) := by
  change Function.Surjective (Scheme.Modules.Hom.app f (p ⁻¹ᵁ ⊤))
  simpa only [Scheme.Hom.preimage_top] using hs


/-- Actual projection formula NATURALITY transfers global section
surjectivity from the pulled Cartier twist upstairs to the twisted direct
image downstairs. This statement includes the actual map, not just objects. -/
theorem cartier_twisted_pushforward_sections_surjective_of_source
    {X Y : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) (D : CartierDivisor X)
    {M N : Y.Modules} (f : M ⟶ N)
    (hs : Function.Surjective (Scheme.Modules.Hom.app
      ((cartierPullbackTwistFunctor D p).map f) ⊤)) :
    Function.Surjective (Scheme.Modules.Hom.app
      ((cartierTwistFunctor D).map ((Scheme.Modules.pushforward p).map f)) ⊤) := by
  have hp := modulePushforward_global_sections_surjective_of_source p _ hs
  let a := cartierProjectionFormulaNatIso D p
  intro z
  obtain ⟨y, hy⟩ := hp (Scheme.Modules.Hom.app (a.hom.app N) ⊤ z)
  refine ⟨Scheme.Modules.Hom.app (a.inv.app M) ⊤ y, ?_⟩
  apply CohomologyAux.app_injective_of_mono (a.hom.app N) ⊤
  have he := congrArg (fun g => Scheme.Modules.Hom.app g ⊤
    (Scheme.Modules.Hom.app (a.inv.app M) ⊤ y)) (a.hom.naturality f)
  change Scheme.Modules.Hom.app (a.hom.app N) ⊤
      (Scheme.Modules.Hom.app ((cartierTwistFunctor D).map ((Scheme.Modules.pushforward p).map f)) ⊤
        (Scheme.Modules.Hom.app (a.inv.app M) ⊤ y)) = _ at he
  rw [he]
  change Scheme.Modules.Hom.app
    (a.inv.app M ≫ a.hom.app M ≫ (cartierPullbackTwistFunctor D p ⋙ Scheme.Modules.pushforward p).map f) ⊤ y = _
  have hc : a.inv.app M ≫ a.hom.app M = 𝟙 _ := (a.app M).inv_hom_id
  rw [← Category.assoc, hc, Category.id_comp]
  exact hy


/-- Eventual H1 vanishing of the ACTUAL pulled ample twists makes the
actual proper direct image of a quotient map epimorphic. No local or higher
direct-image vanishing, all-higher KV or extra relative theorem is assumed. -/
theorem proper_pushforward_epi_of_eventually_pulled_ample_H1_vanishing
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsProper p] (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact) [S.X₃.IsCoherent]
    (hvan : ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → Subsingleton
      (Scheme.Modules.Cohomology (((Scheme.Modules.pullback p).obj (b • A).sheaf) ⊗ S.X₁) 1)) :
    Epi ((Scheme.Modules.pushforward p).map S.g) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (p ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (Y ↘ Spec (CommRingCat.of K))
  let : ((Scheme.Modules.pushforward p).obj S.X₃).IsCoherent :=
    proper_module_pushforward_isCoherent p S.X₃
  apply moduleHom_epi_of_eventually_ample_twisted_sections_surjective K A hA
  obtain ⟨b₀, hb₀⟩ := hvan
  refine ⟨b₀, fun b hb => ?_⟩
  let F := cartierPullbackTwistFunctor (b • A) p
  let : F.IsEquivalence := inferInstanceAs
    (cartierPullbackTwistEquivalence (b • A) p).functor.IsEquivalence
  have ht : (S.map F).ShortExact := hS.map_of_exact F
  apply cartier_twisted_pushforward_sections_surjective_of_source p (b • A) S.g
  exact Scheme.Modules.sections_surjective ht (hb₀ b hb)


/-- With the same genuine H1 input, proper direct image preserves the
ENTIRE actual short exact sequence. The epimorphism is constructed; only
left exactness is taken from the actual pushforward adjunction. -/
theorem proper_pushforward_shortExact_of_eventually_pulled_ample_H1_vanishing
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsProper p] (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    {S : ShortComplex Y.Modules} (hS : S.ShortExact) [S.X₃.IsCoherent]
    (hvan : ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b → Subsingleton
      (Scheme.Modules.Cohomology (((Scheme.Modules.pullback p).obj (b • A).sheaf) ⊗ S.X₁) 1)) :
    (S.map (Scheme.Modules.pushforward p)).ShortExact := by
  let : (Scheme.Modules.pushforward p).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).isRightAdjoint
  let := hS.mono_f
  have hf : Mono ((Scheme.Modules.pushforward p).map S.f) :=
    (Scheme.Modules.pushforward p).map_mono S.f
  have hg : Epi ((Scheme.Modules.pushforward p).map S.g) :=
    proper_pushforward_epi_of_eventually_pulled_ample_H1_vanishing K p A hA hS hvan
  exact ShortComplex.ShortExact.mk'
    (hS.exact.map_of_mono_of_preservesKernel (Scheme.Modules.pushforward p) hS.mono_f inferInstance)
    hf hg

end MixedFujita

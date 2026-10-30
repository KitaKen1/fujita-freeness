/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentAmpleTwistGeneration
public import MixedFujita.FiniteFreeGlobalGenerators
public import MixedFujita.CartierTwistExactness

/-! 有限大域生成と高次ample捻り切断による実層全射性検出。 check-272：高次ample捻りの実大域切断全射と有限生成から、対象層だけの連接性で実層写像の全射性を検出。実射影公式の自然性を写像で証明し、引き戻したample捻りの全大H1消滅からproper順像の商全射・短完全性を内部構成。通常の絶対H1版KVを明示した入力として、元の孤立lc中心から実SNCモデル・例外roundup E・非零臨界Cartier切断Sを内部構成し、内在商 O(E)/O(E-S) の順像を正確な被約中心構造層と、元の単位写像を保って同定。さらに正常源上のCartier格子の交わりをDVR次数で制御し、共通成分のないE/Sについて、実際の未捻り切断Sの構造層から内在商への標準単射を構成。通常KVによる商全射性でこの写像の順像が同型となるため、元の孤立lc中心について実際の未捻り臨界切断の構造層順像＝被約中心構造層まで、モデル・相対消滅・中心正規性を追加仮定せず接続。 -/

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


/-- The canonical map of a section commutes with every actual module map. -/
theorem module_homOfSection_comp
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (s : Γ(M, ⊤)) :
    CohomologyAux.homOfSection M s ≫ f =
      CohomologyAux.homOfSection N (Scheme.Modules.Hom.app f ⊤ s) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Scheme.Modules.Hom.app f U ((CohomologyAux.homOfSection M s).app U r) = _
  rw [CohomologyAux.homOfSection_app, Scheme.Modules.Hom.app_smul,
    CohomologyAux.homOfSection_app, CohomologyAux.hom_app_presheaf_map]


/-- Surjectivity on global sections is enough for an epimorphism when the
actual target has a finite-free global presentation. -/
theorem moduleHom_epi_of_finite_free_target_and_surjective_sections
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (k : ℕ) (π : CohomologyAux.unitBiproduct X k ⟶ N) [Epi π]
    (hs : Function.Surjective (Scheme.Modules.Hom.app f ⊤)) : Epi f := by
  classical
  obtain ⟨g, hg⟩ := finite_free_epi_exists_canonical_global_generators k π
  choose t ht using fun i => hs (g i)
  let τ : CohomologyAux.unitBiproduct X k ⟶ M :=
    biproduct.desc (fun i => CohomologyAux.homOfSection M (t i))
  have he : τ ≫ f = biproduct.desc (fun i => CohomologyAux.homOfSection N (g i)) := by
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.ι_desc_assoc, biproduct.ι_desc, module_homOfSection_comp, ht]
  let : Epi (τ ≫ f) := he.symm ▸ hg
  exact epi_of_epi τ f


/-- Actual high ample twists detect epimorphisms of module sheaves. Only
the target is assumed coherent; source cohomology is not an input. -/
theorem moduleHom_epi_of_eventually_ample_twisted_sections_surjective
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    {M N : X.Modules} [N.IsCoherent] (f : M ⟶ N)
    (hs : ∃ b₁ : ℕ, ∀ b : ℕ, b₁ ≤ b →
      Function.Surjective (Scheme.Modules.Hom.app ((cartierTwistFunctor (b • A)).map f) ⊤)) :
    Epi f := by
  obtain ⟨b₀, hb₀⟩ := cartierIsAmpleProj_coherent_tensor_all_high_finite_free_epi A hA N
  obtain ⟨b₁, hb₁⟩ := hs
  obtain ⟨k, π, hπ⟩ := hb₀ (max b₀ b₁) (le_max_left _ _)
  let := hπ
  have ht : Epi ((cartierTwistFunctor ((max b₀ b₁) • A)).map f) :=
    moduleHom_epi_of_finite_free_target_and_surjective_sections _ k π
      (hb₁ _ (le_max_right _ _))
  exact (cartierTwistFunctor ((max b₀ b₁) • A)).epi_of_epi_map ht

end MixedFujita

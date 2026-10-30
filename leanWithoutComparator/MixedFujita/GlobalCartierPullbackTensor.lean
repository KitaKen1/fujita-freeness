/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleOpenRestrictionAdjunctionTensor
public import MixedFujita.ModuleOpenCoverIsomorphisms

/-!
The actual canonical module-pullback tensor comparison is an isomorphism
if either source factor is the sheaf of an actual Cartier divisor on an
integral scheme. The other module, morphism and target scheme are arbitrary.
Restriction tensor compatibility and the identified inverse restriction
comparisons make the global comparison locally invertible. The inverse
images of source neighborhoods chosen at each target point cover the
target; the actual module open-cover criterion supplies the global result.
Compatible all-graded Cartier pullback representations, chosen curves,
uniform ambient degrees and the final Fujita statements are not asserted.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}
attribute [local instance] moduleRestrictOplaxMonoidal

theorem modulePullbackTensorComparison_restrict_isIso_of_localIso
    (φ : Y ⟶ X) (U : X.Opens) (M N : X.Modules)
    [IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
      (M.restrict U.ι) (N.restrict U.ι))] :
    IsIso ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι).map
      (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N)) := by
  have := moduleOpenRestrictionInducedOplaxTensor_isIso U.ι M N
  have := moduleOpenRestrictionInducedOplaxTensor_isIso (φ ⁻¹ᵁ U).ι
    ((Scheme.Modules.pullback φ).obj M) ((Scheme.Modules.pullback φ).obj N)
  have h := modulePullbackRestrictionIso_tensor_explicit φ U M N
  have hc : IsIso ((Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι).map
      (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) ≫
    Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι)
      ((Scheme.Modules.pullback φ).obj M) ((Scheme.Modules.pullback φ).obj N) ≫
    ((modulePullbackRestrictionIso φ U M).hom ⊗ₘ
      (modulePullbackRestrictionIso φ U N).hom)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Functor.OplaxMonoidal.δ (Scheme.Modules.restrictFunctor (φ ⁻¹ᵁ U).ι)
      ((Scheme.Modules.pullback φ).obj M) ((Scheme.Modules.pullback φ).obj N) ≫
      ((modulePullbackRestrictionIso φ U M).hom ⊗ₘ
        (modulePullbackRestrictionIso φ U N).hom))

theorem modulePullbackTensorComparison_isIso_of_point_localIso
    (φ : Y ⟶ X) (M N : X.Modules)
    (h : ∀ y : Y, ∃ U : X.Opens, φ y ∈ U ∧
      IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
        (M.restrict U.ι) (N.restrict U.ι))) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M N) := by
  classical
  choose U hy hIso using h
  have hcover : IsOpenCover (fun y ↦ φ ⁻¹ᵁ U y) := by
    rw [IsOpenCover]
    apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  apply moduleHom_isIso_of_openCover (fun y ↦ φ ⁻¹ᵁ U y) hcover
  intro y
  have := hIso y
  exact modulePullbackTensorComparison_restrict_isIso_of_localIso φ (U y) M N

open TauCeti.AlgebraicGeometry.Scheme

theorem cartierPullbackTensorComparison_isIso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (N : X.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) D.sheaf N) := by
  apply modulePullbackTensorComparison_isIso_of_point_localIso φ D.sheaf N
  intro y
  exact cartierPullbackTensorComparison_exists_point_local_iso D φ y N

theorem cartierRightPullbackTensorComparison_exists_point_local_iso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (y : Y) (M : X.Modules) :
    ∃ U : X.Opens, φ y ∈ U ∧
      IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback (φ ∣_ U))
        (M.restrict U.ι) (D.sheaf.restrict U.ι)) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨U, hy, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨φ y, hy⟩⟩
  exact ⟨U, hy, modulePullbackTensorComparison_isIso_of_right_frame
    (φ ∣_ U) _ _ (cartierOpenRestrictFrameIso D U f hU)⟩

theorem cartierRightPullbackTensorComparison_isIso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (M : X.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M D.sheaf) := by
  apply modulePullbackTensorComparison_isIso_of_point_localIso φ M D.sheaf
  intro y
  exact cartierRightPullbackTensorComparison_exists_point_local_iso D φ y M

noncomputable def cartierPullbackTensorIso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullback φ).obj (D.sheaf ⊗ N) ≅
      (Scheme.Modules.pullback φ).obj D.sheaf ⊗ (Scheme.Modules.pullback φ).obj N := by
  have := cartierPullbackTensorComparison_isIso D φ N
  exact asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) D.sheaf N)

theorem cartierPullbackTensorIso_hom [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (N : X.Modules) :
    (cartierPullbackTensorIso D φ N).hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) D.sheaf N := rfl

noncomputable def cartierRightPullbackTensorIso [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullback φ).obj (M ⊗ D.sheaf) ≅
      (Scheme.Modules.pullback φ).obj M ⊗ (Scheme.Modules.pullback φ).obj D.sheaf := by
  have := cartierRightPullbackTensorComparison_isIso D φ M
  exact asIso (Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M D.sheaf)

theorem cartierRightPullbackTensorIso_hom [IsIntegral X]
    (D : CartierDivisor X) (φ : Y ⟶ X) (M : X.Modules) :
    (cartierRightPullbackTensorIso D φ M).hom =
      Functor.OplaxMonoidal.δ (Scheme.Modules.pullback φ) M D.sheaf := rfl
end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPulledRegularSections
public import SGA.Foundations.Cohomology.Devissage

/-! 実大域切断乗法・affine被覆の正則係数から実層単射。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- The actual module morphism associated with an actual global section. -/
noncomputable def moduleGlobalSectionHom {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    CohomologyAux.unitModule X ⟶ M :=
  M.unitHomEquiv.symm (PresheafOfModules.sectionsMk
    (fun U => show M.val.obj U from M.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op s)
    (fun {U V} f => by
      change M.presheaf.map f (M.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op s) =
        M.presheaf.map (homOfLE le_top : V.unop ⟶ ⊤).op s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl))


/-- Its actual coefficient in a local frame is multiplication by the
coefficient of the fixed global section. -/
theorem moduleGlobalSectionHom_frame_coefficient
    {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (r : Γ(X, U)) :
    moduleOverFrameCoefficient M U e U le_rfl (Scheme.Modules.Hom.app (moduleGlobalSectionHom M s) U r) =
      r * moduleOverFrameCoefficient M U e U le_rfl
        (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) := by
  change moduleOverFrameCoefficient M U e U le_rfl
    (r • M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) = _
  rw [map_smul, smul_eq_mul]


/-- Regularity of the actual section coefficient gives injectivity of
the actual multiplication map on that affine chart. -/
theorem moduleGlobalSectionHom_app_injective_of_regular_coefficient
    {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (hc : moduleOverFrameCoefficient M U e U le_rfl
      (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) ∈ nonZeroDivisors Γ(X, U)) :
    Function.Injective (Scheme.Modules.Hom.app (moduleGlobalSectionHom M s) U) := by
  intro r t hrt
  have he := congrArg (moduleOverFrameCoefficient M U e U le_rfl) hrt
  rw [moduleGlobalSectionHom_frame_coefficient, moduleGlobalSectionHom_frame_coefficient] at he
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_right.mp hc) (r - t)
  rw [sub_mul, he, sub_self]


/-- Injectivity on an actual affine cover detects a module monomorphism;
the kernel is eliminated by the proved quasi-coherent affine-cover criterion. -/
theorem quasicoherent_moduleHom_mono_of_affine_cover
    {X : Scheme.{u}} {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (hinj : ∀ i, Function.Injective (Scheme.Modules.Hom.app f (U i))) :
    Mono f := by
  let : (kernel f).IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel f
  have hzero (i : ι) (s : Γ(kernel f, U i)) : s = 0 := by
    apply CohomologyAux.app_injective_of_mono (kernel.ι f) (U i)
    rw [map_zero]
    apply hinj i
    rw [map_zero]
    have he := ConcreteCategory.congr_hom
      (congrArg (fun g => Scheme.Modules.Hom.app g (U i)) (kernel.condition f)) s
    exact he
  have hid : 𝟙 (kernel f) = 0 := Scheme.Modules.hom_ext _ _ fun V => by
    ext s
    exact CohomologyAux.eq_zero_of_affine_cover (kernel f) U hU hcover hzero V s
  exact CategoryTheory.Preadditive.mono_of_isZero_kernel f ((IsZero.iff_id_eq_zero _).mpr hid)


/-- Regular coefficients on an actual affine frame cover give an actual
module monomorphism from the structure sheaf. -/
theorem moduleGlobalSectionHom_mono_of_regular_affine_frame_cover
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] (s : Γ(M, ⊤))
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (hcover : (⨆ i, U i) = ⊤)
    (hc : ∀ i, moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl
      (M.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s) ∈ nonZeroDivisors Γ(X, U i)) :
    Mono (moduleGlobalSectionHom M s) := by
  apply quasicoherent_moduleHom_mono_of_affine_cover (moduleGlobalSectionHom M s) U hU hcover
  intro i
  exact moduleGlobalSectionHom_app_injective_of_regular_coefficient M s (U i) (e i) (hc i)


/-- A generated ambient Cartier line pulls to an actual line bundle with
an actual regular global section and an actual structure-sheaf injection.
No integrality or reducedness is required of the noetherian source. -/
theorem cartier_sga_pullback_exists_mono_global_section
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsNoetherian Y]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H) :
    ∃ s : ((cartierSGALineBundle H).pullback p).sections 1,
      Mono (moduleGlobalSectionHom (((cartierSGALineBundle H).pullback p).toModules 1)
        (sgaNaturalSectionToModule ((cartierSGALineBundle H).pullback p) 1 s)) := by
  obtain ⟨ι, hι, U, hU, e, hcover, s, hs⟩ :=
    cartier_sga_pullback_exists_regular_section_affine_frames K p H hH
  exact ⟨s, moduleGlobalSectionHom_mono_of_regular_affine_frame_cover _ _ U hU e hcover hs⟩

end MixedFujita

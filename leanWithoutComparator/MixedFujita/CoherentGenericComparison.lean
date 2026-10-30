/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleAffineExactness
public import SGA.Foundations.Cohomology.Devissage

/-! 準連接な共通標的への実連接核比較列の内部構成。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The image of a coherent module in a quasi-coherent module is coherent. -/
theorem moduleImage_isCoherent_of_source_isCoherent
    {Y : Scheme.{u}} {G Q : Y.Modules} [G.IsCoherent] [Q.IsQuasicoherent]
    (φ : G ⟶ Q) : (Abelian.image φ).IsCoherent := by
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (Abelian.image φ).IsQuasicoherent := CohomologyAux.isQuasicoherent_image φ
  let S := ShortComplex.kernelSequence (Abelian.factorThruImage φ)
  have hS := CohomologyAux.shortExact_kernelSequence (Abelian.factorThruImage φ)
  let : S.X₁.IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel _
  let : S.X₂.IsCoherent := inferInstanceAs G.IsCoherent
  exact CohomologyAux.isCoherent_X₃_of_shortExact hS


/-- Kernels from a coherent source to a quasi-coherent target are coherent
on a locally noetherian scheme; the target need not be of finite type. -/
theorem moduleKernel_isCoherent_of_source_isCoherent
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {G Q : Y.Modules} [G.IsCoherent] [Q.IsQuasicoherent]
    (φ : G ⟶ Q) : (kernel φ).IsCoherent := by
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (Abelian.image φ).IsQuasicoherent := CohomologyAux.isQuasicoherent_image φ
  let S := ShortComplex.kernelSequence (Abelian.factorThruImage φ)
  have hS := CohomologyAux.shortExact_kernelSequence (Abelian.factorThruImage φ)
  let : S.X₁.IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel _
  let : S.X₂.IsCoherent := inferInstanceAs G.IsCoherent
  let : S.X₁.IsCoherent := CohomologyAux.isCoherent_X₁_of_shortExact hS
  let a := (CohomologyAux.kernelIsoKernelFactorThruImage φ).symm
  let : (kernel (Abelian.factorThruImage φ)).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_kernel _
  let : (kernel (Abelian.factorThruImage φ)).IsFiniteType := by
    change S.X₁.IsFiniteType
    exact Scheme.Modules.IsCoherent.isFiniteType
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩


/-- When all target sections on an open vanish, evaluation of the actual
kernel inclusion is bijective. Evaluation preserves kernels internally. -/
theorem moduleKernel_ι_app_bijective_of_target_sections_zero
    {Y : Scheme.{u}} {G Q : Y.Modules} (φ : G ⟶ Q) (U : Y.Opens)
    (hQ : ∀ s : Γ(Q, U), s = 0) :
    Function.Bijective ((kernel.ι φ).app U) := by
  let F := moduleOpenEvaluation Y U
  have hz : F.map φ = 0 := by
    ext s
    exact hQ _
  have hk : IsIso (kernel.ι (F.map φ)) := by
    exact KernelFork.IsLimit.isIso_ι
      (KernelFork.ofι _ (kernel.condition (F.map φ))) (kernelIsKernel (F.map φ)) hz
  have hi : IsIso (F.map (kernel.ι φ)) := by
    rw [← kernelComparison_comp_ι]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso (F.map (kernel.ι φ))


/-- Two coherent sources which map bijectively on an affine open to one
quasi-coherent target admit a coherent comparison zigzag. Its common source
is an actual kernel, so no meromorphic denominator ideal is an input. -/
theorem exists_coherent_generic_comparison_zigzag
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (G Q R : Y.Modules) [G.IsCoherent] [Q.IsCoherent] [R.IsQuasicoherent]
    (φ : G ⟶ R) (ψ : Q ⟶ R) (U : Y.Opens) (hU : IsAffineOpen U)
    (hφ : Function.Bijective (φ.app U)) (hψ : Function.Bijective (ψ.app U)) :
    ∃ P I : Y.Modules, P.IsCoherent ∧ I.IsCoherent ∧
      ∃ (a : P ⟶ G) (b : P ⟶ I) (c : Q ⟶ I),
        Function.Bijective (a.app U) ∧ Function.Bijective (b.app U) ∧
          Function.Bijective (c.app U) := by
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (cokernel ψ).IsQuasicoherent := CohomologyAux.isQuasicoherent_cokernel ψ
  let θ := φ ≫ cokernel.π ψ
  let P := kernel θ
  let I := Abelian.image ψ
  let : P.IsCoherent := moduleKernel_isCoherent_of_source_isCoherent θ
  let : I.IsCoherent := moduleImage_isCoherent_of_source_isCoherent ψ
  let a : P ⟶ G := kernel.ι θ
  let c : Q ⟶ I := Abelian.factorThruImage ψ
  let d : I ⟶ R := Abelian.image.ι ψ
  let b : P ⟶ I := kernel.lift (cokernel.π ψ) (a ≫ φ) (by
    simpa only [Category.assoc] using kernel.condition θ)
  have hbd : b ≫ d = a ≫ φ := kernel.lift_ι _ _ _
  have hcd : c ≫ d = ψ := Abelian.image.fac ψ
  have hd : Function.Bijective (d.app U) := by
    refine ⟨CohomologyAux.app_injective_of_mono d U, ?_⟩
    intro r
    obtain ⟨q, hq⟩ := hψ.2 r
    refine ⟨c.app U q, ?_⟩
    exact (congrArg (fun f : Q ⟶ R => f.app U q) hcd).trans hq
  have hzero : ∀ s : Γ(cokernel ψ, U), s = 0 :=
    (CohomologyAux.vanishesOff_cokernel ψ hU hψ.2) U (Set.disjoint_left.mpr fun _ hx hnx => hnx hx)
  have ha : Function.Bijective (a.app U) :=
    moduleKernel_ι_app_bijective_of_target_sections_zero θ U hzero
  have hbcomp : Function.Bijective (d.app U ∘ b.app U) := by
    change Function.Bijective ((b ≫ d).app U)
    rw [hbd]
    exact hφ.comp ha
  have hb := (Function.Bijective.of_comp_iff' hd _).mp hbcomp
  have hccomp : Function.Bijective (d.app U ∘ c.app U) := by
    change Function.Bijective ((c ≫ d).app U)
    rw [hcd]
    exact hψ
  have hc := (Function.Bijective.of_comp_iff' hd _).mp hccomp
  exact ⟨P,I,inferInstance,inferInstance,a,b,c,ha,hb,hc⟩

end MixedFujita

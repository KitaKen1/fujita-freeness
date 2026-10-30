/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleAffineExactness
public import MixedFujita.InvertibleIdealPresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic

/-!
For an actual invertible-ideal presentation of an actual IdealSheafData,
construct and prove the actual short exact sequence of module sheaves
0 -> I -> O_X -> i_* O_Z -> 0, where Z is the actual ideal-sheaf subscheme.
Affine quotient kernels and surjectivity supply exactness, and the affine
basis criterion supplies global short exactness. Cohomology finiteness and
the top-degree vanishing required by Euler additivity are explicit inputs;
no pointed Bertini curve or curve-uniform degree formula follows yet.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}

noncomputable def schemeUnitToPushforwardUnit (i : Y ⟶ X) :
    SheafOfModules.unit X.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

theorem schemeUnitToPushforwardUnit_app (i : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    Scheme.Modules.Hom.app (schemeUnitToPushforwardUnit i) U a = i.app U a := rfl

theorem invertibleIdeal_inclusion_quotient_comp_zero {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    P.inclusion ≫ schemeUnitToPushforwardUnit I.subschemeι = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext s
  change I.subschemeι.app U.1 (Scheme.Modules.Hom.app P.inclusion U.1 s) = 0
  have hm : Scheme.Modules.Hom.app P.inclusion U.1 s ∈ I.ideal U := by
    exact (Set.ext_iff.mp (P.image_eq U) _).mp ⟨s, rfl⟩
  rw [← I.ker_subschemeι_app U] at hm
  exact hm

noncomputable def invertibleIdealSubschemeShortComplex {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) : ShortComplex X.Modules :=
  ShortComplex.mk P.inclusion (schemeUnitToPushforwardUnit I.subschemeι)
    (invertibleIdeal_inclusion_quotient_comp_zero P)

theorem invertibleIdealSubschemeShortComplex_shortExact {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    (invertibleIdealSubschemeShortComplex P).ShortExact := by
  apply moduleShortComplex_shortExact_of_affine_evaluation
  intro U
  let S := (invertibleIdealSubschemeShortComplex P).map
    (moduleOpenEvaluation X U.1)
  have hf : Mono S.f := (ModuleCat.mono_iff_injective _).mpr (P.injective U.1)
  have hg : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr (I.subschemeι_app_surjective U)
  apply ShortComplex.ShortExact.mk' (S := S) _ hf hg
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hm : a ∈ I.ideal U := by
    rw [← I.ker_subschemeι_app U]
    exact ha
  have hr : a ∈ Set.range (Scheme.Modules.Hom.app P.inclusion U.1) := by
    rw [P.image_eq U]
    exact hm
  exact hr

noncomputable def invertibleIdealSubschemeCokernelIso {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    cokernel P.inclusion ≅
      (Scheme.Modules.pushforward I.subschemeι).obj (SheafOfModules.unit I.subscheme.ringCatSheaf) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel P.inclusion)
    (invertibleIdealSubschemeShortComplex_shortExact P).gIsCokernel

theorem invertibleIdealSubschemeCokernelIso_π_hom {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    cokernel.π P.inclusion ≫ (invertibleIdealSubschemeCokernelIso P).hom =
      schemeUnitToPushforwardUnit I.subschemeι := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel P.inclusion)
    (invertibleIdealSubschemeShortComplex_shortExact P).gIsCokernel
    WalkingParallelPair.one

theorem projectiveHypersurfaceInvertibleIdeal_actual_quotient_shortExact
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    (invertibleIdealSubschemeShortComplex
      (projectiveHypersurfaceInvertibleIdealPresentation R k₀ d f hf h0)).ShortExact :=
  invertibleIdealSubschemeShortComplex_shortExact _

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

theorem invertibleIdealSubscheme_eulerCharBelow_eq_sub
    {I : X.IdealSheafData} (P : InvertibleIdealPresentation I) (n : ℕ)
    (hI : ∀ j < n, 0 < j → FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology P.moduleSheaf j))
    (hO : ∀ j < n, FiniteDimensional K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (SheafOfModules.unit X.ringCatSheaf) j))
    (hvan : Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology P.moduleSheaf n)) :
    Scheme.Modules.eulerCharBelow K X
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf)) n =
      Scheme.Modules.eulerCharBelow K X (SheafOfModules.unit X.ringCatSheaf) n -
        Scheme.Modules.eulerCharBelow K X P.moduleSheaf n := by
  have h := Scheme.Modules.eulerCharBelow_eq_add K
    (invertibleIdealSubschemeShortComplex_shortExact P) n hI hO hvan
  change Scheme.Modules.eulerCharBelow K X (SheafOfModules.unit X.ringCatSheaf) n =
    Scheme.Modules.eulerCharBelow K X P.moduleSheaf n +
      Scheme.Modules.eulerCharBelow K X
        ((Scheme.Modules.pushforward I.subschemeι).obj
          (SheafOfModules.unit I.subscheme.ringCatSheaf)) n at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h.symm)

end MixedFujita

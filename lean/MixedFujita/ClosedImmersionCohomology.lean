/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedEmbeddingSheafCohomology
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
For an actual closed immersion i : Z -> X and any actual module sheaf M on Z,
H^n(X,i_*M) is naturally isomorphic to H^n(Z,M) in every degree.
Over Spec R, this comparison is R-linear. Finite cohomology and vanishing
are transported by the comparison when supplied; their geometric existence
on arbitrary proper schemes is not proved here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}

noncomputable def schemePushforwardToAbelianSheafIso (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.toSheaf Y ≅
      Scheme.Modules.toSheaf X ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N φ
    ext U x
    rfl)

noncomputable def closedImmersionCohomologyFunctorIso
    (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.cohomologyFunctor Y n ≅
      Scheme.Modules.cohomologyFunctor X n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (schemePushforwardToAbelianSheafIso f)
      (Sheaf.functorH.{u} (Opens.grothendieckTopology Y) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.toSheaf X)
      (closedEmbeddingCohomologyFunctorIso f.isClosedEmbedding n)

noncomputable def closedImmersionCohomologyAddEquiv
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) (n : ℕ) :
    Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n ≃+
      Scheme.Modules.Cohomology M n :=
  closedEmbeddingCohomologyAddEquiv f.isClosedEmbedding
    ((Scheme.Modules.toSheaf X).obj M) n

theorem closedImmersionCohomologyAddEquiv_naturality
    (f : X ⟶ Y) [IsClosedImmersion f] {M N : X.Modules} (φ : M ⟶ N) (n : ℕ)
    (x : Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n) :
    closedImmersionCohomologyAddEquiv f N n
        ((Scheme.Modules.cohomologyFunctor Y n).map ((Scheme.Modules.pushforward f).map φ) x) =
      (Scheme.Modules.cohomologyFunctor X n).map φ
        (closedImmersionCohomologyAddEquiv f M n x) :=
  closedEmbeddingCohomologyAddEquiv_naturality f.isClosedEmbedding
    ((Scheme.Modules.toSheaf X).map φ) n x

theorem closedImmersionCohomologyAddEquiv_global_smul
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤))
    (x : Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n) :
    closedImmersionCohomologyAddEquiv f M n (r • x) =
      f.appTop r • closedImmersionCohomologyAddEquiv f M n x := by
  rw [Scheme.Modules.cohomology_smul, Scheme.Modules.cohomology_smul,
    ← Scheme.Modules.pushforward_map_globalSectionsSmul]
  exact closedImmersionCohomologyAddEquiv_naturality f _ n x

variable (R : Type u) [CommRing R]
variable [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]

theorem scheme_appTop_baseRingToGlobalSections
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of R))] (r : R) :
    f.appTop (Scheme.Modules.baseRingToGlobalSections R Y r) =
      Scheme.Modules.baseRingToGlobalSections R X r := by
  have h := congrArg Scheme.Hom.appTop
    (HomIsOver.comp_over (f := f) (S := Spec (CommRingCat.of R)))
  rw [Scheme.Hom.comp_appTop] at h
  simp only [Scheme.Modules.baseRingToGlobalSections_apply]
  exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

noncomputable def closedImmersionCohomologyBaseLinearEquiv
    (f : X ⟶ Y) [IsClosedImmersion f] [f.IsOver (Spec (CommRingCat.of R))]
    (M : X.Modules) (n : ℕ) :
    Scheme.Modules.Cohomology ((Scheme.Modules.pushforward f).obj M) n ≃ₗ[R]
      Scheme.Modules.Cohomology M n where
  toAddEquiv := closedImmersionCohomologyAddEquiv f M n
  map_smul' r x := by
    change closedImmersionCohomologyAddEquiv f M n (r • x) =
      r • closedImmersionCohomologyAddEquiv f M n x
    simp only [Scheme.Modules.base_smul_cohomology]
    rw [
      closedImmersionCohomologyAddEquiv_global_smul,
      scheme_appTop_baseRingToGlobalSections R]

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveRegularCartier

/-!
The actual inclusion O(-D) -> O_X for an effective Cartier divisor on an
integral scheme. It is determined by its composite into rational functions.
The construction uses regular representatives and checks naturality.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable (X : Scheme.{u}) [IsIntegral X]

noncomputable def negativeCartierRegularSection
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (s : Γ((-D).sheaf, U)) : Γ(X, U) :=
  Classical.choose (negativeCartier_section_exists_regular_of_isEffective X D hD U
    (Scheme.Modules.Hom.app (-D).sheafι U s) ((-D).sheafι_app_mem U s))

@[simp]
theorem toRationalFunctions_negativeCartierRegularSection
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (s : Γ((-D).sheaf, U)) :
    Scheme.Modules.Hom.app (toRationalFunctions X) U
      (negativeCartierRegularSection X D hD U s) =
        Scheme.Modules.Hom.app (-D).sheafι U s :=
  Classical.choose_spec (negativeCartier_section_exists_regular_of_isEffective X D hD U
    (Scheme.Modules.Hom.app (-D).sheafι U s) ((-D).sheafι_app_mem U s))

theorem negativeCartierRegularSection_add
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (s t : Γ((-D).sheaf, U)) :
    negativeCartierRegularSection X D hD U (s + t) =
      negativeCartierRegularSection X D hD U s +
        negativeCartierRegularSection X D hD U t := by
  apply toRationalFunctions_app_injective U
  simp

theorem negativeCartierRegularSection_smul
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (r : Γ(X, U)) (s : Γ((-D).sheaf, U)) :
    negativeCartierRegularSection X D hD U (r • s) =
      r • negativeCartierRegularSection X D hD U s := by
  apply toRationalFunctions_app_injective U
  rw [toRationalFunctions_negativeCartierRegularSection]
  calc
    Scheme.Modules.Hom.app (-D).sheafι U (r • s) =
        r • Scheme.Modules.Hom.app (-D).sheafι U s :=
      Scheme.Modules.Hom.app_smul _ _ _
    _ = r • Scheme.Modules.Hom.app (toRationalFunctions X) U
        (negativeCartierRegularSection X D hD U s) := by
      rw [toRationalFunctions_negativeCartierRegularSection]
    _ = Scheme.Modules.Hom.app (toRationalFunctions X) U
        (r • negativeCartierRegularSection X D hD U s) :=
      (Scheme.Modules.Hom.app_smul (toRationalFunctions X) r _).symm

theorem negativeCartierRegularSection_map
    (D : CartierDivisor X) (hD : D.IsEffective) {U V : X.Opens}
    (i : V ⟶ U) (s : Γ((-D).sheaf, U)) :
    negativeCartierRegularSection X D hD V ((-D).sheaf.presheaf.map i.op s) =
      X.presheaf.map i.op (negativeCartierRegularSection X D hD U s) := by
  apply toRationalFunctions_app_injective V
  rw [toRationalFunctions_negativeCartierRegularSection]
  have hι := (-D).sheafι.mapPresheaf.naturality_apply i.op s
  change Scheme.Modules.Hom.app (-D).sheafι V ((-D).sheaf.presheaf.map i.op s) =
    (rationalFunctions X).presheaf.map i.op
      (Scheme.Modules.Hom.app (-D).sheafι U s) at hι
  have hreg := (toRationalFunctions X).mapPresheaf.naturality_apply i.op
    (negativeCartierRegularSection X D hD U s)
  change Scheme.Modules.Hom.app (toRationalFunctions X) V
      (X.presheaf.map i.op (negativeCartierRegularSection X D hD U s)) =
    (rationalFunctions X).presheaf.map i.op
      (Scheme.Modules.Hom.app (toRationalFunctions X) U
        (negativeCartierRegularSection X D hD U s)) at hreg
  rw [toRationalFunctions_negativeCartierRegularSection] at hreg
  exact hι.trans hreg.symm

noncomputable def negativeCartierToUnit
    (D : CartierDivisor X) (hD : D.IsEffective) :
    (-D).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf where
  val.app U := ModuleCat.ofHom
    { toFun := negativeCartierRegularSection X D hD U.unop
      map_add' := negativeCartierRegularSection_add X D hD U.unop
      map_smul' := negativeCartierRegularSection_smul X D hD U.unop }
  val.naturality {U V} i := by
    ext s
    exact negativeCartierRegularSection_map X D hD i.unop s

@[simp]
theorem negativeCartierToUnit_app
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (s : Γ((-D).sheaf, U)) :
    Scheme.Modules.Hom.app (negativeCartierToUnit X D hD) U s =
      negativeCartierRegularSection X D hD U s := rfl

@[simp, reassoc]
theorem negativeCartierToUnit_toRationalFunctions
    (D : CartierDivisor X) (hD : D.IsEffective) :
    negativeCartierToUnit X D hD ≫ toRationalFunctions X = (-D).sheafι := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact toRationalFunctions_negativeCartierRegularSection X D hD U s

theorem negativeCartierToUnit_app_injective
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (negativeCartierToUnit X D hD) U) := by
  intro s t h
  apply (-D).sheafι_app_injective U
  simpa only [negativeCartierToUnit_app,
    ← toRationalFunctions_negativeCartierRegularSection X D hD U] using
      congrArg (Scheme.Modules.Hom.app (toRationalFunctions X) U) h

theorem negativeCartierToUnit_mono
    (D : CartierDivisor X) (hD : D.IsEffective) :
    Mono (negativeCartierToUnit X D hD) := by
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ inferInstance
    (negativeCartierToUnit_toRationalFunctions X D hD)

attribute [instance] negativeCartierToUnit_mono

theorem eq_negativeCartierToUnit
    (D : CartierDivisor X) (hD : D.IsEffective)
    (φ : (-D).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hφ : φ ≫ toRationalFunctions X = (-D).sheafι) :
    φ = negativeCartierToUnit X D hD := by
  apply (cancel_mono (toRationalFunctions X)).mp
  rw [hφ, negativeCartierToUnit_toRationalFunctions]

theorem negativeCartierToUnit_range_iff
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens) (a : Γ(X, U)) :
    a ∈ Set.range (Scheme.Modules.Hom.app (negativeCartierToUnit X D hD) U) ↔
      Scheme.Modules.Hom.app (toRationalFunctions X) U a ∈ (-D).sections U := by
  constructor
  · rintro ⟨s, rfl⟩
    simpa only [negativeCartierToUnit_app,
      toRationalFunctions_negativeCartierRegularSection] using (-D).sheafι_app_mem U s
  · intro ha
    refine ⟨CartierDivisor.sectionMk _ ha, ?_⟩
    apply toRationalFunctions_app_injective U
    simp

end MixedFujita

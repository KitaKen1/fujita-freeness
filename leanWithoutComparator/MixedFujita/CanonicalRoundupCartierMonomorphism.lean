/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalGenericFrameRationalMorphism
public import MixedFujita.SNCIntegerWeilCartierSheaf

/-! Factor the actual generic-frame rational morphism through the actual
Cartier target supplied by the checked unique section representation.
The factorization is natural and linear on all opens, and is a monomorphism
by its actual source field formula. No direct-image invertibility is assumed. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
  (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (heff : E.IsEffective)
  (F : B.Opens) (hgenF : genericPoint B ∈ F)
  [IsIso ((effectiveCartierPushforwardUnitMap q E heff).over F)]
  (C : CartierDivisor B)
  (hdesc : ∀ (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)),
    letI := dominant_preimage_nonempty q U
    ∃! t : Γ(C.sheaf, U),
      (dominantFunctionFieldMap q).hom
        (rationalFunctionsEquiv (X := B) U (Scheme.Modules.Hom.app C.sheafι U t)) =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s))

include hdesc

/-- The generic-frame morphism lands in the actual Cartier section
submodule on every open, including the empty open. -/
theorem canonicalRoundupRationalHom_mem_cartier_sections
    (U : B.Opens) (s : Γ((Scheme.Modules.pushforward q).obj E.sheaf, U)) :
    Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U s ∈
      C.sections U := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    letI := dominant_preimage_nonempty q U
    obtain ⟨t, ht, -⟩ := hdesc U s
    have hEq : Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U s =
        Scheme.Modules.Hom.app C.sheafι U t := by
      apply (rationalFunctionsEquiv (X := B) U).injective
      apply (dominantFunctionFieldMap q).hom.injective
      exact (canonicalRoundupRationalHom_field_pullback q E heff F hgenF U s).trans ht.symm
    rw [hEq]
    exact C.sheafι_app_mem U t
  · have hbot : U = ⊥ := (Opens.not_nonempty_iff_eq_bot U).mp
      (fun ⟨x, hx⟩ => hU ⟨⟨x, hx⟩⟩)
    letI := Scheme.subsingleton_rationalFunctions U hbot
    have hzero : Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U s = 0 :=
      Subsingleton.elim _ _
    rw [hzero]
    exact Submodule.zero_mem _

/-- The actual canonical Cartier-target morphism, constructed by factoring
the already checked rational morphism through its actual Cartier submodule. -/
noncomputable def canonicalRoundupCartierHom :
    (Scheme.Modules.pushforward q).obj E.sheaf ⟶ C.sheaf :=
  C.sheafLift (canonicalRoundupRationalHom q E heff F hgenF)
    (canonicalRoundupRationalHom_mem_cartier_sections q E heff F hgenF C hdesc)

/-- The actual Cartier factorization preserves the inclusion into rational
functions as an equality of sheaf morphisms. -/
theorem canonicalRoundupCartierHom_ι :
    canonicalRoundupCartierHom q E heff F hgenF C hdesc ≫ C.sheafι =
      canonicalRoundupRationalHom q E heff F hgenF := by
  exact C.sheafLift_ι _ _

/-- The actual Cartier image pulls back to the same actual source rational
section on every nonempty base open. -/
theorem canonicalRoundupCartierHom_field_pullback
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    (dominantFunctionFieldMap q).hom
      (rationalFunctionsEquiv (X := B) U
        (Scheme.Modules.Hom.app C.sheafι U
          (Scheme.Modules.Hom.app (canonicalRoundupCartierHom q E heff F hgenF C hdesc) U s))) =
      rationalFunctionsEquiv (X := T) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := dominant_preimage_nonempty q U
  have hι : Scheme.Modules.Hom.app C.sheafι U
      (Scheme.Modules.Hom.app (canonicalRoundupCartierHom q E heff F hgenF C hdesc) U s) =
      Scheme.Modules.Hom.app (canonicalRoundupRationalHom q E heff F hgenF) U s := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      canonicalRoundupCartierHom_ι]
  rw [hι]
  exact canonicalRoundupRationalHom_field_pullback q E heff F hgenF U s

/-- The actual Cartier-target morphism is injective on every open. -/
theorem canonicalRoundupCartierHom_app_injective (U : B.Opens) :
    Function.Injective
      (Scheme.Modules.Hom.app (canonicalRoundupCartierHom q E heff F hgenF C hdesc) U) := by
  intro s t h
  apply canonicalRoundupRationalHom_app_injective q E heff F hgenF U
  have h' := congrArg (Scheme.Modules.Hom.app C.sheafι U) h
  simpa only [canonicalRoundupCartierHom, CartierDivisor.sheafι_app_sheafLift] using h'

/-- The actual Cartier-target morphism is a monomorphism of module sheaves. -/
theorem canonicalRoundupCartierHom_mono :
    Mono (canonicalRoundupCartierHom q E heff F hgenF C hdesc) :=
  (SheafOfModules.forget _).mono_of_mono_map
    (PresheafOfModules.mono_of_injective (fun V =>
      canonicalRoundupCartierHom_app_injective q E heff F hgenF C hdesc V.unop))

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierEffectivity
public import MixedFujita.HironakaSNCModelExistence

/-!
Convert coefficient conditions at primes specializing over a base point into
an actual Cartier unit section over an actual inverse-image neighbourhood.
Finite Weil support removes precisely the negative components. Normal Hartogs
supplies the actual local regular equations; no properness is required.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- On any actual open, the distinguished rational unit is a Cartier section
exactly when all codimension-one coefficients on that open are nonnegative. -/
theorem normal_cartier_one_mem_sections_iff_coefficients_nonneg_on_open
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (C : CartierDivisor X) (U : X.Opens) :
    Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U)) ∈ C.sections U ↔
      ∀ t : CodimensionOnePoint X, (t : X) ∈ U → 0 ≤ cartierCoefficient C (t : X) := by
  constructor
  · intro hs t ht
    letI : Nonempty U := ⟨⟨(t : X), ht⟩⟩
    obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt (t : X)
    have hreg := (CartierDivisor.mem_sections.mp hs) (t : X) ht f hf
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one] at hreg
    exact cartierCoefficient_nonneg_of_mem_range hf hreg
  · intro h
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := C.exists_isLocalEquationAt x
    obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    letI : Nonempty V := ⟨⟨x, hxV⟩⟩
    let W : X.Opens := V ⊓ U
    have hxW : x ∈ W := ⟨hxV, hx⟩
    letI : Nonempty W := ⟨⟨x, hxW⟩⟩
    obtain ⟨s, hs⟩ := OAI.RelativeDenominators.exists_section_of_ord_nonneg X hnorm W
      (f : X.functionField) (Units.ne_zero f) (by
        intro z hz hcod
        rw [← cartierCoefficient_eq_ord
          (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV hz.1)]
        exact h ⟨z, hcod⟩ hz.2)
    refine ⟨f, hf, ?_⟩
    rw [Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one]
    exact ⟨X.presheaf.germ W x hxW s,
      (X.algebraMap_germ_eq_germToFunctionField hxW s).trans hs⟩

/-- Finite negative prime support identifies actual unit sections near a base
point with the coefficient conditions at exactly the primes specializing there. -/
theorem exists_base_neighborhood_one_mem_cartier_sections_iff
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {Y : Scheme.{u}} (g : X ⟶ Y) (η : Y) (C : CartierDivisor X) :
    (∃ U : Y.Opens, η ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) (g ⁻¹ᵁ U)
        (1 : Γ(X, g ⁻¹ᵁ U)) ∈ C.sections (g ⁻¹ᵁ U)) ↔
      ∀ t : CodimensionOnePoint X, η ∈ closure ({g (t : X)} : Set Y) →
        0 ≤ cartierCoefficient C (t : X) := by
  classical
  constructor
  · rintro ⟨U, hηU, hs⟩ t ht
    apply (normal_cartier_one_mem_sections_iff_coefficients_nonneg_on_open hnorm C _).mp hs t
    exact (specializes_iff_mem_closure.mpr ht).mem_open U.isOpen hηU
  · intro h
    let bad := C.toWeilDivisor.support.filter
      (fun t : CodimensionOnePoint X => ¬ 0 ≤ cartierCoefficient C (t : X))
    let B : Set Y := ⋃ t ∈ bad, closure ({g (t : X)} : Set Y)
    have hclosed : IsClosed B := isClosed_biUnion_finset (fun _ _ => isClosed_closure)
    let U : Y.Opens := ⟨Bᶜ, hclosed.isOpen_compl⟩
    have hηU : η ∈ U := by
      intro hbad
      obtain ⟨t, ht, hηt⟩ := Set.mem_iUnion₂.mp hbad
      exact (Finset.mem_filter.mp ht).2 (h t hηt)
    refine ⟨U, hηU,
      (normal_cartier_one_mem_sections_iff_coefficients_nonneg_on_open hnorm C _).mpr ?_⟩
    intro t ht
    by_contra hneg
    have hne : C.toWeilDivisor t ≠ 0 := by
      change WeilDivisor.coeff C.toWeilDivisor t ≠ 0
      rw [cartier_toWeilDivisor_coeff_eq_cartierCoefficient]
      omega
    have hbad : t ∈ bad := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne, hneg⟩
    exact ht (Set.mem_iUnion₂.mpr ⟨t, hbad, subset_closure (Set.mem_singleton _)⟩)

end MixedFujita

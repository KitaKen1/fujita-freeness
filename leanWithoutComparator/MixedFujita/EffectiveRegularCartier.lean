/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularEquationCartier
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective

/-!
Regular local equations give effectivity in Tau Ceti's actual predicate.
On a chart carrying a nonzero regular equation f, the regular functions
that are sections of O(-D) form exactly the principal ideal (f).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable (X : Scheme.{u}) [IsIntegral X]

theorem cartier_isEffective_of_regularEquations
    (D : CartierDivisor X) {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (f : ∀ i, Γ(X, U i)) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i, (cartierDivisorSheaf X).1.map
      (homOfLE (show U i ≤ ⊤ from le_top)).op D =
        rationalUnitClass X (U i)
          (Additive.ofMul (regularEquationRationalUnit X (U i) (f i) (hf i)))) :
    D.IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
  refine ⟨regularEquationRationalUnit X (U i) (f i) (hf i), ?_, ?_⟩
  · exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hD i).symm hi
  · exact regularEquationRationalUnit_mem_stalk_range X _ _ _ x hi

theorem cartier_existsUnique_effective_of_regularEquations
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (f : ∀ i, Γ(X, U i)) (hf : ∀ i, f i ≠ 0)
    (htransition : ∀ i j, ∃ w : Γ(X, U i ⊓ U j)ˣ,
      X.presheaf.map (homOfLE inf_le_left).op (f i) =
        (w : Γ(X, U i ⊓ U j)) * X.presheaf.map (homOfLE inf_le_right).op (f j)) :
    ∃! D : CartierDivisor X,
      (∀ i, (cartierDivisorSheaf X).1.map
        (homOfLE (show U i ≤ ⊤ from le_top)).op D =
          rationalUnitClass X (U i)
            (Additive.ofMul (regularEquationRationalUnit X (U i) (f i) (hf i)))) ∧
      D.IsEffective := by
  obtain ⟨D, hD, huniq⟩ := cartierDivisor_existsUnique_of_regularEquations
    X U hcover f hf htransition
  exact ⟨D, ⟨hD, cartier_isEffective_of_regularEquations X D U hcover f hf hD⟩,
    fun E hE => huniq E hE.1⟩

theorem negativeCartier_regularSection_mem_iff (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (f : Γ(X, U)) (hf : f ≠ 0)
    (hD : rationalUnitClass X U
      (Additive.ofMul (regularEquationRationalUnit X U f hf)) = D |_ U)
    (s : Γ(X, U)) :
    Scheme.Modules.Hom.app (toRationalFunctions X) U s ∈ (-D).sections U ↔
      s ∈ Ideal.span ({f} : Set Γ(X, U)) := by
  have hneg : rationalUnitClass X U
      (Additive.ofMul (regularEquationRationalUnit X U f hf)⁻¹) = (-D) |_ U := by
    rw [ofMul_inv, map_neg, hD]
    simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_neg]
  rw [CartierDivisor.mem_sections_iff_of_rationalUnitClass_eq le_rfl hneg,
    rationalFunctionsEquiv_toRationalFunctions_app, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply X.germToFunctionField_injective U
    rw [(X.germToFunctionField U).hom.map_mul, ha]
    change X.germToFunctionField U s =
      (regularEquationRationalUnit X U f hf : X.functionField) *
        (((regularEquationRationalUnit X U f hf)⁻¹ : X.functionField) *
          X.germToFunctionField U s)
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [ha, (X.germToFunctionField U).hom.map_mul]
    change X.germToFunctionField U a =
      ((regularEquationRationalUnit X U f hf)⁻¹ : X.functionField) *
        ((regularEquationRationalUnit X U f hf : X.functionField) *
          X.germToFunctionField U a)
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

theorem negativeCartier_section_exists_regular_of_isEffective
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.Opens)
    (s : Γ(rationalFunctions X, U)) (hs : s ∈ (-D).sections U) :
    ∃ a : Γ(X, U), Scheme.Modules.Hom.app (toRationalFunctions X) U a = s := by
  rcases U.1.eq_empty_or_nonempty with hU | hU
  · have := subsingleton_rationalFunctions (X := X) U (SetLike.ext' hU)
    exact ⟨0, Subsingleton.elim _ _⟩
  · let : Nonempty U := by simpa using hU
    have hregular : ∀ (x : X) (hx : x ∈ U), rationalFunctionsEquiv U s ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
      intro x hx
      obtain ⟨f, hf, hfr⟩ := CartierDivisor.isEffective_iff_exists.mp hD x
      have hir := CartierDivisor.mem_sections.mp hs x hx f⁻¹ hf.inv
      have hm := Subring.mul_mem _ hfr hir
      simpa! only [← mul_assoc, Units.mul_inv, one_mul] using hm
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range hregular
    refine ⟨a, ?_⟩
    apply (rationalFunctionsEquiv U).injective
    rw [rationalFunctionsEquiv_toRationalFunctions_app, ha]

end MixedFujita

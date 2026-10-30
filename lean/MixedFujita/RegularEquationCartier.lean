/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Basic
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Nonzero regular equations on an integral scheme define actual Cartier
divisors when their ratios are regular units on overlaps. The construction
uses the Cartier quotient sheaf and its unique gluing property. It does not
assert relative effectivity or identify a closed subscheme with the divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable (X : Scheme.{u}) [IsIntegral X]

theorem integral_opens_inter_nonempty (U V : X.Opens) [Nonempty U] [Nonempty V] :
    Nonempty (U ⊓ V : X.Opens) := by
  rcases nonempty_preirreducible_inter U.isOpen V.isOpen
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty U))
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty V)) with ⟨x, hx⟩
  exact ⟨⟨x, hx⟩⟩

theorem germToFunctionField_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (f : Γ(X, U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op f) =
      X.germToFunctionField U f := by
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ f

noncomputable def regularEquationRationalUnit (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (hf : f ≠ 0) : X.functionFieldˣ :=
  Units.mk0 (X.germToFunctionField U f) (by
    intro h
    apply hf
    apply X.germToFunctionField_injective U
    simpa using h)

@[simp]
theorem regularEquationRationalUnit_val (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (hf : f ≠ 0) :
    (regularEquationRationalUnit X U f hf : X.functionField) =
      X.germToFunctionField U f := rfl

theorem regularEquationRationalUnit_mem_stalk_range (U : X.Opens) [Nonempty U]
    (f : Γ(X, U)) (hf : f ≠ 0) (x : X) (hx : x ∈ U) :
    (regularEquationRationalUnit X U f hf : X.functionField) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  refine ⟨X.presheaf.germ U x hx f, ?_⟩
  exact X.algebraMap_germ_eq_germToFunctionField hx f

theorem regularEquation_germ_mem_nonZeroDivisors (U : X.Opens)
    (f : Γ(X, U)) (hf : f ≠ 0) (x : X) (hx : x ∈ U) :
    X.presheaf.germ U x hx f ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  apply hf
  apply germ_injective_of_isIntegral X x hx
  simpa using h

theorem rationalUnitClass_eq_of_regularUnit_mul (U : X.Opens) [Nonempty U]
    (a b : X.functionFieldˣ) (w : Γ(X, U)ˣ)
    (h : a = Units.map (X.germToFunctionField U).hom w * b) :
    rationalUnitClass X U (Additive.ofMul a) =
      rationalUnitClass X U (Additive.ofMul b) := by
  rw [h]
  change rationalUnitClass X U
    (Additive.ofMul (Units.map (X.germToFunctionField U).hom w) + Additive.ofMul b) = _
  rw [map_add, rationalUnitClass_germToFunctionField_eq_zero, zero_add]

theorem regularEquationRationalUnit_eq_of_overlap
    {U V : X.Opens} [Nonempty U] [Nonempty V]
    (f : Γ(X, U)) (hf : f ≠ 0) (g : Γ(X, V)) (hg : g ≠ 0)
    (w : Γ(X, U ⊓ V)ˣ)
    (h : X.presheaf.map (homOfLE inf_le_left).op f =
      (w : Γ(X, U ⊓ V)) * X.presheaf.map (homOfLE inf_le_right).op g) :
    letI := integral_opens_inter_nonempty X U V
    regularEquationRationalUnit X U f hf =
      Units.map (X.germToFunctionField (U ⊓ V)).hom w *
        regularEquationRationalUnit X V g hg := by
  let := integral_opens_inter_nonempty X U V
  apply Units.ext
  change X.germToFunctionField U f =
    X.germToFunctionField (U ⊓ V) w * X.germToFunctionField V g
  rw [← germToFunctionField_restrict X (U := U) (V := U ⊓ V) inf_le_left f,
    ← germToFunctionField_restrict X (U := V) (V := U ⊓ V) inf_le_right g, h]
  exact (X.germToFunctionField (U ⊓ V)).hom.map_mul _ _

theorem cartierDivisor_existsUnique_of_rationalUnits
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (g : ι → X.functionFieldˣ)
    (htransition : ∀ i j, letI := integral_opens_inter_nonempty X (U i) (U j)
      ∃ w : Γ(X, U i ⊓ U j)ˣ,
        g i = Units.map (X.germToFunctionField (U i ⊓ U j)).hom w * g j) :
    ∃! D : CartierDivisor X, ∀ i,
      (cartierDivisorSheaf X).1.map (homOfLE (show U i ≤ ⊤ from le_top)).op D =
        rationalUnitClass X (U i) (Additive.ofMul (g i)) := by
  let sf := fun i => rationalUnitClass X (U i) (Additive.ofMul (g i))
  have hcompat : TopCat.Presheaf.IsCompatible (cartierDivisorSheaf X).1 U sf := by
    intro i j
    let := integral_opens_inter_nonempty X (U i) (U j)
    obtain ⟨w, hw⟩ := htransition i j
    change (sf i) |_ (U i ⊓ U j) = (sf j) |_ (U i ⊓ U j)
    simp only [sf, rationalUnitClass_restrict]
    exact rationalUnitClass_eq_of_regularUnit_mul X _ _ _ w hw
  exact (cartierDivisorSheaf X).existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) (by rw [hcover]) sf hcompat

theorem cartierDivisor_existsUnique_of_regularEquations
    {ι : Type*} (U : ι → X.Opens) [∀ i, Nonempty (U i)]
    (hcover : iSup U = ⊤) (f : ∀ i, Γ(X, U i)) (hf : ∀ i, f i ≠ 0)
    (htransition : ∀ i j, ∃ w : Γ(X, U i ⊓ U j)ˣ,
      X.presheaf.map (homOfLE inf_le_left).op (f i) =
        (w : Γ(X, U i ⊓ U j)) * X.presheaf.map (homOfLE inf_le_right).op (f j)) :
    ∃! D : CartierDivisor X, ∀ i,
      (cartierDivisorSheaf X).1.map (homOfLE (show U i ≤ ⊤ from le_top)).op D =
        rationalUnitClass X (U i)
          (Additive.ofMul (regularEquationRationalUnit X (U i) (f i) (hf i))) := by
  apply cartierDivisor_existsUnique_of_rationalUnits X U hcover
    (fun i => regularEquationRationalUnit X (U i) (f i) (hf i))
  intro i j
  obtain ⟨w, hw⟩ := htransition i j
  exact ⟨w, regularEquationRationalUnit_eq_of_overlap X _ _ _ _ w hw⟩

end MixedFujita

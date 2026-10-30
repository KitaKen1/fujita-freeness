/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SemiampleIitakaZero

/-!
Any prescribed nonzero rational function is a local equation of any Cartier divisor on a dense
open subset of an integral scheme. At the generic point all nonzero rational functions differ by
a unit of its stalk. Local equations persist on open neighbourhoods.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- Every nonzero rational function is a local equation at the generic point. -/
theorem cartier_isLocalEquationAt_genericPoint (D : CartierDivisor Y) (f : Y.functionFieldˣ) :
    D.IsLocalEquationAt (genericPoint Y) f := by
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt (genericPoint Y)
  apply isLocalEquationAt_of_eq_unit_mul hg (g * f⁻¹)
  simp only [RingHom.algebraMap_toAlgebra]
  rw [Y.presheaf.stalkSpecializes_refl]
  simp

/-- The locus on which a fixed rational function is a local equation is open. -/
theorem isOpen_cartier_localEquation_locus (D : CartierDivisor Y) (f : Y.functionFieldˣ) :
    IsOpen {y : Y | D.IsLocalEquationAt y f} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hx
  exact ⟨U, fun y hy => CartierDivisor.isLocalEquationAt_iff.mpr ⟨U, hy, hU⟩, U.isOpen, hxU⟩

/-- Intersecting a nonempty open with a prescribed local-equation locus stays nonempty and dense.
This supplies a boundary-free open inside a fixed smooth chart without source smoothness. -/
theorem exists_dense_open_localEquation (D : CartierDivisor Y) (f : Y.functionFieldˣ)
    (U : Y.Opens) (hU : Nonempty U) :
    ∃ V : Y.Opens, V ≤ U ∧ Nonempty V ∧ Dense (V : Set Y) ∧
      ∀ y ∈ V, D.IsLocalEquationAt y f := by
  let W : Y.Opens := ⟨{y : Y | D.IsLocalEquationAt y f}, isOpen_cartier_localEquation_locus D f⟩
  have : Nonempty U := hU
  have hgen : genericPoint Y ∈ U ⊓ W :=
    ⟨Scheme.genericPoint_mem U, cartier_isLocalEquationAt_genericPoint D f⟩
  refine ⟨U ⊓ W, inf_le_left, ⟨⟨genericPoint Y, hgen⟩⟩, ?_, fun y hy => hy.2⟩
  exact (U ⊓ W).isOpen.dense ⟨genericPoint Y, hgen⟩

end MixedFujita

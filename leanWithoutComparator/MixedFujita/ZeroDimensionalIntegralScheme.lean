/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Topology.KrullDimension

/-! An actual integral scheme of topological Krull dimension zero has
only its generic point. No projectivity, smoothness, base field or
Noetherian hypothesis is needed. -/

@[expose] public section
open AlgebraicGeometry TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem zeroDimensional_integral_point_eq_generic
    (hdim : topologicalKrullDim X = 0) (x : X) : x = genericPoint X := by
  let Z : IrreducibleCloseds X := ⟨closure ({x} : Set X), isIrreducible_singleton.closure,
    isClosed_closure⟩
  let U : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hall : ∀ C : IrreducibleCloseds X, IsMax C :=
    Order.krullDim_nonpos_iff_forall_isMax.mp (by change topologicalKrullDim X ≤ 0; rw [hdim])
  have hZU : Z ≤ U := Set.subset_univ _
  have hUZ : U ≤ Z := hall Z hZU
  have heq : Z = U := le_antisymm hZU hUZ
  have hclosure : closure ({x} : Set X) = Set.univ := congrArg (fun C : IrreducibleCloseds X => (C : Set X)) heq
  exact (show IsGenericPoint x Set.univ from hclosure).eq (genericPoint_spec X)

theorem zeroDimensional_integral_subsingleton (hdim : topologicalKrullDim X = 0) : Subsingleton X :=
  ⟨fun x y => (zeroDimensional_integral_point_eq_generic hdim x).trans
    (zeroDimensional_integral_point_eq_generic hdim y).symm⟩

end MixedFujita

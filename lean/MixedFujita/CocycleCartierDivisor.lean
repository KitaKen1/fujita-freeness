/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularEquationCartier
public import MixedFujita.CartierCechBaseChange

/-!
Cartier divisors from cocycles of units (step 10, R4-7).

Let `X` be an integral scheme with a finite open cover `U_0, …, U_N` and units `w_{ij}` on
`U_i ⊓ U_j` with `w_{ij} w_{j0} = w_{i0}` on `U_i ⊓ U_j ⊓ U_0`. The germs `g_i = w_{i0}` in the
function field (`cocycleEquation`) satisfy `g_i = w_{ij} g_j` (`cocycleEquation_transition`), so
they are the local equations of a Cartier divisor (`exists_cartierDivisor_of_cocycle`, glued by
`cartierDivisor_existsUnique_of_rationalUnits`). The cocycle pulls back along any morphism
(`pullbackCocycle`, `pullbackCocycle_spec`), with the same transition relation for the pulled-back
local equations; these are the hypotheses `huX`, `huY` of check 499 (`cocycle_huX`,
`cocycle_huY`).

For the closure `T_A`, a cocycle of transition functions of `Q` spread out from `T_K` gives the
divisor `Q_A` on `T_A` and `Q_κ` on the fibre `T_κ`, whose Čech complexes are compared by check 499.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section Cocycle

variable {X : Scheme.{u}} [IsIntegral X] {N : ℕ} (U : Fin (N + 1) → X.Opens)
  [hU : ∀ i, Nonempty (U i)] (w : ∀ i j, Γ(X, U i ⊓ U j)ˣ)

/-- The cocycle condition `w_{ij} w_{j0} = w_{i0}` on the triple intersections. -/
def IsCocycleZero : Prop :=
  ∀ i j, X.presheaf.map (homOfLE (show U i ⊓ U j ⊓ U 0 ≤ U i ⊓ U j from inf_le_left)).op
      (w i j : Γ(X, U i ⊓ U j)) *
    X.presheaf.map (homOfLE (show U i ⊓ U j ⊓ U 0 ≤ U j ⊓ U 0 from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op (w j 0 : Γ(X, U j ⊓ U 0)) =
    X.presheaf.map (homOfLE (show U i ⊓ U j ⊓ U 0 ≤ U i ⊓ U 0 from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op (w i 0 : Γ(X, U i ⊓ U 0))

/-- The local equation `g_i = w_{i0}` on `U_i`, in the function field. -/
noncomputable def cocycleEquation (i : Fin (N + 1)) : X.functionFieldˣ :=
  letI := integral_opens_inter_nonempty X (U i) (U 0)
  Units.map (X.germToFunctionField (U i ⊓ U 0)).hom (w i 0)

include hU in
/-- **The local equations of a cocycle have the cocycle as transition functions.** -/
theorem cocycleEquation_transition (hw : IsCocycleZero U w) (i j : Fin (N + 1)) :
    letI := integral_opens_inter_nonempty X (U i) (U j)
    (cocycleEquation U w i : X.functionField) =
      X.germToFunctionField (U i ⊓ U j) (w i j : Γ(X, U i ⊓ U j)) *
        (cocycleEquation U w j : X.functionField) := by
  let _ := integral_opens_inter_nonempty X (U i) (U j)
  let _ := integral_opens_inter_nonempty X (U i) (U 0)
  let _ := integral_opens_inter_nonempty X (U j) (U 0)
  let _ := integral_opens_inter_nonempty X (U i ⊓ U j) (U 0)
  change X.germToFunctionField (U i ⊓ U 0) (w i 0 : Γ(X, U i ⊓ U 0)) =
    X.germToFunctionField (U i ⊓ U j) (w i j : Γ(X, U i ⊓ U j)) *
      X.germToFunctionField (U j ⊓ U 0) (w j 0 : Γ(X, U j ⊓ U 0))
  rw [← germToFunctionField_restrict X (show U i ⊓ U j ⊓ U 0 ≤ U i ⊓ U 0 from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right),
    ← germToFunctionField_restrict X (show U i ⊓ U j ⊓ U 0 ≤ U i ⊓ U j from inf_le_left),
    ← germToFunctionField_restrict X (show U i ⊓ U j ⊓ U 0 ≤ U j ⊓ U 0 from
      le_inf (inf_le_left.trans inf_le_right) inf_le_right),
    ← hw i j, map_mul]

include hU in
/-- **A cocycle of units on a cover defines a Cartier divisor** with local equations `w_{i0}`. -/
theorem exists_cartierDivisor_of_cocycle (hw : IsCocycleZero U w) (hcover : iSup U = ⊤) :
    ∃ D : CartierDivisor X, ∀ i, ∀ y ∈ U i, D.IsLocalEquationAt y (cocycleEquation U w i) := by
  obtain ⟨D, hD, -⟩ := cartierDivisor_existsUnique_of_rationalUnits X U hcover
    (cocycleEquation U w) (fun i j => ⟨w i j, Units.ext (cocycleEquation_transition U w hw i j)⟩)
  exact ⟨D, fun i y hy => CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hD i).symm hy⟩

include hU in
/-- The transition relation in the form of check 499 (`huX`). -/
theorem cocycle_huX (hw : IsCocycleZero U w) :
    ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (w i j : Γ(X, U i ⊓ U j)) *
        cocycleEquation U w j = cocycleEquation U w i := by
  intro i j _
  exact (cocycleEquation_transition U w hw i j).symm

end Cocycle

section Pullback

variable {X Y : Scheme.{u}} {N : ℕ} (U : Fin (N + 1) → X.Opens)
  (g : Y ⟶ X) (w : ∀ i j, Γ(X, U i ⊓ U j)ˣ)

/-- The pulled-back cocycle on `g⁻¹U_i ⊓ g⁻¹U_j`. -/
noncomputable def pullbackCocycle (i j : Fin (N + 1)) :
    Γ(Y, (fun k => g ⁻¹ᵁ U k) i ⊓ (fun k => g ⁻¹ᵁ U k) j)ˣ :=
  Units.map (g.appLE (U i ⊓ U j) (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j) le_rfl).hom.toMonoidHom (w i j)

theorem pullbackCocycle_val (i j : Fin (N + 1)) :
    (pullbackCocycle U g w i j : Γ(Y, g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j)) =
      baseChangeTransition (g := g) U (fun i j => (w i j : Γ(X, U i ⊓ U j))) i j :=
  rfl

/-- **The pulled-back cocycle is a cocycle.** -/
theorem pullbackCocycle_spec (hw : IsCocycleZero U w) :
    IsCocycleZero (fun k => g ⁻¹ᵁ U k) (pullbackCocycle U g w) := by
  intro i j
  have h := congrArg (g.appLE (U i ⊓ U j ⊓ U 0) (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ⊓ g ⁻¹ᵁ U 0) le_rfl) (hw i j)
  rw [map_mul, appLE_of_restrict_apply, appLE_of_restrict_apply, appLE_of_restrict_apply] at h
  simp only [pullbackCocycle, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  rw [appLE_restrict_apply, appLE_restrict_apply, appLE_restrict_apply]
  exact h

/-- The transition relation of the pulled-back cocycle in the form of check 499 (`huY`). -/
theorem cocycle_huY [IsIntegral Y] [∀ i, Nonempty (g ⁻¹ᵁ U i)] (hw : IsCocycleZero U w) :
    ∀ i j, ∀ (_ : Nonempty (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j : Y.Opens)),
      Y.germToFunctionField (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j)
          (baseChangeTransition (g := g) U (fun i j => (w i j : Γ(X, U i ⊓ U j))) i j) *
        cocycleEquation (fun k => g ⁻¹ᵁ U k) (pullbackCocycle U g w) j =
      cocycleEquation (fun k => g ⁻¹ᵁ U k) (pullbackCocycle U g w) i :=
  cocycle_huX (fun k => g ⁻¹ᵁ U k) (pullbackCocycle U g w) (pullbackCocycle_spec U g w hw)

end Pullback

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreGlobalSectionsRank
public import MixedFujita.AffineSectionsBaseChange

/-!
Functions on a flat scheme inject into the functions of its fibres (step 10, R4-3).

Let `X` be flat over a ring `A` and `Y = X ×_A L` its fibre over an `A`-algebra `L` with `A → L`
injective (for the closure `T_A` and the field `K ⊇ A`). For an affine open `W`, pulling back
functions `Γ(X, W) → Γ(Y, g⁻¹W)` is injective (`appLE_injective_of_flat`): it is
`Γ(X, W) → L ⊗_A Γ(X, W) ≅ Γ(Y, g⁻¹W)` (check 497), injective since `Γ(X, W)` is flat over `A`
(check 516). Identities among functions on `X` can therefore be checked on `Y`
(`eq_of_appLE_eq`), and a function whose pullback is a unit with an inverse coming from `X` is a
unit (`isUnit_of_appLE_mul_eq_one`).

This is how the identities of the transition functions, Jacobians and units on `T_K` spread to
the closure `T_A` once the finitely many functions involved come from `T_A`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] structureSectionsAlgebra sectionsRingModule

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of L))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A L))))

include H in
/-- **Pulling back functions on an affine open of a flat scheme to a fibre is injective.** -/
theorem appLE_injective_of_flat [Flat (X ↘ Spec (CommRingCat.of A))]
    (hL : Function.Injective (algebraMap A L)) {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Injective (g.appLE W (g ⁻¹ᵁ W) le_rfl) := by
  have hflat : Module.Flat A ((CohomologyAux.unitModule X).presheaf.obj (op W)) :=
    flat_sections_of_flat hW
  have : Module.Flat A Γ(X, W) := hflat
  have hinj : Function.Injective fun b : Γ(X, W) => (1 : L) ⊗ₜ[A] b := by
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := Γ(X, W))
      (Algebra.linearMap A L) hL
    have h2 : (fun b : Γ(X, W) => (1 : L) ⊗ₜ[A] b) =
        ((Algebra.linearMap A L).rTensor Γ(X, W)) ∘ (TensorProduct.lid A Γ(X, W)).symm := by
      funext b
      simp
    rw [h2]
    exact h1.comp (TensorProduct.lid A Γ(X, W)).symm.injective
  intro a b hab
  apply hinj
  apply (sectionsBaseChangeEquiv H hW).injective
  simp only [sectionsBaseChangeEquiv_tmul, map_one, one_mul]
  exact hab

include H in
/-- **Identities of functions on a flat scheme can be checked on a fibre.** -/
theorem eq_of_appLE_eq [Flat (X ↘ Spec (CommRingCat.of A))]
    (hL : Function.Injective (algebraMap A L)) {W : X.Opens} (hW : IsAffineOpen W)
    {a b : Γ(X, W)} (hab : g.appLE W (g ⁻¹ᵁ W) le_rfl a = g.appLE W (g ⁻¹ᵁ W) le_rfl b) :
    a = b :=
  appLE_injective_of_flat H hL hW hab

include H in
/-- A function whose pullback has an inverse pulled back from the scheme is a unit. -/
theorem isUnit_of_appLE_mul_eq_one [Flat (X ↘ Spec (CommRingCat.of A))]
    (hL : Function.Injective (algebraMap A L)) {W : X.Opens} (hW : IsAffineOpen W)
    {a b : Γ(X, W)}
    (hab : g.appLE W (g ⁻¹ᵁ W) le_rfl a * g.appLE W (g ⁻¹ᵁ W) le_rfl b = 1) : IsUnit a := by
  have h : a * b = 1 := by
    apply eq_of_appLE_eq H hL hW
    rw [map_mul, map_one]
    exact hab
  exact isUnit_iff_exists_inv.2 ⟨b, h⟩

end MixedFujita

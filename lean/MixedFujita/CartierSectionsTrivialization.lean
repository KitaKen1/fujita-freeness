/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechTensorExact
public import MixedFujita.RegularEquationCartier
public import TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf

/-!
Trivializations of `𝒪_X(D)` by local equations (step 10, R4).

On an integral scheme, a section of `𝒪_X(D)` over a nonempty open `V` is a rational function
(`cartierSectionRationalOn`, injective, unchanged by restriction). If `g` is a local equation of
`D` at every point of `V`, multiplication by `g` identifies the sections over `V` with `Γ(X, V)`
(`cartierSectionsTrivialization`, characterized by `germToFunctionField_cartierSectionsTrivialization`).
For `W ≤ V` with a local equation `g'` on `W`, the trivializations differ by the unit `g'/g`
(`cartierSectionsTrivialization_restrict`). These are the first-vertex trivializations of Čech
cochains of `𝒪_X(D)` used to compare the Čech complexes of a model and of its fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsIntegral X]

/-- **The rational function of a section of `𝒪_X(D)`** over a nonempty open. -/
noncomputable def cartierSectionRationalOn (D : CartierDivisor X) (V : X.Opens) [Nonempty V] :
    Γ(D.sheaf, V) →+ X.functionField :=
  (rationalFunctionsEquiv V).toLinearMap.toAddMonoidHom.comp
    (Scheme.Modules.Hom.app D.sheafι V).hom

theorem cartierSectionRationalOn_apply (D : CartierDivisor X) (V : X.Opens) [Nonempty V]
    (s : Γ(D.sheaf, V)) :
    cartierSectionRationalOn D V s =
      rationalFunctionsEquiv V (Scheme.Modules.Hom.app D.sheafι V s) :=
  rfl

theorem cartierSectionRationalOn_injective (D : CartierDivisor X) (V : X.Opens) [Nonempty V] :
    Function.Injective (cartierSectionRationalOn D V) :=
  (rationalFunctionsEquiv V).injective.comp (D.sheafι_app_injective V)

/-- **Restriction does not change the rational function.** -/
theorem cartierSectionRationalOn_restrict (D : CartierDivisor X) {V W : X.Opens} [Nonempty V]
    [Nonempty W] (h : W ≤ V) (s : Γ(D.sheaf, V)) :
    cartierSectionRationalOn D W (D.sheaf.presheaf.map (homOfLE h).op s) =
      cartierSectionRationalOn D V s := by
  rw [cartierSectionRationalOn_apply, cartierSectionRationalOn_apply]
  have hnat := congrArg (fun f => (ConcreteCategory.hom f) s)
    (D.sheafι.mapPresheaf.naturality (homOfLE h).op)
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hnat
  change rationalFunctionsEquiv W (Scheme.Modules.Hom.app D.sheafι W
    (D.sheaf.presheaf.map (homOfLE h).op s)) = _
  rw [hnat, rationalFunctionsEquiv_map]

/-- A section times a local equation is regular. -/
theorem exists_trivialization_section (D : CartierDivisor X) {V : X.Opens} [Nonempty V]
    {g : X.functionFieldˣ} (hg : ∀ y ∈ V, D.IsLocalEquationAt y g) (s : Γ(D.sheaf, V)) :
    ∃ a : Γ(X, V), X.germToFunctionField V a = g * cartierSectionRationalOn D V s := by
  have hmem := D.sheafι_app_mem V s
  exact exists_germToFunctionField_eq_of_forall_mem_range fun y hy =>
    CartierDivisor.mem_sections.mp hmem y hy g (hg y hy)

/-- The trivializing map `s ↦ g s`. -/
noncomputable def cartierSectionsTrivializationHom (D : CartierDivisor X) (V : X.Opens)
    [Nonempty V] (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g) :
    Γ(D.sheaf, V) →+ Γ(X, V) :=
  AddMonoidHom.mk' (fun s => (exists_trivialization_section D hg s).choose) fun s t => by
    apply X.germToFunctionField_injective V
    rw [(exists_trivialization_section D hg (s + t)).choose_spec, map_add, map_add,
      (exists_trivialization_section D hg s).choose_spec,
      (exists_trivialization_section D hg t).choose_spec, mul_add]

theorem germToFunctionField_cartierSectionsTrivializationHom (D : CartierDivisor X)
    (V : X.Opens) [Nonempty V] (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g)
    (s : Γ(D.sheaf, V)) :
    X.germToFunctionField V (cartierSectionsTrivializationHom D V g hg s) =
      g * cartierSectionRationalOn D V s :=
  (exists_trivialization_section D hg s).choose_spec

theorem cartierSectionsTrivializationHom_bijective (D : CartierDivisor X) (V : X.Opens)
    [Nonempty V] (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g) :
    Function.Bijective (cartierSectionsTrivializationHom D V g hg) := by
  constructor
  · intro s t hst
    apply cartierSectionRationalOn_injective D V
    have hs := germToFunctionField_cartierSectionsTrivializationHom D V g hg s
    have ht := germToFunctionField_cartierSectionsTrivializationHom D V g hg t
    rw [hst, ht] at hs
    exact (mul_left_cancel₀ (Units.ne_zero g) hs).symm
  · intro a
    have hmem : (rationalFunctionsEquiv V).symm
        ((g⁻¹ : X.functionFieldˣ) * X.germToFunctionField V a) ∈ D.sections V := by
      refine CartierDivisor.mem_sections_iff_exists.mpr fun y hy => ⟨g, hg y hy, ?_⟩
      rw [LinearEquiv.apply_symm_apply, ← mul_assoc, Units.mul_inv, one_mul,
        ← Scheme.algebraMap_germ_eq_germToFunctionField X hy]
      exact RingHom.mem_range_self _ _
    refine ⟨CartierDivisor.sectionMk _ hmem, ?_⟩
    apply X.germToFunctionField_injective V
    rw [germToFunctionField_cartierSectionsTrivializationHom, cartierSectionRationalOn_apply,
      CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply, ← mul_assoc,
      Units.mul_inv, one_mul]

/-- **The trivialization of `𝒪_X(D)` over `V` by a local equation `g`**: `s ↦ g s`. -/
noncomputable def cartierSectionsTrivialization (D : CartierDivisor X) (V : X.Opens) [Nonempty V]
    (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g) : Γ(D.sheaf, V) ≃+ Γ(X, V) :=
  AddEquiv.ofBijective (cartierSectionsTrivializationHom D V g hg)
    (cartierSectionsTrivializationHom_bijective D V g hg)

/-- **The trivialization is multiplication by the local equation.** -/
theorem germToFunctionField_cartierSectionsTrivialization (D : CartierDivisor X) (V : X.Opens)
    [Nonempty V] (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g)
    (s : Γ(D.sheaf, V)) :
    X.germToFunctionField V (cartierSectionsTrivialization D V g hg s) =
      g * cartierSectionRationalOn D V s :=
  germToFunctionField_cartierSectionsTrivializationHom D V g hg s

/-- The rational function of a multiple of a section. -/
theorem cartierSectionRationalOn_smul (D : CartierDivisor X) (V : X.Opens) [Nonempty V]
    (a : Γ(X, V)) (s : Γ(D.sheaf, V)) :
    cartierSectionRationalOn D V (a • s) =
      X.germToFunctionField V a * cartierSectionRationalOn D V s := by
  rw [cartierSectionRationalOn_apply, cartierSectionRationalOn_apply, Scheme.Modules.Hom.app_smul,
    LinearEquiv.map_smul, Algebra.smul_def]
  rfl

/-- **The trivialization is `Γ(X, V)`-linear.** -/
theorem cartierSectionsTrivialization_smul (D : CartierDivisor X) (V : X.Opens) [Nonempty V]
    (g : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g) (a : Γ(X, V))
    (s : Γ(D.sheaf, V)) :
    cartierSectionsTrivialization D V g hg (a • s) = a * cartierSectionsTrivialization D V g hg s := by
  apply X.germToFunctionField_injective V
  rw [germToFunctionField_cartierSectionsTrivialization, cartierSectionRationalOn_smul, map_mul,
    germToFunctionField_cartierSectionsTrivialization, mul_left_comm]

/-- **Restriction in trivializations**: for `W ≤ V` with local equations `g` on `V` and `g'` on
`W`, the trivializations differ by a function `u` on `W` with `u g = g'`. -/
theorem cartierSectionsTrivialization_restrict (D : CartierDivisor X) {V W : X.Opens} [Nonempty V]
    [Nonempty W] (h : W ≤ V) (g g' : X.functionFieldˣ) (hg : ∀ y ∈ V, D.IsLocalEquationAt y g)
    (hg' : ∀ y ∈ W, D.IsLocalEquationAt y g') (u : Γ(X, W))
    (hu : X.germToFunctionField W u * g = g') (s : Γ(D.sheaf, V)) :
    cartierSectionsTrivialization D W g' hg' (D.sheaf.presheaf.map (homOfLE h).op s) =
      u * X.presheaf.map (homOfLE h).op (cartierSectionsTrivialization D V g hg s) := by
  apply X.germToFunctionField_injective W
  rw [germToFunctionField_cartierSectionsTrivialization, cartierSectionRationalOn_restrict,
    map_mul, germToFunctionField_restrict (X := X) h,
    germToFunctionField_cartierSectionsTrivialization, ← hu, mul_assoc]

end MixedFujita

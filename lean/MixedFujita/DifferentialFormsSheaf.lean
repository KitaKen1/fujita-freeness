/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeRhamExteriorDegree
public import MixedFujita.CanonicalDivisor
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import MixedFujita.CanonicalCartierTopLattice

/-!
The sheaves `Ω^b_X` of differential forms (step 10, the sheaves of the de Rham complex).

For an integral scheme `X` over a field `K`, the rational `b`-forms are the `K(X)`-module
`⋀^b Ω[K(X)⁄K]`. As for the sheaf `𝒦_X` of rational functions (TauCeti), the constant sheaf with
this value is the pushforward of the quasi-coherent sheaf `(⋀^b Ω[K(X)⁄K])^~` on `Spec K(X)` along
`Spec K(X) → X` (`rationalFormsSheaf`). Its sections over a nonempty open subset are the rational
`b`-forms (`rationalFormsSectionsEquiv`), compatibly with restriction (`rationalFormsSectionsEquiv_map`):
the morphism `Spec K(X) → X` pulls every nonempty open back to the whole one-point space. A function
on `U` acts through its germ in `K(X)` (`rationalFormsSectionsEquiv_smul`).

A rational form is regular at `x` if it comes from `⋀^b Ω[𝒪_{X,x}⁄K]` (`stalkFormsMap`). The forms
regular at every point of `U` form a `Γ(X, U)`-submodule (`regularFormsSections`), and regularity is
local, so they form a subsheaf of modules (`regularFormsSubmodule`, Mathlib's
`SheafOfModules.Submodule`). This is the sheaf `Ω^b_X` (`differentialFormsSheaf`), with its
inclusion into the rational forms (`differentialFormsInclusion`). A rational form is the value of a
section over `U` iff it is regular at every point of `U` (`exists_regularFormsValue_eq_iff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower

/-- The rational `b`-forms `⋀^b Ω[K(X)⁄K]`. -/
abbrev RationalForms (b : ℕ) : Type u := ⋀[X.functionField]^b Ω[X.functionField⁄K]

/-- The rational `b`-forms as a module over the function field. -/
noncomputable abbrev rationalFormsModule (b : ℕ) : ModuleCat.{u} X.functionField :=
  ModuleCat.of X.functionField (RationalForms K X b)

/-- **The constant sheaf of rational `b`-forms** on an integral scheme. -/
noncomputable def rationalFormsSheaf (b : ℕ) : X.Modules :=
  (Scheme.Modules.pushforward (fromSpecFunctionField X)).obj (tilde (rationalFormsModule K X b))

variable {X}

/-- The global sections of `M^~` on `Spec K(X)` are `M`. -/
noncomputable def tildeTopAddEquiv (M : ModuleCat.{u} X.functionField) :
    Γ(tilde M, ⊤) ≃+ M :=
  (tilde.isoTop M).toLinearEquiv.toAddEquiv.symm

/-- Sections of `M^~` over the preimage of a nonempty open subset are its global sections. -/
noncomputable def tildePreimageAddEquiv (M : ModuleCat.{u} X.functionField) (U : X.Opens)
    [Nonempty U] : Γ(tilde M, (fromSpecFunctionField X) ⁻¹ᵁ U) ≃+ Γ(tilde M, ⊤) :=
  ((Scheme.Modules.presheaf (tilde M)).mapIso
    (eqToIso (congrArg op (fromSpecFunctionField_preimage U)))).addCommGroupIsoToAddEquiv

/-- **Sections of the constant sheaf of rational forms over a nonempty open subset.** -/
noncomputable def rationalFormsSectionsEquiv (b : ℕ) (U : X.Opens) [Nonempty U] :
    Γ(rationalFormsSheaf K X b, U) ≃+ RationalForms K X b :=
  (tildePreimageAddEquiv (rationalFormsModule K X b) U).trans
    (tildeTopAddEquiv (rationalFormsModule K X b))

/-- The identifications commute with restriction: the sheaf is constant. -/
theorem rationalFormsSectionsEquiv_map (b : ℕ) {U V : X.Opens} [Nonempty U] [Nonempty V]
    (i : U ⟶ V) (s : Γ(rationalFormsSheaf K X b, V)) :
    rationalFormsSectionsEquiv K b U ((rationalFormsSheaf K X b).presheaf.map i.op s) =
      rationalFormsSectionsEquiv K b V s := by
  simp only [rationalFormsSectionsEquiv, AddEquiv.trans_apply]
  congr 1

/-- On global sections of `M^~` over `Spec K(X)`, a section of the structure sheaf acts through its
value in `K(X)`. -/
theorem tildeTopAddEquiv_smul (M : ModuleCat.{u} X.functionField) (a : Γ(Spec X.functionField, ⊤))
    (x : Γ(tilde M, ⊤)) :
    tildeTopAddEquiv M (a • x) = (Scheme.ΓSpecIso X.functionField).hom a • tildeTopAddEquiv M x := by
  have h : a • x = ((Scheme.ΓSpecIso X.functionField).hom a) • x := by
    rw [Scheme.Modules.smul_Spec_def]
    congr 1
    rw [Iso.hom_inv_id_apply]
    exact (congrArg (fun φ => φ a)
      (congrArg (fun g => ConcreteCategory.hom g) ((Spec X.functionField).presheaf.map_id _))).symm
  rw [h]
  exact (tilde.isoTop M).toLinearEquiv.symm.map_smul _ x

/-- The structure-sheaf section `f.app U r` restricted back to the whole of `Spec K(X)` is the germ
of `r`. -/
theorem ΓSpecIso_hom_map_fromSpecFunctionField_app (U : X.Opens) [Nonempty U] (r : Γ(X, U)) :
    (Scheme.ΓSpecIso X.functionField).hom ((Spec X.functionField).presheaf.map
        (eqToHom (congrArg op (fromSpecFunctionField_preimage U)))
        ((fromSpecFunctionField X).app U r)) = X.germToFunctionField U r := by
  rw [fromSpecFunctionField_app]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply ((Spec X.functionField).presheaf.map (homOfLE le_top).op),
    ← Functor.map_comp]
  rw [Subsingleton.elim ((homOfLE le_top).op ≫ eqToHom (congrArg op (fromSpecFunctionField_preimage U)))
    (𝟙 _), CategoryTheory.Functor.map_id]
  simp

/-- **The sections of the constant sheaf of rational forms are `Γ(X, U)`-linearly the rational forms**:
a function acts through its germ in `K(X)`. -/
theorem rationalFormsSectionsEquiv_smul (b : ℕ) (U : X.Opens) [Nonempty U] (r : Γ(X, U))
    (s : Γ(rationalFormsSheaf K X b, U)) :
    rationalFormsSectionsEquiv K b U (r • s) =
      X.germToFunctionField U r • rationalFormsSectionsEquiv K b U s := by
  simp only [rationalFormsSectionsEquiv, AddEquiv.trans_apply, tildePreimageAddEquiv]
  rw [← ΓSpecIso_hom_map_fromSpecFunctionField_app U r, ← tildeTopAddEquiv_smul]
  congr 1

section Regular

/-- The map of `b`-forms from the stalk at `x` to the rational forms. -/
noncomputable def stalkFormsMap (b : ℕ) (x : X) :
    (⋀[X.presheaf.stalk x]^b Ω[X.presheaf.stalk x⁄K]) →ₗ[X.presheaf.stalk x] RationalForms K X b :=
  OAI.ReverseLogKodaira.DifferentialBaseChange.exteriorDifferentialMap K K (X.presheaf.stalk x)
    X.functionField b

/-- The rational `b`-forms on `U` regular at every point of `U`. -/
noncomputable def regularFormsSections (b : ℕ) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFormsSheaf K X b, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U), haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    rationalFormsSectionsEquiv K b U s ∈ LinearMap.range (stalkFormsMap K b x)}
  zero_mem' := by
    intro x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro s t hs ht x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add]
    exact Submodule.add_mem _ (hs x hx) (ht x hx)
  smul_mem' := by
    intro r s hs x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨w, hw⟩ := hs x hx
    refine ⟨X.presheaf.germ U x hx r • w, ?_⟩
    rw [rationalFormsSectionsEquiv_smul, map_smul, hw, ← algebraMap_smul X.functionField,
      Scheme.algebraMap_germ_eq_germToFunctionField]

theorem mem_regularFormsSections (b : ℕ) {U : X.Opens} (s : Γ(rationalFormsSheaf K X b, U)) :
    s ∈ regularFormsSections K b U ↔ ∀ (x : X) (hx : x ∈ U), haveI : Nonempty U := ⟨⟨x, hx⟩⟩
      rationalFormsSectionsEquiv K b U s ∈ LinearMap.range (stalkFormsMap K b x) :=
  Iff.rfl

/-- **The regular `b`-forms as a submodule of the sheaf of rational forms.** -/
noncomputable def regularFormsSubmodule (b : ℕ) : (rationalFormsSheaf K X b).Submodule where
  obj U := regularFormsSections K b U.unop
  map {U V} i := fun s hs x hx => by
    have : Nonempty V.unop := ⟨⟨x, hx⟩⟩
    have : Nonempty U.unop := ⟨⟨x, i.unop.le hx⟩⟩
    have h := rationalFormsSectionsEquiv_map K b i.unop s
    change rationalFormsSectionsEquiv K b V.unop
      ((rationalFormsSheaf K X b).presheaf.map i.unop.op s) ∈ _
    rw [h]
    exact hs x (i.unop.le hx)
  isSheaf {U} s hs := by
    intro x hx
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFormsSheaf K X b).presheaf.map i.op s ∈ regularFormsSections K b V := hi
    rw [← rationalFormsSectionsEquiv_map K b i s]
    exact hi' x hxV

/-- **The sheaf `Ω^b_X` of regular differential `b`-forms.** -/
noncomputable def differentialFormsSheaf (b : ℕ) : X.Modules :=
  (regularFormsSubmodule K b).toSheafOfModules

/-- The inclusion of `Ω^b_X` into the constant sheaf of rational `b`-forms. -/
noncomputable def differentialFormsInclusion (b : ℕ) :
    differentialFormsSheaf K b ⟶ rationalFormsSheaf K X b :=
  (regularFormsSubmodule K b).ι

instance differentialFormsInclusion_mono (b : ℕ) : Mono (differentialFormsInclusion K (X := X) b) :=
  inferInstanceAs (Mono (regularFormsSubmodule K b).ι)

/-- The rational form of a regular section over a nonempty open subset. -/
noncomputable def regularFormsValue (b : ℕ) (U : X.Opens) [Nonempty U] :
    regularFormsSections K b U →+ RationalForms K X b :=
  (rationalFormsSectionsEquiv K b U).toAddMonoidHom.comp
    (regularFormsSections K b U).subtype.toAddMonoidHom

theorem regularFormsValue_apply (b : ℕ) (U : X.Opens) [Nonempty U]
    (s : regularFormsSections K b U) :
    regularFormsValue K b U s = rationalFormsSectionsEquiv K b U s := rfl

theorem regularFormsValue_injective (b : ℕ) (U : X.Opens) [Nonempty U] :
    Function.Injective (regularFormsValue K b U) :=
  (rationalFormsSectionsEquiv K b U).injective.comp Subtype.val_injective

/-- **A rational form is the value of a regular section over `U` iff it is regular at every point
of `U`.** -/
theorem exists_regularFormsValue_eq_iff (b : ℕ) (U : X.Opens) [Nonempty U]
    (ω : RationalForms K X b) :
    (∃ s, regularFormsValue K b U s = ω) ↔
      ∀ (x : X) (_ : x ∈ U), ω ∈ LinearMap.range (stalkFormsMap K b x) := by
  constructor
  · rintro ⟨s, rfl⟩ x hx
    exact s.2 x hx
  · intro h
    refine ⟨⟨(rationalFormsSectionsEquiv K b U).symm ω, fun x hx => ?_⟩, ?_⟩
    · rw [AddEquiv.apply_symm_apply]
      exact h x hx
    · rw [regularFormsValue_apply, AddEquiv.apply_symm_apply]

end Regular

end MixedFujita

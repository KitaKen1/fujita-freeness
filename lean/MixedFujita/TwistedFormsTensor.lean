/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedDifferentialForms
public import TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct
public import MixedFujita.CartierCoherentTensor
public import MixedFujita.CoherentAmpleSerreVanishing

/-!
`𝒪_X(E) ⊗ Ω^b_X(F) ≅ Ω^b_X(E + F)` (step 10).

A rational function times a rational form is a rational form (`formsMul`, on each open subset), and
a section of `𝒪_X(E)` times a section of `Ω^b_X(F)` is a section of `Ω^b_X(E + F)`
(`formsMul_mem`). This multiplication is bilinear and commutes with restriction, so it defines a
morphism from the sectionwise tensor product (`twistedTensorPresheafHom`). As in TauCeti's proof of
`𝒪_X(D) ⊗ 𝒪_X(E) ≅ 𝒪_X(D + E)`, on an open subset where `E` has an equation `g` the map
`ω ↦ g⁻¹ ⊗ g ω` is a retraction of the multiplication and shows that it is surjective; so the
multiplication is locally bijective and its sheafification is an isomorphism
(`twistedTensorSheafIso`).

With `Ω^b_X(0) = Ω^b_X` this gives `𝒪_X(E) ⊗ Ω^b_X ≅ Ω^b_X(E)`
(`cartierTensorDifferentialFormsIso`), so `Ω^b_X(E)` is coherent (`isCoherent_twistedFormsSheaf`)
and the Serre vanishing theorem applies: `Hⁱ(Ω^b_X(m H)) = 0` for `i > 0`, `m ≫ 0` and `H` ample
(`twistedFormsSheaf_serreVanishing`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TensorProduct TopologicalSpace MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

theorem rationalFormsSheaf_sections_subsingleton (b : ℕ) {U : X.Opens} (hU : IsEmpty U) :
    Subsingleton Γ(rationalFormsSheaf K X b, U) :=
  modules_sections_subsingleton_of_eq_bot _ (Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU))

theorem rationalFormsSheaf_sections_ext {b : ℕ} {U : X.Opens} {s t : Γ(rationalFormsSheaf K X b, U)}
    (h : ∀ (_ : Nonempty U), rationalFormsSectionsEquiv K b U s = rationalFormsSectionsEquiv K b U t) :
    s = t := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (rationalFormsSheaf_sections_subsingleton b hU) _ _
  · exact (rationalFormsSectionsEquiv K b U).injective (h hU)

open Classical in
variable (K) in
/-- The product of a rational function and a rational `b`-form on an open subset (zero on the
empty open subset, where all sections vanish). -/
noncomputable def formsMul (b : ℕ) (U : X.Opens) (a : Γ(rationalFunctions X, U))
    (t : Γ(rationalFormsSheaf K X b, U)) : Γ(rationalFormsSheaf K X b, U) :=
  if _h : Nonempty U then
    (rationalFormsSectionsEquiv K b U).symm
      (rationalFunctionsEquiv U a • rationalFormsSectionsEquiv K b U t)
  else 0

theorem rationalFormsSectionsEquiv_formsMul (b : ℕ) (U : X.Opens) [h : Nonempty U]
    (a : Γ(rationalFunctions X, U)) (t : Γ(rationalFormsSheaf K X b, U)) :
    rationalFormsSectionsEquiv K b U (formsMul K b U a t) =
      rationalFunctionsEquiv U a • rationalFormsSectionsEquiv K b U t := by
  unfold formsMul
  split
  · rw [AddEquiv.apply_symm_apply]
  · exact absurd h ‹_›

theorem formsMul_add_left (b : ℕ) (U : X.Opens) (a a' : Γ(rationalFunctions X, U))
    (t : Γ(rationalFormsSheaf K X b, U)) :
    formsMul K b U (a + a') t = formsMul K b U a t + formsMul K b U a' t :=
  rationalFormsSheaf_sections_ext fun _ => by
    rw [map_add, rationalFormsSectionsEquiv_formsMul, rationalFormsSectionsEquiv_formsMul,
      rationalFormsSectionsEquiv_formsMul, map_add, add_smul]

theorem formsMul_add_right (b : ℕ) (U : X.Opens) (a : Γ(rationalFunctions X, U))
    (t t' : Γ(rationalFormsSheaf K X b, U)) :
    formsMul K b U a (t + t') = formsMul K b U a t + formsMul K b U a t' :=
  rationalFormsSheaf_sections_ext fun _ => by
    rw [map_add, rationalFormsSectionsEquiv_formsMul, rationalFormsSectionsEquiv_formsMul,
      rationalFormsSectionsEquiv_formsMul, map_add, smul_add]

theorem formsMul_smul_left (b : ℕ) (U : X.Opens) (r : Γ(X, U)) (a : Γ(rationalFunctions X, U))
    (t : Γ(rationalFormsSheaf K X b, U)) :
    formsMul K b U (r • a) t = r • formsMul K b U a t :=
  rationalFormsSheaf_sections_ext fun _ => by
    rw [rationalFormsSectionsEquiv_formsMul, rationalFormsSectionsEquiv_smul,
      rationalFormsSectionsEquiv_formsMul, map_smul, Algebra.smul_def, mul_smul]
    rfl

theorem formsMul_smul_right (b : ℕ) (U : X.Opens) (r : Γ(X, U)) (a : Γ(rationalFunctions X, U))
    (t : Γ(rationalFormsSheaf K X b, U)) :
    formsMul K b U a (r • t) = r • formsMul K b U a t :=
  rationalFormsSheaf_sections_ext fun _ => by
    rw [rationalFormsSectionsEquiv_formsMul, rationalFormsSectionsEquiv_smul,
      rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_formsMul, smul_comm]

theorem formsMul_map (b : ℕ) {U V : X.Opens} (i : V ⟶ U) (a : Γ(rationalFunctions X, U))
    (t : Γ(rationalFormsSheaf K X b, U)) :
    formsMul K b V ((rationalFunctions X).presheaf.map i.op a)
        ((rationalFormsSheaf K X b).presheaf.map i.op t) =
      (rationalFormsSheaf K X b).presheaf.map i.op (formsMul K b U a t) :=
  rationalFormsSheaf_sections_ext fun hV => by
    have : Nonempty U := ⟨⟨hV.some.1, i.le hV.some.2⟩⟩
    rw [rationalFormsSectionsEquiv_formsMul, rationalFunctionsEquiv_map,
      rationalFormsSectionsEquiv_map, rationalFormsSectionsEquiv_map,
      rationalFormsSectionsEquiv_formsMul]

/-- **A section of `𝒪_X(E)` times a section of `Ω^b_X(F)` is a section of `Ω^b_X(E + F)`.** -/
theorem formsMul_mem {E F : CartierDivisor X} {b : ℕ} {U : X.Opens}
    {a : Γ(rationalFunctions X, U)} {t : Γ(rationalFormsSheaf K X b, U)}
    (ha : a ∈ E.sections U) (ht : t ∈ twistedFormsSections K F b U) :
    formsMul K b U a t ∈ twistedFormsSections K (E + F) b U := by
  refine (mem_twistedFormsSections_iff_exists _).mpr fun x hx => ?_
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨f, hf⟩ := E.exists_isLocalEquationAt x
  obtain ⟨g, hg⟩ := F.exists_isLocalEquationAt x
  refine ⟨f * g, hf.mul hg, ?_⟩
  obtain ⟨c, hc⟩ := (CartierDivisor.mem_sections.mp ha) x hx f hf
  have hgt := ht x hx g hg
  rw [rationalFormsSectionsEquiv_formsMul, smul_smul, Units.val_mul,
    show (f : X.functionField) * g * rationalFunctionsEquiv U a =
      (f * rationalFunctionsEquiv U a) * g by ring, mul_smul, ← hc, algebraMap_smul]
  exact Submodule.smul_mem _ c hgt

variable (K) in
/-- Multiplication of sections, `Γ(𝒪_X(E), U) × Γ(Ω^b_X(F), U) → Γ(Ω^b_X(E + F), U)`. -/
noncomputable def twistedSectionsMul (E F : CartierDivisor X) (b : ℕ) (U : X.Opens)
    (s : Γ(E.sheaf, U)) (t : Γ(twistedFormsSheaf K F b, U)) :
    Γ(twistedFormsSheaf K (E + F) b, U) :=
  ⟨formsMul K b U (Scheme.Modules.Hom.app E.sheafι U s) t.1,
    formsMul_mem (CartierDivisor.sheafι_app_mem E U s) t.2⟩

theorem twistedSectionsMul_val (E F : CartierDivisor X) (b : ℕ) (U : X.Opens)
    (s : Γ(E.sheaf, U)) (t : Γ(twistedFormsSheaf K F b, U)) :
    (twistedSectionsMul K E F b U s t).1 = formsMul K b U (Scheme.Modules.Hom.app E.sheafι U s) t.1 :=
  rfl

variable {E F : CartierDivisor X} {b : ℕ} {U : X.Opens}

theorem twistedSectionsMul_add_left (s s' : Γ(E.sheaf, U)) (t : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMul K E F b U (s + s') t =
      twistedSectionsMul K E F b U s t + twistedSectionsMul K E F b U s' t :=
  Subtype.ext (by
    rw [Submodule.coe_add, twistedSectionsMul_val, twistedSectionsMul_val, twistedSectionsMul_val,
      map_add, formsMul_add_left])

theorem twistedSectionsMul_add_right (s : Γ(E.sheaf, U)) (t t' : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMul K E F b U s (t + t') =
      twistedSectionsMul K E F b U s t + twistedSectionsMul K E F b U s t' :=
  Subtype.ext (by
    rw [Submodule.coe_add, twistedSectionsMul_val, twistedSectionsMul_val, twistedSectionsMul_val,
      Submodule.coe_add, formsMul_add_right])

theorem twistedSectionsMul_smul_left (r : Γ(X, U)) (s : Γ(E.sheaf, U))
    (t : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMul K E F b U (r • s) t = r • twistedSectionsMul K E F b U s t :=
  Subtype.ext (by
    rw [Submodule.coe_smul, twistedSectionsMul_val, twistedSectionsMul_val,
      Scheme.Modules.Hom.app_smul, formsMul_smul_left])

theorem twistedSectionsMul_smul_right (r : Γ(X, U)) (s : Γ(E.sheaf, U))
    (t : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMul K E F b U s (r • t) = r • twistedSectionsMul K E F b U s t :=
  Subtype.ext (by
    rw [Submodule.coe_smul, twistedSectionsMul_val, twistedSectionsMul_val, Submodule.coe_smul,
      formsMul_smul_right])

/-- Restriction commutes with multiplication of sections. -/
theorem twistedSectionsMul_map {V : X.Opens} (i : V ⟶ U) (s : Γ(E.sheaf, U))
    (t : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMul K E F b V (E.sheaf.presheaf.map i.op s)
        ((twistedFormsSheaf K F b).presheaf.map i.op t) =
      (twistedFormsSheaf K (E + F) b).presheaf.map i.op (twistedSectionsMul K E F b U s t) := by
  apply Subtype.ext
  have h := NatTrans.naturality_apply (CartierDivisor.sheafι E).mapPresheaf i.op s
  simp only [Scheme.Modules.mapPresheaf_app] at h
  change formsMul K b V (Scheme.Modules.Hom.app E.sheafι V (E.sheaf.presheaf.map i.op s))
      ((rationalFormsSheaf K X b).presheaf.map i.op t.1) =
    (rationalFormsSheaf K X b).presheaf.map i.op (formsMul K b U
      (Scheme.Modules.Hom.app E.sheafι U s) t.1)
  rw [h, formsMul_map]

variable (K E F b U) in
/-- Multiplication, linear on the tensor product of the sections. -/
noncomputable def twistedSectionsMulLift :
    TensorProduct Γ(X, U) Γ(E.sheaf, U) Γ(twistedFormsSheaf K F b, U) →ₗ[Γ(X, U)]
      Γ(twistedFormsSheaf K (E + F) b, U) :=
  TensorProduct.lift <| LinearMap.mk₂ Γ(X, U) (twistedSectionsMul K E F b U)
    (fun s s' t ↦ twistedSectionsMul_add_left s s' t)
    (fun r s t ↦ twistedSectionsMul_smul_left r s t)
    (fun s t t' ↦ twistedSectionsMul_add_right s t t')
    (fun r s t ↦ twistedSectionsMul_smul_right r s t)

theorem twistedSectionsMulLift_tmul (s : Γ(E.sheaf, U)) (t : Γ(twistedFormsSheaf K F b, U)) :
    twistedSectionsMulLift K E F b U (s ⊗ₜ t) = twistedSectionsMul K E F b U s t :=
  rfl

variable (K E F b) in
/-- The multiplication morphism of presheaves of modules. -/
noncomputable def twistedTensorPresheafHom :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj) E.sheaf.val
      (twistedFormsSheaf K F b).val ⟶ (twistedFormsSheaf K (E + F) b).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun s t ↦ twistedSectionsMul K E F b U.unop s t)
    (fun s s' t ↦ twistedSectionsMul_add_left s s' t)
    (fun r s t ↦ twistedSectionsMul_smul_left r s t)
    (fun s t t' ↦ twistedSectionsMul_add_right s t t')
    (fun r s t ↦ twistedSectionsMul_smul_right r s t)
  naturality f := ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ twistedSectionsMul_map f.unop s t

theorem twistedTensorPresheafHom_app :
    ModuleCat.Hom.hom (R := X.sheaf.obj.obj (op U)) ((twistedTensorPresheafHom K E F b).app (op U)) =
      twistedSectionsMulLift K E F b U :=
  TensorProduct.ext' fun s t ↦ (twistedSectionsMulLift_tmul s t).symm

section LocalEquation

variable {V : X.Opens} [Nonempty V] {g : X.functionFieldˣ}
  (hg : ∀ x ∈ V, E.IsLocalEquationAt x g)

include hg

/-- Multiplying a form with poles bounded by `E + F` by an equation of `E` bounds its poles by
`F`. -/
theorem smul_localEquation_mem_twisted (ω : Γ(rationalFormsSheaf K X b, V))
    (hω : ω ∈ twistedFormsSections K (E + F) b V) :
    (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω) ∈
      twistedFormsSections K F b V := by
  intro x hx h hh
  rw [AddEquiv.apply_symm_apply, smul_smul, mul_comm]
  have := hω x hx (g * h) ((hg x hx).mul hh)
  rwa [Units.val_mul] at this

/-- The inverse of an equation of `E` is a section of `𝒪_X(E)`. -/
theorem inv_localEquation_mem_sections_of_forall :
    (rationalFunctionsEquiv V).symm ((g : X.functionField)⁻¹) ∈ E.sections V := by
  refine CartierDivisor.mem_sections.mpr fun x hx f hf => ?_
  rw [(hf.mul_mem_range_iff (hg x hx) _), LinearEquiv.apply_symm_apply,
    mul_inv_cancel₀ g.ne_zero]
  exact Subring.one_mem _

/-- An equation of `E` times a section of `𝒪_X(E)` is regular. -/
theorem exists_germ_eq_localEquation_mul (a : Γ(E.sheaf, V)) :
    ∃ r : Γ(X, V), X.germToFunctionField V r =
      g * rationalFunctionsEquiv V (Scheme.Modules.Hom.app E.sheafι V a) :=
  exists_germToFunctionField_eq_of_forall_mem_range fun x hx =>
    (CartierDivisor.mem_sections.mp (CartierDivisor.sheafι_app_mem E V a)) x hx g (hg x hx)

variable (K F b) in
/-- The section `g • ω` of `Ω^b_X(F)` for a section `ω` of `Ω^b_X(E + F)`. -/
noncomputable def localEquationSmulSection (ω : Γ(twistedFormsSheaf K (E + F) b, V)) :
    Γ(twistedFormsSheaf K F b, V) :=
  ⟨(rationalFormsSectionsEquiv K b V).symm
      ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1),
    smul_localEquation_mem_twisted hg ω.1 ω.2⟩

/-- The section `g⁻¹` of `𝒪_X(E)`. -/
noncomputable def invLocalEquationSection : Γ(E.sheaf, V) :=
  CartierDivisor.sectionMk _ (inv_localEquation_mem_sections_of_forall hg)

theorem rationalFunctionsEquiv_invLocalEquationSection :
    rationalFunctionsEquiv V (Scheme.Modules.Hom.app E.sheafι V (invLocalEquationSection hg)) =
      (g : X.functionField)⁻¹ := by
  rw [invLocalEquationSection, CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem twistedSectionsMul_inv_smul (ω : Γ(twistedFormsSheaf K (E + F) b, V)) :
    twistedSectionsMul K E F b V (invLocalEquationSection hg)
        (localEquationSmulSection K F b hg ω) = ω := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b V).injective
  rw [twistedSectionsMul_val, rationalFormsSectionsEquiv_formsMul,
    rationalFunctionsEquiv_invLocalEquationSection]
  change ((g : X.functionField))⁻¹ • rationalFormsSectionsEquiv K b V
    ((rationalFormsSectionsEquiv K b V).symm ((g : X.functionField) •
      rationalFormsSectionsEquiv K b V ω.1)) = _
  rw [AddEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ g.ne_zero, one_smul]

/-- Multiplication of sections is surjective on a domain of an equation of `E`. -/
theorem exists_twistedSectionsMul_eq (ω : Γ(twistedFormsSheaf K (E + F) b, V)) :
    ∃ (a : Γ(E.sheaf, V)) (t : Γ(twistedFormsSheaf K F b, V)),
      twistedSectionsMul K E F b V a t = ω :=
  ⟨_, _, twistedSectionsMul_inv_smul hg ω⟩

variable (K F b) in
/-- Multiplication by the equation `g` gives a linear retraction of the multiplication. -/
noncomputable def twistedRetraction :
    Γ(twistedFormsSheaf K (E + F) b, V) →ₗ[Γ(X, V)]
      TensorProduct Γ(X, V) Γ(E.sheaf, V) Γ(twistedFormsSheaf K F b, V) where
  toFun ω := invLocalEquationSection hg ⊗ₜ localEquationSmulSection K F b hg ω
  map_add' ω ω' := by
    rw [← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V (ω.1 + ω'.1))) =
      rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1) +
        (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω'.1))
    rw [map_add, map_add, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, smul_add]
  map_smul' r ω := by
    rw [RingHom.id_apply, ← TensorProduct.tmul_smul]
    congr 1
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V (r • ω.1))) =
      rationalFormsSectionsEquiv K b V (r • (rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V ω.1))
    rw [AddEquiv.apply_symm_apply, rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_smul,
      AddEquiv.apply_symm_apply, smul_comm]

/-- Multiplication by the equation `g` retracts the multiplication. -/
theorem twistedRetraction_twistedSectionsMul (a : Γ(E.sheaf, V))
    (t : Γ(twistedFormsSheaf K F b, V)) :
    twistedRetraction K F b hg (twistedSectionsMul K E F b V a t) = a ⊗ₜ t := by
  obtain ⟨r, hr⟩ := exists_germ_eq_localEquation_mul hg a
  have h1 : localEquationSmulSection K F b hg (twistedSectionsMul K E F b V a t) = r • t := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K b V).injective
    change rationalFormsSectionsEquiv K b V ((rationalFormsSectionsEquiv K b V).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b V
          (twistedSectionsMul K E F b V a t).1)) = rationalFormsSectionsEquiv K b V (r • t.1)
    rw [AddEquiv.apply_symm_apply, twistedSectionsMul_val, rationalFormsSectionsEquiv_formsMul,
      rationalFormsSectionsEquiv_smul, hr, smul_smul]
  have h2 : r • invLocalEquationSection hg = a := by
    apply CartierDivisor.sheafι_app_injective E V
    apply (rationalFunctionsEquiv V).injective
    rw [Scheme.Modules.Hom.app_smul, map_smul, rationalFunctionsEquiv_invLocalEquationSection,
      Algebra.smul_def]
    change X.germToFunctionField V r * _ = _
    rw [hr, mul_comm (g : X.functionField), mul_assoc, mul_inv_cancel₀ g.ne_zero, mul_one]
  change invLocalEquationSection hg ⊗ₜ
    localEquationSmulSection K F b hg (twistedSectionsMul K E F b V a t) = a ⊗ₜ t
  rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', h2]

/-- Multiplication is injective on a domain of an equation of `E`. -/
theorem twistedSectionsMulLift_injective : Function.Injective (twistedSectionsMulLift K E F b V) := by
  have key : Function.LeftInverse (twistedRetraction K F b hg) (twistedSectionsMulLift K E F b V) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a t =>
      rw [twistedSectionsMulLift_tmul]
      exact twistedRetraction_twistedSectionsMul hg a t
    | add u v hu hv => rw [map_add, map_add, hu, hv]
  exact key.injective

end LocalEquation

/-- Every point has a neighbourhood inside a given open subset carrying an equation of `E`. -/
theorem exists_forall_isLocalEquationAt_le (E : CartierDivisor X) (U : X.Opens) {x : X}
    (hx : x ∈ U) : ∃ (V : X.Opens) (_ : V ≤ U) (_ : x ∈ V) (g : X.functionFieldˣ),
      ∀ y ∈ V, E.IsLocalEquationAt y g := by
  obtain ⟨V, hVU, hxV, g, hg⟩ := CartierDivisor.exists_localEquation_le E U hx
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact ⟨V, hVU, hxV, g, fun y hy => CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hg hy⟩

variable (K E F b) in
theorem isLocallySurjective_twistedTensorPresheafHom :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (twistedTensorPresheafHom K E F b)) where
  imageSieve_mem {U} s x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_forall_isLocalEquationAt_le E U hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    obtain ⟨a, t, hat⟩ := exists_twistedSectionsMul_eq (K := K) (F := F) (b := b) hg
      ((twistedFormsSheaf K (E + F) b).presheaf.map (homOfLE hVU).op s)
    exact ⟨V, homOfLE hVU, ⟨a ⊗ₜ t, hat⟩, hxV⟩

variable (K E F b) in
theorem isLocallyInjective_twistedTensorPresheafHom :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (twistedTensorPresheafHom K E F b)) where
  equalizerSieve_mem {U} z z' h x hx := by
    obtain ⟨V, hVU, hxV, g, hg⟩ := exists_forall_isLocalEquationAt_le E U.unop hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    refine ⟨V, homOfLE hVU, twistedSectionsMulLift_injective (K := K) (F := F) (b := b) hg ?_, hxV⟩
    exact (PresheafOfModules.naturality_apply (twistedTensorPresheafHom K E F b) (homOfLE hVU).op
      z).trans ((congrArg ((twistedFormsSheaf K (E + F) b).val.map (homOfLE hVU).op) h).trans
        (PresheafOfModules.naturality_apply (twistedTensorPresheafHom K E F b) (homOfLE hVU).op
          z').symm)

variable (K E F b) in
theorem isIso_sheafification_map_twistedTensorPresheafHom :
    IsIso ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).map (twistedTensorPresheafHom K E F b)) := by
  have := isLocallySurjective_twistedTensorPresheafHom K E F b
  have := isLocallyInjective_twistedTensorPresheafHom K E F b
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)))
      (twistedTensorPresheafHom K E F b)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective _

variable (K E F b) in
/-- **`𝒪_X(E) ⊗ Ω^b_X(F) ≅ Ω^b_X(E + F)`.** -/
noncomputable def twistedTensorSheafIso :
    E.sheaf ⊗ twistedFormsSheaf K F b ≅ twistedFormsSheaf K (E + F) b :=
  E.sheaf.tensorUnderlyingIso (twistedFormsSheaf K F b) ≪≫
    @asIso _ _ _ _ _ (isIso_sheafification_map_twistedTensorPresheafHom K E F b) ≪≫
    TauCeti.SheafOfModules.sheafificationIso X.ringCatSheaf (twistedFormsSheaf K (E + F) b)

theorem twistedFormsSubmodule_zero (b : ℕ) :
    twistedFormsSubmodule K (0 : CartierDivisor X) b = regularFormsSubmodule K b :=
  SheafOfModules.Submodule.ext
    (PresheafOfModules.Submodule.ext fun U => twistedFormsSections_zero b U.unop)

variable (K) in
/-- `Ω^b_X(0) ≅ Ω^b_X`. -/
noncomputable def twistedFormsSheafZeroIso (b : ℕ) :
    twistedFormsSheaf K (0 : CartierDivisor X) b ≅ differentialFormsSheaf K (X := X) b :=
  eqToIso (congrArg (fun N => SheafOfModules.Submodule.toSheafOfModules N)
    (twistedFormsSubmodule_zero b))

variable (K) in
/-- **`𝒪_X(E) ⊗ Ω^b_X ≅ Ω^b_X(E)`.** -/
noncomputable def cartierTensorDifferentialFormsIso (E : CartierDivisor X) (b : ℕ) :
    E.sheaf ⊗ differentialFormsSheaf K (X := X) b ≅ twistedFormsSheaf K E b :=
  (MonoidalCategory.whiskerLeftIso E.sheaf (twistedFormsSheafZeroIso K b)).symm ≪≫
    twistedTensorSheafIso K E 0 b ≪≫
    eqToIso (congrArg (fun D => twistedFormsSheaf K D b) (add_zero E))

/-- **`Ω^b_X(E)` is coherent** on an integral scheme covered by étale charts. -/
theorem isCoherent_twistedFormsSheaf {n : ℕ}
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) (b : ℕ) :
    (twistedFormsSheaf K E b).IsCoherent := by
  have := isCoherent_differentialFormsSheaf hcover b
  have := cartierTensorModule_isCoherent E (differentialFormsSheaf K (X := X) b)
  let a := cartierTensorDifferentialFormsIso K E b
  have : (E.sheaf ⊗ differentialFormsSheaf K (X := X) b).IsQuasicoherent :=
    Scheme.Modules.IsCoherent.isQuasicoherent
  have : (E.sheaf ⊗ differentialFormsSheaf K (X := X) b).IsFiniteType :=
    Scheme.Modules.IsCoherent.isFiniteType
  exact ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩

/-- **Serre vanishing for `Ω^b_X(n H)`**, `H` ample: `Hⁱ(Ω^b_X(n H)) = 0` for `i > 0` and
`n ≫ 0`. -/
theorem twistedFormsSheaf_serreVanishing {n : ℕ}
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (H : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (b : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ q : ℕ,
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
        (twistedFormsSheaf K (m • H) b) (q + 1)) := by
  have := isCoherent_differentialFormsSheaf hcover b
  obtain ⟨m₀, hm₀⟩ := cartierIsAmpleProj_coherent_tensor_serreVanishing H hH
    (differentialFormsSheaf K (X := X) b)
  refine ⟨m₀, fun m hm q => ?_⟩
  have h := hm₀ m hm q
  let e := ((TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyFunctor X (q + 1)).mapIso
    (cartierTensorDifferentialFormsIso K (m • H) b)).addCommGroupIsoToAddEquiv
  exact @Equiv.subsingleton _ _ e.symm.toEquiv h

end MixedFujita

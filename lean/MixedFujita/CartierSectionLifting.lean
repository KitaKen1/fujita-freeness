/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleAffineExactness
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
Lifting sections along an effective Cartier divisor from the vanishing of first cohomology
(step 12, section 6.3 of the manuscript: the surjection (31)).

Let D be a Cartier divisor and E an effective Cartier divisor on an integral scheme with
H¹(X, O(D − E)) = 0. Let W and V be open subsets covering X such that over W ∩ V the sections of
O(D) are sections of O(D − E) (E is trivial on V: W is a neighbourhood of the support of E), and
let g_W be a section of O(D) over W. Then there is a global section g of O(D) such that g − g_W
is a section of O(D − E) over W: the section g_W, defined near the support of E, lifts to a
global section up to sections vanishing along E.

Proof. The inclusion O(D − E) → O(D) and its cokernel form a short exact sequence. The image of
g_W in the cokernel over W vanishes on W ∩ V, so it glues with zero on V to a global section of
the cokernel; the vanishing of H¹ lifts it to a global section g of O(D), and g − g_W dies in the
cokernel over W, hence comes from O(D − E) by left exactness of sections over W. The divisor E
is not given a scheme structure.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Exactness

variable {X : Scheme.{u}}

/-- Sections over an open subset are left exact: a section of the middle term of a short exact
sequence of modules which dies in the third term comes from the first term. -/
theorem moduleSections_exists_of_app_eq_zero {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (U : X.Opens) (x₂ : Γ(S.X₂, U)) (h : Scheme.Modules.Hom.app S.g U x₂ = 0) :
    ∃ x₁ : Γ(S.X₁, U), Scheme.Modules.Hom.app S.f U x₁ = x₂ := by
  have hmono := hS.mono_f
  have hex : (S.map (moduleOpenEvaluation X U)).Exact :=
    hS.exact.map_of_mono_of_preservesKernel (moduleOpenEvaluation X U) hmono inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).mp hex x₂ h

/-- Morphisms of modules commute with restriction of sections. -/
theorem moduleHom_app_restrict {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V)
    (a : Γ(M, V)) :
    Scheme.Modules.Hom.app φ W (M.presheaf.map i.op a) =
      N.presheaf.map i.op (Scheme.Modules.Hom.app φ V a) :=
  φ.mapPresheaf.naturality_apply i.op a

/-- A section over W whose restriction to W ∩ V vanishes extends by zero to a section over the
whole space when W and V cover it. -/
theorem moduleSections_exists_extension_of_restrict_eq_zero (M : X.Modules) (W V : X.Opens)
    (hWV : W ⊔ V = ⊤) (a : Γ(M, W))
    (ha : M.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op a = 0) :
    ∃ y : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y = a := by
  let U : Bool → X.Opens := fun t => cond t W V
  let sf : ∀ t : Bool, Γ(M, U t) := fun t =>
    match t with
    | true => a
    | false => 0
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf U sf := by
    intro i j
    cases i <;> cases j
    · change M.presheaf.map (Opens.infLELeft V V).op (0 : Γ(M, V)) =
        M.presheaf.map (Opens.infLERight V V).op (0 : Γ(M, V))
      rw [map_zero, map_zero]
    · change M.presheaf.map (Opens.infLELeft V W).op (0 : Γ(M, V)) =
        M.presheaf.map (Opens.infLERight V W).op a
      rw [map_zero]
      have h1 : M.presheaf.map (Opens.infLERight V W).op a =
          M.presheaf.map (homOfLE (le_inf inf_le_right inf_le_left : V ⊓ W ≤ W ⊓ V)).op
            (M.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op a) := by
        rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
        rfl
      rw [h1, ha, map_zero]
    · change M.presheaf.map (Opens.infLELeft W V).op a =
        M.presheaf.map (Opens.infLERight W V).op (0 : Γ(M, V))
      rw [map_zero]
      exact ha
    · rfl
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    rw [← hWV]
    exact sup_le (le_iSup U true) (le_iSup U false)
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
    (fun t => homOfLE le_top) hcover sf hcompat
  exact ⟨y, hy true⟩

end Exactness

section Lifting

variable {X : Scheme.{u}} [IsIntegral X]

/-- The sections of O(D − E) are sections of O(D) when E is effective. -/
theorem cartier_sections_sub_le (D E : CartierDivisor X) (hE : E.IsEffective) (U : X.Opens) :
    (D - E).sections U ≤ D.sections U := by
  intro s hs
  rw [CartierDivisor.mem_sections_iff_exists]
  intro x hx
  obtain ⟨f, hf⟩ := (D - E).exists_isLocalEquationAt x
  obtain ⟨e, he, hreg⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
  have hfe : D.IsLocalEquationAt x (f * e) := by
    have h := hf.mul he
    rwa [sub_add_cancel] at h
  refine ⟨f * e, hfe, ?_⟩
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  have hr := (CartierDivisor.mem_sections.mp hs) x hx f hf
  have hmul := Subring.mul_mem (algebraMap (X.presheaf.stalk x) X.functionField).range hreg hr
  have heq : ((f * e : X.functionFieldˣ) : X.functionField) * rationalFunctionsEquiv U s =
      (e : X.functionField) * ((f : X.functionField) * rationalFunctionsEquiv U s) := by
    rw [Units.val_mul]
    ring
  rw [heq]
  exact hmul

/-- The inclusion O(D − E) → O(D) for an effective Cartier divisor E. -/
noncomputable def cartierEffectiveInclusion (D E : CartierDivisor X) (hE : E.IsEffective) :
    (D - E).sheaf ⟶ D.sheaf :=
  CartierDivisor.sheafLift D (D - E).sheafι fun U s =>
    cartier_sections_sub_le D E hE U ((D - E).sheafι_app_mem U s)

theorem cartierEffectiveInclusion_ι (D E : CartierDivisor X) (hE : E.IsEffective) :
    cartierEffectiveInclusion D E hE ≫ D.sheafι = (D - E).sheafι :=
  CartierDivisor.sheafLift_ι _ _ _

theorem cartierEffectiveInclusion_mono (D E : CartierDivisor X) (hE : E.IsEffective) :
    Mono (cartierEffectiveInclusion D E hE) :=
  @mono_of_mono_fac _ _ _ _ _ _ _ _ inferInstance (cartierEffectiveInclusion_ι D E hE)

/-- The short exact sequence 0 → O(D − E) → O(D) → O(D)/O(D − E) → 0. -/
theorem cartierEffectiveInclusion_cokernelSequence_shortExact (D E : CartierDivisor X)
    (hE : E.IsEffective) :
    (ShortComplex.cokernelSequence (cartierEffectiveInclusion D E hE)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (cartierEffectiveInclusion_mono D E hE) (inferInstanceAs (Epi (cokernel.π _)))

/-- Lifting sections along an effective Cartier divisor: if H¹(X, O(D − E)) vanishes, W and V
cover X and the sections of O(D) over W ∩ V are sections of O(D − E), then every section of O(D)
over W agrees with a global section of O(D) up to a section of O(D − E) over W. -/
theorem cartierSections_exists_global_congr (D E : CartierDivisor X) (hE : E.IsEffective)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf 1)) (W V : X.Opens)
    (hWV : W ⊔ V = ⊤) (hV : D.sections (W ⊓ V) ≤ (D - E).sections (W ⊓ V))
    (sW : Γ(rationalFunctions X, W)) (hsW : sW ∈ D.sections W) :
    ∃ s : Γ(rationalFunctions X, ⊤), s ∈ D.sections ⊤ ∧
      (rationalFunctions X).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s - sW ∈
        (D - E).sections W := by
  have hS : (ShortComplex.mk (cartierEffectiveInclusion D E hE)
      (cokernel.π (cartierEffectiveInclusion D E hE)) (cokernel.condition _)).ShortExact :=
    cartierEffectiveInclusion_cokernelSequence_shortExact D E hE
  -- the given section of O(D) over W
  obtain ⟨tW, htW⟩ : ∃ tW : Γ(D.sheaf, W), Scheme.Modules.Hom.app D.sheafι W tW = sW :=
    ⟨CartierDivisor.sectionMk sW hsW, CartierDivisor.sheafι_app_sectionMk sW hsW⟩
  -- over W ∩ V it comes from O(D − E)
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : Γ((D - E).sheaf, W ⊓ V),
      Scheme.Modules.Hom.app (cartierEffectiveInclusion D E hE) (W ⊓ V) u₀ =
        D.sheaf.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op tW := by
    have hmem : (rationalFunctions X).presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op sW ∈
        (D - E).sections (W ⊓ V) :=
      hV (CartierDivisor.sections_map (homOfLE (inf_le_left : W ⊓ V ≤ W)) hsW)
    refine ⟨CartierDivisor.sectionMk _ hmem, ?_⟩
    apply D.sheafι_app_injective (W ⊓ V)
    have h1 : Scheme.Modules.Hom.app D.sheafι (W ⊓ V)
        (Scheme.Modules.Hom.app (cartierEffectiveInclusion D E hE) (W ⊓ V)
          (CartierDivisor.sectionMk _ hmem)) =
        Scheme.Modules.Hom.app (D - E).sheafι (W ⊓ V) (CartierDivisor.sectionMk _ hmem) := by
      rw [← cartierEffectiveInclusion_ι D E hE]
      rfl
    rw [h1, CartierDivisor.sheafι_app_sectionMk, moduleHom_app_restrict D.sheafι, htW]
  -- so its image in the cokernel vanishes on W ∩ V
  have ha : (cokernel (cartierEffectiveInclusion D E hE)).presheaf.map
      (homOfLE (inf_le_left : W ⊓ V ≤ W)).op
        (Scheme.Modules.Hom.app (cokernel.π (cartierEffectiveInclusion D E hE)) W tW) = 0 := by
    rw [← moduleHom_app_restrict, ← hu₀]
    have hz : cartierEffectiveInclusion D E hE ≫ cokernel.π (cartierEffectiveInclusion D E hE) =
        0 := cokernel.condition _
    exact congrArg (fun φ => Scheme.Modules.Hom.app φ (W ⊓ V) u₀) hz
  obtain ⟨y, hy⟩ := moduleSections_exists_extension_of_restrict_eq_zero
    (cokernel (cartierEffectiveInclusion D E hE)) W V hWV _ ha
  obtain ⟨t, ht⟩ := Scheme.Modules.sections_surjective hS hvan y
  have ht' : Scheme.Modules.Hom.app (cokernel.π (cartierEffectiveInclusion D E hE)) ⊤ t = y := ht
  -- the difference dies in the cokernel over W
  have hdiff : Scheme.Modules.Hom.app (cokernel.π (cartierEffectiveInclusion D E hE)) W
      (D.sheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t - tW) = 0 := by
    rw [map_sub, moduleHom_app_restrict, ht', hy, sub_self]
  obtain ⟨u, hu⟩ := moduleSections_exists_of_app_eq_zero hS W
    (D.sheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t - tW) hdiff
  have hu' : Scheme.Modules.Hom.app (cartierEffectiveInclusion D E hE) W u =
      D.sheaf.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t - tW := hu
  refine ⟨Scheme.Modules.Hom.app D.sheafι ⊤ t, D.sheafι_app_mem ⊤ t, ?_⟩
  have hιu : Scheme.Modules.Hom.app (D - E).sheafι W u =
      (rationalFunctions X).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (Scheme.Modules.Hom.app D.sheafι ⊤ t) - sW := by
    have h1 : Scheme.Modules.Hom.app (D - E).sheafι W u =
        Scheme.Modules.Hom.app D.sheafι W
          (Scheme.Modules.Hom.app (cartierEffectiveInclusion D E hE) W u) := by
      rw [← cartierEffectiveInclusion_ι D E hE]
      rfl
    rw [h1, hu', map_sub, moduleHom_app_restrict D.sheafι, htW]
  rw [← hιu]
  exact (D - E).sheafι_app_mem W u

/-- The lifted section generates at a point of the divisor: if moreover the section g_W over W
generates O(D) at a point ξ of W at which the local equation of E is not a unit, then the global
section g generates O(D) at ξ as well, since g − g_W lies in the maximal ideal times O(D) there. -/
theorem cartierSections_exists_global_generator (D E : CartierDivisor X) (hE : E.IsEffective)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf 1)) (W V : X.Opens)
    [Nonempty W] (hWV : W ⊔ V = ⊤) (hV : D.sections (W ⊓ V) ≤ (D - E).sections (W ⊓ V))
    (gW : X.functionField) (hgW : (rationalFunctionsEquiv (X := X) W).symm gW ∈ D.sections W)
    (ξ : X) (hξ : ξ ∈ W) (f e : X.functionFieldˣ) (hf : D.IsLocalEquationAt ξ f)
    (he : E.IsLocalEquationAt ξ e)
    (heξ : ∃ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ),
      algebraMap (X.presheaf.stalk ξ) X.functionField a = e)
    (hgen : ∃ u : (X.presheaf.stalk ξ)ˣ,
      algebraMap (X.presheaf.stalk ξ) X.functionField u = f * gW) :
    ∃ g : X.functionField, (rationalFunctionsEquiv (X := X) ⊤).symm g ∈ D.sections ⊤ ∧
      ∃ u : (X.presheaf.stalk ξ)ˣ,
        algebraMap (X.presheaf.stalk ξ) X.functionField u = f * g := by
  obtain ⟨s, hs, hdiff⟩ := cartierSections_exists_global_congr D E hE hvan W V hWV hV _ hgW
  have : Nonempty (⊤ : X.Opens) := ⟨⟨ξ, trivial⟩⟩
  refine ⟨rationalFunctionsEquiv ⊤ s, by rw [LinearEquiv.symm_apply_apply]; exact hs, ?_⟩
  have hfe : (D - E).IsLocalEquationAt ξ (f * e⁻¹) := by
    have h := hf.mul he.inv
    rwa [← sub_eq_add_neg] at h
  obtain ⟨b, hb⟩ := (CartierDivisor.mem_sections.mp hdiff) ξ hξ (f * e⁻¹) hfe
  rw [map_sub, rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply] at hb
  obtain ⟨a, ha, hae⟩ := heξ
  obtain ⟨u, hu⟩ := hgen
  have hunit : IsUnit ((u : X.presheaf.stalk ξ) + a * b) := by
    by_contra hnot
    have hmem : (u : X.presheaf.stalk ξ) + a * b ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := (IsLocalRing.mem_maximalIdeal _).mpr hnot
    have hab : a * b ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) :=
      Ideal.mul_mem_right b _ ha
    have hu' : (u : X.presheaf.stalk ξ) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) := by
      have h := Ideal.sub_mem _ hmem hab
      rwa [add_sub_cancel_right] at h
    exact (IsLocalRing.mem_maximalIdeal _).mp hu' u.isUnit
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, map_add, map_mul, hu, hae, hb, Units.val_mul, Units.val_inv_eq_inv_val]
  have he0 : (e : X.functionField) ≠ 0 := Units.ne_zero e
  field_simp
  ring

end Lifting

end MixedFujita

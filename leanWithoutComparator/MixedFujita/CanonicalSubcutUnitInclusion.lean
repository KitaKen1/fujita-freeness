/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ExceptionalSubcutKernel

/-! 実kernel標準包含と全開上の単位切断・Cartier格子判定。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The canonical actual subcut direct-image inclusion, using the inverse of the
canonical effective-divisor unit map. Its inverse is used only when proved an isomorphism. -/
noncomputable def cartierSubcutPushforwardUnitInclusion
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] :
    (Scheme.Modules.pushforward p).obj (E - S).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pushforward p).map (cartierEffectiveInclusion E S hS) ≫
    inv (effectiveCartierPushforwardUnitMap p E hE)


/-- This particular inclusion commutes with the canonical effective-divisor unit map. -/
theorem cartierSubcutPushforwardUnitInclusion_comp_unit
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] :
    cartierSubcutPushforwardUnitInclusion p E S hE hS ≫ effectiveCartierPushforwardUnitMap p E hE =
      (Scheme.Modules.pushforward p).map (cartierEffectiveInclusion E S hS) := by
  simp only [cartierSubcutPushforwardUnitInclusion, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]


/-- The canonical subcut inclusion is actually monic. -/
theorem cartierSubcutPushforwardUnitInclusion_mono
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] :
    Mono (cartierSubcutPushforwardUnitInclusion p E S hE hS) := by
  let := cartierEffectiveInclusion_mono E S hS
  dsimp only [cartierSubcutPushforwardUnitInclusion]
  infer_instance


/-- On EVERY actual open, the regular unit lies in the canonical direct-image kernel
exactly when it is a section of the actual subcut Cartier lattice upstairs. -/
theorem one_in_range_cartierSubcutPushforwardUnitInclusion_iff
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] (U : X.Opens) :
    (∃ s : Γ((Scheme.Modules.pushforward p).obj (E - S).sheaf, U),
      Scheme.Modules.Hom.app (cartierSubcutPushforwardUnitInclusion p E S hE hS) U s =
        (1 : Γ(X, U))) ↔
      Scheme.Modules.Hom.app (toRationalFunctions T) (p ⁻¹ᵁ U) (1 : Γ(T, p ⁻¹ᵁ U)) ∈
        (E - S).sections (p ⁻¹ᵁ U) := by
  let c := effectiveCartierPushforwardUnitMap p E hE
  let j := cartierSubcutPushforwardUnitInclusion p E S hE hS
  have hcomp : j ≫ c = (Scheme.Modules.pushforward p).map (cartierEffectiveInclusion E S hS) :=
    cartierSubcutPushforwardUnitInclusion_comp_unit p E S hE hS
  have hunit : Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U)
      (Scheme.Modules.Hom.app c U (1 : Γ(X, U))) =
      Scheme.Modules.Hom.app (toRationalFunctions T) (p ⁻¹ᵁ U) (1 : Γ(T, p ⁻¹ᵁ U)) := by
    rw [effectiveCartierPushforwardUnitMap_app, map_one]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.unitToSheaf_ι]
  have hinc (s : Γ((Scheme.Modules.pushforward p).obj (E - S).sheaf, U)) :
      Scheme.Modules.Hom.app c U (Scheme.Modules.Hom.app j U s) =
        Scheme.Modules.Hom.app (cartierEffectiveInclusion E S hS) (p ⁻¹ᵁ U) s := by
    change Scheme.Modules.Hom.app (j ≫ c) U s = _
    rw [hcomp]
    rfl
  constructor
  · rintro ⟨s, hs⟩
    have he := congrArg (Scheme.Modules.Hom.app E.sheafι (p ⁻¹ᵁ U)) (hinc s)
    rw [hs, hunit] at he
    have hι := ConcreteCategory.congr_hom (congrArg
      (fun f => Scheme.Modules.Hom.app f (p ⁻¹ᵁ U)) (cartierEffectiveInclusion_ι E S hS)) s
    exact he.symm ▸ (hι.symm ▸ (E - S).sheafι_app_mem (p ⁻¹ᵁ U) s)
  · intro hs
    let s := CartierDivisor.sectionMk _ hs
    refine ⟨s, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app c U)).injective
    rw [hinc s]
    apply E.sheafι_app_injective (p ⁻¹ᵁ U)
    rw [hunit]
    have hι := ConcreteCategory.congr_hom (congrArg
      (fun f => Scheme.Modules.Hom.app f (p ⁻¹ᵁ U)) (cartierEffectiveInclusion_ι E S hS)) s
    exact hι.trans (CartierDivisor.sheafι_app_sectionMk _ hs)


/-- The global unit criterion is actual effectivity, with no supplied section transport. -/
theorem one_in_global_range_cartierSubcutPushforwardUnitInclusion_iff
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (p : T ⟶ X)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] :
    (∃ s : Γ((Scheme.Modules.pushforward p).obj (E - S).sheaf, ⊤),
      Scheme.Modules.Hom.app (cartierSubcutPushforwardUnitInclusion p E S hE hS) ⊤ s =
        (1 : Γ(X, ⊤))) ↔ (E - S).IsEffective := by
  rw [one_in_range_cartierSubcutPushforwardUnitInclusion_iff, Scheme.Hom.preimage_top]
  exact CartierDivisor.isEffective_iff_one_mem_sections.symm

end MixedFujita

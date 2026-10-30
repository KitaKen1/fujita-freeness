/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureSubscheme
public import MixedFujita.AmpleSumReduction
public import MixedFujita.ClosedImmersionCohomology
public import MixedFujita.CartierSectionDivisor

/-!
Restricting sections to the closure of a point and expanding them at a point of it (step 4). Let
W be the closure of a point η of an integral scheme X over K, with its closed immersion ι, and y a
point of W with completion coordinates of the local ring of W at y. A section s of a Cartier
divisor D on X with local equation f at ι(y) has a local coefficient at ι(y); its image under the
stalk map of ι, expanded in the coordinates, is a K-linear map Ψ to power series. It is
multiplicative for products of sections, it does not change under principal shifts of D with the
matching local equations, and it kills the sections vanishing at η: the stalk map at the generic
point of W is local into a field, and the local ring of W at y embeds into the function field of
W. So the restrictions to the closure of η of a finite-dimensional space of sections have at least
the dimension of any finite-dimensional space of power series in the image of Ψ.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

omit [X.Over (Spec (CommRingCat.of K))] in
/-- Specialization of stalks is compatible with the maps to the function field. -/
theorem stalkSpecializes_algebraMap_functionField {x x' : X} (h : x' ⤳ x)
    (c : X.presheaf.stalk x) :
    algebraMap (X.presheaf.stalk x') X.functionField (X.presheaf.stalkSpecializes h c) =
      algebraMap (X.presheaf.stalk x) X.functionField c := by
  change X.presheaf.stalkSpecializes _ (X.presheaf.stalkSpecializes h c) =
    X.presheaf.stalkSpecializes _ c
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

variable (η : X)

/-- The stalk map of the closure of η at y, as a K-algebra map. -/
noncomputable def pointClosureStalkAlgHom (y : pointClosureScheme η) :
    X.presheaf.stalk (pointClosureι η y) →ₐ[K] (pointClosureScheme η).presheaf.stalk y where
  toRingHom := ((pointClosureι η).stalkMap y).hom
  commutes' k := by
    change (pointClosureι η).stalkMap y (X.presheaf.germ ⊤ (pointClosureι η y) trivial
        (Scheme.Modules.baseRingToGlobalSections K X k)) =
      (pointClosureScheme η).presheaf.germ ⊤ y trivial
        (Scheme.Modules.baseRingToGlobalSections K (pointClosureScheme η) k)
    rw [Scheme.Hom.germ_stalkMap_apply,
      ← scheme_appTop_baseRingToGlobalSections K (pointClosureι η) k]
    rfl

variable {η}

/-- The Taylor expansion at y of the restriction to the closure of η. -/
noncomputable def pointClosureTaylor (y : pointClosureScheme η) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K) :
    X.presheaf.stalk (pointClosureι η y) →ₐ[K] MvPowerSeries (Fin m) K :=
  coords.toAlgHom.comp ((IsScalarTower.toAlgHom K ((pointClosureScheme η).presheaf.stalk y)
    (AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y))).comp (pointClosureStalkAlgHom η y))

omit [IsIntegral X] in
theorem pointClosureTaylor_apply (y : pointClosureScheme η) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (a : X.presheaf.stalk (pointClosureι η y)) :
    pointClosureTaylor y coords a = coords (algebraMap ((pointClosureScheme η).presheaf.stalk y)
      (AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
        ((pointClosureScheme η).presheaf.stalk y)) ((pointClosureι η).stalkMap y a)) := rfl

/-- Sections of D, through their local coefficients at ι(y), restricted to the closure of η and
expanded at y. -/
noncomputable def pointClosureSectionTaylor (D : CartierDivisor X) (y : pointClosureScheme η)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K) :
    Γ(D.sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin m) K :=
  (pointClosureTaylor y coords).toLinearMap.comp
    ((cartierLocalCoefficient D (pointClosureι η y) f hf).restrictScalars K)

theorem pointClosureSectionTaylor_apply (D : CartierDivisor X) (y : pointClosureScheme η)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (s : Γ(D.sheaf, ⊤)) :
    pointClosureSectionTaylor D y f hf coords s =
      pointClosureTaylor y coords (cartierLocalCoefficient D (pointClosureι η y) f hf s) := rfl

/-- Products of sections go to products of power series. -/
theorem pointClosureSectionTaylor_product (D E : CartierDivisor X) (y : pointClosureScheme η)
    (f g : X.functionFieldˣ) (hf : D.IsLocalEquationAt (pointClosureι η y) f)
    (hg : E.IsLocalEquationAt (pointClosureι η y) g) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (s : Γ(D.sheaf, ⊤)) (t : Γ(E.sheaf, ⊤)) :
    pointClosureSectionTaylor (D + E) y (f * g) (hf.mul hg) coords (cartierSectionProduct D E s t) =
      pointClosureSectionTaylor D y f hf coords s * pointClosureSectionTaylor E y g hg coords t := by
  rw [pointClosureSectionTaylor_apply, pointClosureSectionTaylor_apply,
    pointClosureSectionTaylor_apply, cartierSectionProduct_localCoefficient, map_mul]

/-- The image of the product of two section spaces lies in the image of the sum divisor. -/
theorem pointClosureSectionTaylor_range_mul (D E : CartierDivisor X) (y : pointClosureScheme η)
    (f g : X.functionFieldˣ) (hf : D.IsLocalEquationAt (pointClosureι η y) f)
    (hg : E.IsLocalEquationAt (pointClosureι η y) g) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K) :
    LinearMap.range (pointClosureSectionTaylor D y f hf coords) *
        LinearMap.range (pointClosureSectionTaylor E y g hg coords) ≤
      LinearMap.range (pointClosureSectionTaylor (D + E) y (f * g) (hf.mul hg) coords) := by
  rw [Submodule.mul_le]
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  exact ⟨cartierSectionProduct D E s t, pointClosureSectionTaylor_product D E y f g hf hg coords s t⟩

/-- A principal shift of D with the matching local equation has the same image. -/
theorem pointClosureSectionTaylor_range_le_principal (D : CartierDivisor X)
    (y : pointClosureScheme η) (f G : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K) :
    LinearMap.range (pointClosureSectionTaylor D y f hf coords) ≤
      LinearMap.range (pointClosureSectionTaylor (D + principalCartierDivisor X G) y (f * G)
        (hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor _ G)) coords) := by
  rintro _ ⟨s, rfl⟩
  have hmem : (rationalFunctionsEquiv (X := X) ⊤).symm
      ((G⁻¹ : X.functionFieldˣ) * cartierSectionRational D s) ∈
        (D + principalCartierDivisor X G).sections ⊤ := by
    rw [cartierSections_mem_principalShift]
    have h := D.sheafι_app_mem ⊤ s
    convert h using 1
    apply (rationalFunctionsEquiv (X := X) ⊤).injective
    rw [rationalFunctionsEquiv_rationalFunctionsMul_app, LinearEquiv.apply_symm_apply,
      ← mul_assoc, Units.mul_inv, one_mul, cartierSectionRational_apply]
  refine ⟨CartierDivisor.sectionMk _ hmem, ?_⟩
  rw [pointClosureSectionTaylor_apply, pointClosureSectionTaylor_apply]
  congr 1
  apply IsFractionRing.injective (X.presheaf.stalk (pointClosureι η y)) X.functionField
  rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image,
    cartierSectionRational_sectionMk_of_mem, LinearEquiv.apply_symm_apply, Units.val_mul,
    mul_assoc, ← mul_assoc (G : X.functionField), Units.mul_inv, one_mul]

/-- Sections vanishing at η restrict to zero. -/
theorem pointClosureSectionTaylor_eq_zero_of_mem (D : CartierDivisor X)
    (y : pointClosureScheme η) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (s : Γ(D.sheaf, ⊤)) (hs : s ∈ cartierSectionsVanishingAt K D η) :
    pointClosureSectionTaylor D y f hf coords s = 0 := by
  have hspec : genericPoint (pointClosureScheme η) ⤳ y :=
    (genericPoint_spec (pointClosureScheme η)).specializes trivial
  have hspecX : pointClosureι η (genericPoint (pointClosureScheme η)) ⤳ pointClosureι η y :=
    hspec.map (pointClosureι η).continuous
  have hfξ : D.IsLocalEquationAt (pointClosureι η (genericPoint (pointClosureScheme η))) f := by
    obtain ⟨V, hyV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    have : Nonempty V := ⟨⟨_, hyV⟩⟩
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (hspecX.mem_open V.isOpen hyV)
  have hcξ : X.presheaf.stalkSpecializes hspecX
      (cartierLocalCoefficient D (pointClosureι η y) f hf s) =
        cartierLocalCoefficient D (pointClosureι η (genericPoint (pointClosureScheme η))) f hfξ s := by
    apply IsFractionRing.injective
      (X.presheaf.stalk (pointClosureι η (genericPoint (pointClosureScheme η)))) X.functionField
    rw [stalkSpecializes_algebraMap_functionField, cartierLocalCoefficient_image,
      cartierLocalCoefficient_image]
  have hs' : s ∈ cartierSectionsVanishingAt K D
      (pointClosureι η (genericPoint (pointClosureScheme η))) := by
    rw [pointClosureι_genericPoint]
    exact hs
  have hm := (mem_cartierSectionsVanishingAt_iff D _ f hfξ s).mp hs'
  have hW0 : (pointClosureι η).stalkMap (genericPoint (pointClosureScheme η))
      (cartierLocalCoefficient D (pointClosureι η (genericPoint (pointClosureScheme η))) f hfξ s) =
        0 := by
    have hle := IsLocalRing.map_maximalIdeal_le
      ((pointClosureι η).stalkMap (genericPoint (pointClosureScheme η))).hom
    have hmem := hle (Ideal.mem_map_of_mem _ hm)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at hmem
    exact hmem
  have hy0 : (pointClosureι η).stalkMap y (cartierLocalCoefficient D (pointClosureι η y) f hf s) =
      0 := by
    apply IsFractionRing.injective ((pointClosureScheme η).presheaf.stalk y)
      (pointClosureScheme η).functionField
    rw [map_zero]
    change (pointClosureScheme η).presheaf.stalkSpecializes _
      ((pointClosureι η).stalkMap y (cartierLocalCoefficient D (pointClosureι η y) f hf s)) = 0
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, hcξ]
    exact hW0
  rw [pointClosureSectionTaylor_apply, pointClosureTaylor_apply, hy0, map_zero, map_zero]

/-- A finite-dimensional space of power series in the image restricts: some finite-dimensional
subspace of sections of D restricts to the closure of η with at least its dimension. -/
theorem exists_le_cartierRestrictedSubspaceDim_of_le_range (D : CartierDivisor X)
    (y : pointClosureScheme η) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (U : Submodule K (MvPowerSeries (Fin m) K)) [FiniteDimensional K U]
    (hU : U ≤ LinearMap.range (pointClosureSectionTaylor D y f hf coords)) :
    ∃ V : Submodule K Γ(D.sheaf, ⊤), FiniteDimensional K V ∧
      Module.finrank K U ≤ cartierRestrictedSubspaceDim K D η V := by
  classical
  set Ψ := pointClosureSectionTaylor D y f hf coords
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule K U).FG)
  have hlift : ∀ u : U, ∃ s : Γ(D.sheaf, ⊤), Ψ s = u := fun u => hU u.2
  choose lift hlift using hlift
  have hVfin : FiniteDimensional K (Submodule.span K (lift '' S)) :=
    FiniteDimensional.span_of_finite K (S.finite_toSet.image lift)
  refine ⟨Submodule.span K (lift '' S), hVfin, ?_⟩
  set Q := cartierSectionsVanishingAt K D η
  have hker : Q ≤ LinearMap.ker Ψ := fun s hs =>
    pointClosureSectionTaylor_eq_zero_of_mem D y f hf coords s hs
  have h1 : U = (Submodule.span K (S : Set U)).map U.subtype := by
    rw [hS, Submodule.map_top, Submodule.range_subtype]
  have h2 : (Submodule.span K (S : Set U)).map U.subtype ≤
      Submodule.span K (Ψ '' (lift '' S)) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.subset_span ⟨lift u, ⟨u, hu, rfl⟩, hlift u⟩
  have hUle : U ≤ ((Submodule.span K (lift '' S)).map Q.mkQ).map (Q.liftQ Ψ hker) := by
    rw [← Submodule.map_comp, Submodule.liftQ_mkQ, Submodule.map_span]
    calc U = _ := h1
      _ ≤ _ := h2
  unfold cartierRestrictedSubspaceDim
  calc Module.finrank K U ≤
        Module.finrank K (((Submodule.span K (lift '' S)).map Q.mkQ).map (Q.liftQ Ψ hker)) :=
        Submodule.finrank_mono hUle
    _ ≤ Module.finrank K ((Submodule.span K (lift '' S)).map Q.mkQ) :=
        Submodule.finrank_map_le _ _

end MixedFujita

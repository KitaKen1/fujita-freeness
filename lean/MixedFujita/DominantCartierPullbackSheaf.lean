/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierNefPullback
public import MixedFujita.ModuleLocalPullbackCoefficients
public import MixedFujita.ModuleOpenFrameCoefficients
public import MixedFujita.CartierOpenCoefficient

/-!
The module pullback of the sheaf of every Cartier divisor along a dominant morphism (step 10, R0′).

Let `ρ : T → X` be a dominant morphism of integral schemes and `D` a Cartier divisor of `X`; no
ample divisor and no global section is assumed. Pull back the frame of `O(D)` given by an equation
`f₀` of `D` on a nonempty open `U₀`: it trivializes `ρ*O(D)` on the dense open `ρ⁻¹U₀`, and
TauCeti's rational embedding gives a Cartier divisor `E` with `ρ*O(D) ≅ O(E)` whose restriction
to the domain of every trivialization is the class of its inverse rational basis function
(`Scheme.Modules.exists_cartierDivisor_restrict_eq`). For the pulled frame of an equation `f₁` on
`U₁`, the basis section is the pullback of the basis section of `O(D)` (rational function `f₁⁻¹`),
which on `U₀ ⊓ U₁` is `(f₀/f₁)` times the one of `U₀`; hence its rational basis function is
`φ(f₀/f₁)` (`trivializationGeneratorRationalUnit_cartierPullbackOpen`). So `E` has the local
equation `φ(f₁)·φ(f₀)⁻¹` everywhere, `E = ρ*D + div(φ(f₀)⁻¹)`, and
`ρ*O(D) ≅ O(ρ*D)` (`cartierPullback_sheaf_iso_modulePullback_of_dominant`).

Consequently degrees along curves are compatible with pullback and the pullback of a nef divisor
along a dominant morphism over the base field is nef, without an ample divisor on the target
(`cartierIsNef_cartierPullback_of_dominant`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Frames

variable {X : Scheme.{u}}

/-- The rank-one trivialization of a module frame. -/
noncomputable def overFrameTrivialization (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U :=
  (e ≪≫ (TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).symm).symm

/-- In a frame, a section with coefficient one generates: every section is its coefficient times
the restricted section. -/
theorem eq_moduleOverFrameCoefficient_smul (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (s : Γ(M, U))
    (hs : moduleOverFrameCoefficient M U e U le_rfl s = 1) {W : X.Opens} (i : W ⟶ U)
    (v : Γ(M, W)) :
    v = moduleOverFrameCoefficient M U e W i.le v • M.presheaf.map i.op s := by
  apply (moduleOverFrameCoefficient M U e W i.le).injective
  rw [LinearEquiv.map_smul, moduleOverFrameCoefficient_restrict M U e le_rfl i s, hs, map_one,
    smul_eq_mul, mul_one]

/-- A frame section with coefficient one is a regular unit times the basis section of any
rank-one trivialization on the same open. -/
theorem exists_unit_smul_trivializationGenerator (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (s : Γ(M, U))
    (hs : moduleOverFrameCoefficient M U e U le_rfl s = 1)
    (t : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    ∃ r : Γ(X, U)ˣ, s = (r : Γ(X, U)) • Scheme.Modules.trivializationGenerator M t := by
  obtain ⟨r₁, h₁⟩ : ∃ r₁ : Γ(X, U), s = r₁ • Scheme.Modules.trivializationGenerator M t := by
    have h := Scheme.Modules.eq_trivializationCoordinate_smul_map_trivializationGenerator M t
      (𝟙 U) s
    rw [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h
    exact ⟨_, h⟩
  have h₂ := eq_moduleOverFrameCoefficient_smul M U e s hs (𝟙 U)
    (Scheme.Modules.trivializationGenerator M t)
  rw [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] at h₂
  have hrc : r₁ * moduleOverFrameCoefficient M U e U (𝟙 U).le
      (Scheme.Modules.trivializationGenerator M t) = 1 := by
    have h3 : moduleOverFrameCoefficient M U e U le_rfl s =
        moduleOverFrameCoefficient M U e U le_rfl ((r₁ * moduleOverFrameCoefficient M U e U
          (𝟙 U).le (Scheme.Modules.trivializationGenerator M t)) • s) := by
      rw [← smul_smul, ← h₂, ← h₁]
    rw [LinearEquiv.map_smul, hs, smul_eq_mul, mul_one] at h3
    exact h3.symm
  exact ⟨Units.mkOfMulEqOne _ _ hrc, h₁⟩

end Frames

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

section Generator

/-- The basis section of `O(D)` over an open subset carrying an equation `f` of `D`. -/
noncomputable def cartierOpenGenerator (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    Γ(D.sheaf, U) :=
  (LinearEquiv.ofBijective (cartierOpenCoefficient D U f hf U le_rfl)
    (cartierOpenCoefficient_bijective D U f hf U le_rfl)).symm 1

theorem cartierOpenCoefficient_cartierOpenGenerator (D : CartierDivisor X) (U : X.Opens)
    [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    cartierOpenCoefficient D U f hf U le_rfl (cartierOpenGenerator D U f hf) = 1 := by
  have h := (LinearEquiv.ofBijective (cartierOpenCoefficient D U f hf U le_rfl)
    (cartierOpenCoefficient_bijective D U f hf U le_rfl)).apply_symm_apply 1
  rw [LinearEquiv.ofBijective_apply] at h
  exact h

/-- Rational functions of sections of `O(D)` do not change under restriction. -/
theorem cartierSheafRational_restrict (D : CartierDivisor X) {U V : X.Opens} [Nonempty U]
    [Nonempty V] (i : V ⟶ U) (s : Γ(D.sheaf, U)) :
    rationalFunctionsEquiv V (Scheme.Modules.Hom.app D.sheafι V (D.sheaf.presheaf.map i.op s)) =
      rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U s) := by
  have h := ConcreteCategory.congr_hom (D.sheafι.mapPresheaf.naturality i.op) s
  change Scheme.Modules.Hom.app D.sheafι V (D.sheaf.presheaf.map i.op s) =
    (rationalFunctions X).presheaf.map i.op (Scheme.Modules.Hom.app D.sheafι U s) at h
  rw [h, rationalFunctionsEquiv_map]

/-- The rational function of the basis section of an equation `f` is `f⁻¹`. -/
theorem cartierOpenGenerator_rational (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    rationalFunctionsEquiv U (Scheme.Modules.Hom.app D.sheafι U (cartierOpenGenerator D U f hf)) =
      (f : X.functionField)⁻¹ := by
  have h := cartierOpenCoefficient_image D U f hf U le_rfl (cartierOpenGenerator D U f hf)
  rw [cartierOpenCoefficient_cartierOpenGenerator, map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **Transition of the basis sections of two equations**: on `U₀ ⊓ U₁` the basis section of
`f₁` is a regular multiple of the one of `f₀`, with rational coefficient `f₀ / f₁`. -/
theorem exists_cartierOpenGenerator_transition (D : CartierDivisor X) (U₀ U₁ : X.Opens)
    [Nonempty U₀] [Nonempty U₁] [Nonempty (U₀ ⊓ U₁ : X.Opens)] (f₀ f₁ : X.functionFieldˣ)
    (hf₀ : rationalUnitClass X U₀ (Additive.ofMul f₀) = D |_ U₀)
    (hf₁ : rationalUnitClass X U₁ (Additive.ofMul f₁) = D |_ U₁) :
    ∃ c : Γ(X, U₀ ⊓ U₁),
      D.sheaf.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op
          (cartierOpenGenerator D U₁ f₁ hf₁) =
        c • D.sheaf.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op
          (cartierOpenGenerator D U₀ f₀ hf₀) ∧
      X.germToFunctionField (U₀ ⊓ U₁) c = (f₀ : X.functionField) * (f₁ : X.functionField)⁻¹ := by
  let s₁ := D.sheaf.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op
    (cartierOpenGenerator D U₁ f₁ hf₁)
  refine ⟨cartierOpenCoefficient D U₀ f₀ hf₀ (U₀ ⊓ U₁) inf_le_left s₁, ?_, ?_⟩
  · apply (cartierOpenCoefficient_bijective D U₀ f₀ hf₀ (U₀ ⊓ U₁) inf_le_left).1
    rw [map_smul, cartierOpenCoefficient_restrict D U₀ f₀ hf₀ le_rfl
      (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)), cartierOpenCoefficient_cartierOpenGenerator,
      map_one, smul_eq_mul, mul_one]
  · rw [cartierOpenCoefficient_image, cartierSheafRational_restrict, cartierOpenGenerator_rational]

end Generator

section Pullback

variable (ρ : T ⟶ X) [IsDominant ρ] (D : CartierDivisor X)

/-- The frame of `ρ*O(D)` over `ρ⁻¹U` pulled back from an equation of `D` on `U`. -/
noncomputable def cartierPullbackOpenFrame (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    ((Scheme.Modules.pullback ρ).obj D.sheaf).over (ρ ⁻¹ᵁ U) ≅
      SheafOfModules.unit (T.ringCatSheaf.over (ρ ⁻¹ᵁ U)) :=
  moduleRestrictFrameOverIso _ (ρ ⁻¹ᵁ U)
    (moduleLocalPullbackFrameIso ρ D.sheaf U (cartierOpenRestrictFrameIso D U f hf))

omit [IsIntegral T] [IsDominant ρ] in
/-- The pullback of the basis section of `O(D)` has coefficient one in the pulled frame. -/
theorem cartierPullbackOpenFrame_coefficient_generator (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    moduleOverFrameCoefficient _ (ρ ⁻¹ᵁ U) (cartierPullbackOpenFrame ρ D U f hf) (ρ ⁻¹ᵁ U) le_rfl
      (modulePullbackSections ρ D.sheaf U (cartierOpenGenerator D U f hf)) = 1 := by
  unfold cartierPullbackOpenFrame
  rw [modulePullbackSections_local_frame_coefficient,
    show moduleRestrictFrameOverIso D.sheaf U (cartierOpenRestrictFrameIso D U f hf) =
      cartierOpenFrameIso D U f hf from
        moduleRestrictFrameOverIso_roundTrip D.sheaf U (cartierOpenFrameIso D U f hf)]
  change ρ.app U (cartierOpenCoefficient D U f hf U le_rfl (cartierOpenGenerator D U f hf)) = 1
  rw [cartierOpenCoefficient_cartierOpenGenerator, map_one]

/-- **The rational function of a pulled basis section**: relative to any dense trivialization,
the pullback of the basis section of `f₁` is `φ(f₀ / f₁)` times the pullback of the basis section
of `f₀`. -/
theorem rationalFunction_cartierPullbackGenerator (U₀ U₁ : X.Opens) [Nonempty U₀] [Nonempty U₁]
    (f₀ f₁ : X.functionFieldˣ) (hf₀ : rationalUnitClass X U₀ (Additive.ofMul f₀) = D |_ U₀)
    (hf₁ : rationalUnitClass X U₁ (Additive.ofMul f₁) = D |_ U₁) {V : T.Opens}
    (e : SheafOfModules.free (R := T.ringCatSheaf.over V) PUnit ≅
      ((Scheme.Modules.pullback ρ).obj D.sheaf).over V)
    (hU : Dense (V : Set T)) [Nonempty (ρ ⁻¹ᵁ U₀)] [Nonempty (ρ ⁻¹ᵁ U₁)] :
    Scheme.Modules.rationalFunction _ e hU (ρ ⁻¹ᵁ U₁)
        (modulePullbackSections ρ D.sheaf U₁ (cartierOpenGenerator D U₁ f₁ hf₁)) =
      (dominantFunctionFieldMap ρ).hom ((f₀ : X.functionField) * (f₁ : X.functionField)⁻¹) *
        Scheme.Modules.rationalFunction _ e hU (ρ ⁻¹ᵁ U₀)
          (modulePullbackSections ρ D.sheaf U₀ (cartierOpenGenerator D U₀ f₀ hf₀)) := by
  have : Nonempty (U₀ ⊓ U₁ : X.Opens) := by
    simpa using nonempty_preirreducible_inter U₀.isOpen U₁.isOpen
      (by simpa using (inferInstance : Nonempty U₀)) (by simpa using (inferInstance : Nonempty U₁))
  have : Nonempty (ρ ⁻¹ᵁ (U₀ ⊓ U₁)) := dominant_preimage_nonempty ρ _
  obtain ⟨c, hc, hgerm⟩ := exists_cartierOpenGenerator_transition D U₀ U₁ f₀ f₁ hf₀ hf₁
  rw [← Scheme.Modules.rationalFunction_map _ e hU
      ((Opens.map ρ.base).map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)))
      (modulePullbackSections ρ D.sheaf U₁ (cartierOpenGenerator D U₁ f₁ hf₁)),
    ← modulePullbackSections_restrict, hc, modulePullbackSections_smul,
    Scheme.Modules.rationalFunction_smul, modulePullbackSections_restrict,
    Scheme.Modules.rationalFunction_map]
  congr 1
  have hφ := dominantFunctionFieldMap_germ ρ (U₀ ⊓ U₁) (ρ ⁻¹ᵁ (U₀ ⊓ U₁)) le_rfl c
  simp only [Scheme.Hom.appLE_eq_app] at hφ
  rw [← hφ, hgerm]

/-- **The module pullback of the sheaf of every Cartier divisor along a dominant morphism is the
sheaf of the pullback divisor**: no ample divisor and no global section is needed. -/
theorem cartierPullback_sheaf_iso_modulePullback_of_dominant :
    Nonempty ((Scheme.Modules.pullback ρ).obj D.sheaf ≅ (cartierPullback ρ D).sheaf) := by
  obtain ⟨f₀, hf₀⟩ := D.exists_isLocalEquationAt (genericPoint X)
  obtain ⟨U₀, hx₀, hU₀⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf₀
  have : Nonempty U₀ := ⟨⟨_, hx₀⟩⟩
  have hne : Nonempty (ρ ⁻¹ᵁ U₀) := dominant_preimage_nonempty ρ U₀
  have hU : Dense ((ρ ⁻¹ᵁ U₀ : T.Opens) : Set T) := by
    obtain ⟨⟨t, ht⟩⟩ := hne
    exact (ρ ⁻¹ᵁ U₀).isOpen.dense ⟨t, ht⟩
  have := cartierPullbackSheaf_isInvertible D ρ
  let M := (Scheme.Modules.pullback ρ).obj D.sheaf
  let e₀ := overFrameTrivialization M (ρ ⁻¹ᵁ U₀) (cartierPullbackOpenFrame ρ D U₀ f₀ hU₀)
  obtain ⟨E, hE⟩ := Scheme.Modules.exists_cartierDivisor_restrict_eq M e₀ hU
  let a := CartierDivisor.isoSheafOfRestrictEq hE
  let s₀ := modulePullbackSections ρ D.sheaf U₀ (cartierOpenGenerator D U₀ f₀ hU₀)
  obtain ⟨r', hr'⟩ := exists_unit_smul_trivializationGenerator M (ρ ⁻¹ᵁ U₀)
    (cartierPullbackOpenFrame ρ D U₀ f₀ hU₀) s₀
    (cartierPullbackOpenFrame_coefficient_generator ρ D U₀ f₀ hU₀) e₀
  let r₀ : T.functionFieldˣ :=
    Units.map (T.germToFunctionField (ρ ⁻¹ᵁ U₀)).hom.toMonoidHom r' *
      Scheme.Modules.trivializationGeneratorRationalUnit M e₀ hU e₀
  have hr₀ : (r₀ : T.functionField) = Scheme.Modules.rationalFunction M e₀ hU (ρ ⁻¹ᵁ U₀) s₀ := by
    rw [hr', Scheme.Modules.rationalFunction_smul, Units.val_mul, Units.coe_map,
      Scheme.Modules.coe_trivializationGeneratorRationalUnit]
    rfl
  let φf : X.functionFieldˣ →* T.functionFieldˣ :=
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
  let h : T.functionFieldˣ := (φf f₀ * r₀)⁻¹
  have hEq : E = cartierPullback ρ D + principalCartierDivisor T h := by
    apply cartierDivisor_eq_of_isLocalEquationAt
    intro t
    obtain ⟨f₁, hf₁⟩ := D.exists_isLocalEquationAt (ρ t)
    obtain ⟨U₁, ht₁, hU₁⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf₁
    have : Nonempty U₁ := ⟨⟨_, ht₁⟩⟩
    have : Nonempty (ρ ⁻¹ᵁ U₁) := ⟨⟨t, ht₁⟩⟩
    refine ⟨φf f₁ * h, ?_, (cartierPullback_isLocalEquationAt ρ D t hf₁).mul
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor t h)⟩
    let t₁ := overFrameTrivialization M (ρ ⁻¹ᵁ U₁) (cartierPullbackOpenFrame ρ D U₁ f₁ hU₁)
    let s₁ := modulePullbackSections ρ D.sheaf U₁ (cartierOpenGenerator D U₁ f₁ hU₁)
    obtain ⟨r, hr⟩ := exists_unit_smul_trivializationGenerator M (ρ ⁻¹ᵁ U₁)
      (cartierPullbackOpenFrame ρ D U₁ f₁ hU₁) s₁
      (cartierPullbackOpenFrame_coefficient_generator ρ D U₁ f₁ hU₁) t₁
    have hrat : Scheme.Modules.rationalFunction M e₀ hU (ρ ⁻¹ᵁ U₁) s₁ =
        T.germToFunctionField (ρ ⁻¹ᵁ U₁) (r : Γ(T, ρ ⁻¹ᵁ U₁)) *
          (Scheme.Modules.trivializationGeneratorRationalUnit M e₀ hU t₁ : T.functionField) := by
      rw [hr, Scheme.Modules.rationalFunction_smul,
        Scheme.Modules.coe_trivializationGeneratorRationalUnit]
    have hcomp := rationalFunction_cartierPullbackGenerator ρ D U₀ U₁ f₀ f₁ hU₀ hU₁ e₀ hU
    have hgen : Scheme.Modules.trivializationGeneratorRationalUnit M e₀ hU t₁ =
        (Units.map (T.germToFunctionField (ρ ⁻¹ᵁ U₁)).hom r)⁻¹ * (φf f₁ * h)⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, Units.coe_map]
      change T.germToFunctionField (ρ ⁻¹ᵁ U₁) (r : Γ(T, ρ ⁻¹ᵁ U₁)) * _ = _
      rw [← hrat, hcomp]
      simp only [h, φf, mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.coe_map, hr₀]
      simp only [MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe, map_mul, map_inv₀]
      ring
    have h1 := hE (ρ ⁻¹ᵁ U₁) t₁
    rw [hgen, ofMul_mul, ofMul_inv, ofMul_inv, neg_add, neg_neg, neg_neg, map_add,
      rationalUnitClass_germToFunctionField_eq_zero T (ρ ⁻¹ᵁ U₁) r, zero_add] at h1
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq h1.symm ht₁
  exact ⟨a ≪≫ eqToIso (congrArg CartierDivisor.sheaf hEq) ≪≫
    cartierSheafPrincipalShiftIso (cartierPullback ρ D) h⟩

end Pullback

section Degree

variable {K : Type u} [Field K]

/-- The degree along a curve `ψ` of `ρ*D` is the degree of `D` along `ψ ≫ ρ`, for every Cartier
divisor `D`. -/
theorem cartierCurvePullbackDegree_cartierPullback_of_dominant {C : Scheme.{u}} [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (ρ : T ⟶ X) [IsDominant ρ] (ψ : C ⟶ T) (D : CartierDivisor X) :
    cartierCurvePullbackDegree (K := K) (cartierPullback ρ D) ψ =
      cartierCurvePullbackDegree (K := K) D (ψ ≫ ρ) := by
  obtain ⟨e⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant ρ D
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D (ψ ≫ ρ)
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hC D (ψ ≫ ρ) A a,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hC (cartierPullback ρ D) ψ A
      ((Scheme.Modules.pullback ψ).mapIso e.symm ≪≫
        (Scheme.Modules.pullbackComp ψ ρ).app D.sheaf ≪≫ a)]

variable [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

/-- **The pullback of a nef divisor along a dominant morphism over the base field is nef**, with
no ample divisor on the target. -/
theorem cartierIsNef_cartierPullback_of_dominant (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] {N : CartierDivisor X} (hN : CartierIsNef K N) :
    CartierIsNef K (cartierPullback ρ N) := by
  intro C _ _ _ _ hC ψ hψ
  rw [cartierCurvePullbackDegree_cartierPullback_of_dominant (K := K) hC ρ ψ N]
  have hover : (ψ ≫ ρ) ≫ (X ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) := by
    rw [Category.assoc, HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)), hψ]
  exact hN C hC (ψ ≫ ρ) hover

end Degree

end MixedFujita

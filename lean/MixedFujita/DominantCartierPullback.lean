/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularEquationCartier
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import TauCeti.AlgebraicGeometry.CartierDivisor.LocalEquations

/-!
Pullback of Cartier divisors along dominant morphisms of integral schemes (step 6). A dominant
morphism ρ : T → X of integral schemes sends the generic point to the generic point, so the stalk
maps give a map of function fields φ : K(X) → K(T), compatible with the pullback of sections.
Local equations are stable under regular units, and two Cartier divisors with a common local
equation at every point are equal (the Cartier divisors form a sheaf). Local equations f_x of D on
neighbourhoods V_x of the points x of X give φ(f_x) on ρ⁻¹(V_x); their ratios are images of units
of the sections, so they glue to a Cartier divisor ρ*D, and φ(f) is a local equation of ρ*D at t
for every local equation f of D at ρ(t). The pullback is additive and sends div f to div φ(f).
This gives ρ*L on a resolution and the relative canonical divisor K_{T/X} = K_T - ρ*K_X.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section LocalEquations

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- Multiplying a local equation by a regular unit near the point gives a local equation. -/
theorem isLocalEquationAt_regularUnit_mul {D : CartierDivisor Y} {t : Y} {g : Y.functionFieldˣ}
    (hg : D.IsLocalEquationAt t g) (W : Y.Opens) (ht : t ∈ W) [Nonempty W] (r : Γ(Y, W)ˣ) :
    D.IsLocalEquationAt t (regularUnitToFunctionField Y W r * g) := by
  obtain ⟨V, htV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hg
  have : Nonempty V := ⟨⟨t, htV⟩⟩
  have : Nonempty (V ⊓ W : Y.Opens) := ⟨⟨t, htV, ht⟩⟩
  refine CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (V := V ⊓ W) ?_ ⟨htV, ht⟩
  rw [← CartierDivisor.rationalUnitClass_eq_of_le inf_le_left hV,
    rationalUnitClass_eq_rationalUnitClass_iff]
  refine ⟨Units.map (Y.presheaf.map (homOfLE inf_le_right : (V ⊓ W : Y.Opens) ⟶ W).op).hom.toMonoidHom
    r, ?_⟩
  congr 1
  apply Units.ext
  rw [regularUnitToFunctionField_apply, regularUnitToFunctionField_apply, Units.coe_map,
    Units.coe_map, Units.coe_map]
  exact germToFunctionField_restrict Y inf_le_right (r : Γ(Y, W))

/-- Two Cartier divisors with a common local equation at every point are equal. -/
theorem cartierDivisor_eq_of_isLocalEquationAt {D E : CartierDivisor Y}
    (h : ∀ t : Y, ∃ f : Y.functionFieldˣ, D.IsLocalEquationAt t f ∧ E.IsLocalEquationAt t f) :
    D = E := by
  have key : ∀ t : Y, ∃ W : Y.Opens, t ∈ W ∧ D |_ W = E |_ W := by
    intro t
    obtain ⟨f, hD, hE⟩ := h t
    obtain ⟨V, htV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hD
    obtain ⟨V', htV', hV'⟩ := CartierDivisor.isLocalEquationAt_iff.mp hE
    have : Nonempty V := ⟨⟨t, htV⟩⟩
    have : Nonempty V' := ⟨⟨t, htV'⟩⟩
    have : Nonempty (V ⊓ V' : Y.Opens) := ⟨⟨t, htV, htV'⟩⟩
    refine ⟨V ⊓ V', ⟨htV, htV'⟩, ?_⟩
    rw [← CartierDivisor.rationalUnitClass_eq_of_le inf_le_left hV,
      ← CartierDivisor.rationalUnitClass_eq_of_le inf_le_right hV']
  choose W hW hDE using key
  refine (cartierDivisorSheaf Y).eq_of_locally_eq' W ⊤ (fun t => homOfLE le_top) ?_ D E hDE
  intro t _
  exact Opens.mem_iSup.mpr ⟨t, hW t⟩

end LocalEquations

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]

section FunctionField

/-- A dominant morphism of integral schemes sends the generic point to the generic point. -/
theorem dominant_map_genericPoint (ρ : T ⟶ X) [IsDominant ρ] :
    ρ (genericPoint T) = genericPoint X := by
  have h := (genericPoint_spec T).image ρ.continuous
  have hcl : closure (ρ '' (Set.univ : Set T)) = Set.univ := by
    rw [Set.image_univ]
    exact ρ.denseRange.closure_range
  rw [hcl] at h
  exact h.eq (genericPoint_spec X)

omit [IsIntegral X] [IsIntegral T] in
/-- The preimage of a nonempty open subset under a dominant morphism is nonempty. -/
theorem dominant_preimage_nonempty (ρ : T ⟶ X) [IsDominant ρ] (V : X.Opens) [Nonempty V] :
    Nonempty (ρ ⁻¹ᵁ V) := by
  obtain ⟨⟨x, hx⟩⟩ := (inferInstance : Nonempty V)
  obtain ⟨t, ht⟩ := ρ.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
  exact ⟨⟨t, ht⟩⟩

/-- The map of function fields of a dominant morphism. -/
noncomputable def dominantFunctionFieldMap (ρ : T ⟶ X) [IsDominant ρ] :
    X.functionField ⟶ T.functionField :=
  X.presheaf.stalkSpecializes (specializes_of_eq (dominant_map_genericPoint ρ)) ≫
    ρ.stalkMap (genericPoint T)

/-- The function field map is compatible with the pullback of sections. -/
theorem dominantFunctionFieldMap_germ (ρ : T ⟶ X) [IsDominant ρ] (V : X.Opens) [Nonempty V]
    (V' : T.Opens) [Nonempty V'] (e : V' ≤ ρ ⁻¹ᵁ V) (s : Γ(X, V)) :
    (dominantFunctionFieldMap ρ).hom (X.germToFunctionField V s) =
      T.germToFunctionField V' (ρ.appLE V V' e s) := by
  have hmem : ρ (genericPoint T) ∈ V := by
    rw [dominant_map_genericPoint]
    exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using
      (inferInstance : Nonempty V))
  change ρ.stalkMap (genericPoint T) (X.presheaf.stalkSpecializes _
      (X.presheaf.germ V (genericPoint X) _ s)) =
    T.presheaf.germ V' (genericPoint T) _ (ρ.appLE V V' e s)
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply,
    Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- The image of a regular unit. -/
theorem dominantFunctionFieldMap_regularUnit (ρ : T ⟶ X) [IsDominant ρ] (V : X.Opens) [Nonempty V]
    (V' : T.Opens) [Nonempty V'] (e : V' ≤ ρ ⁻¹ᵁ V) (r : Γ(X, V)ˣ) :
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (regularUnitToFunctionField X V r) =
      regularUnitToFunctionField T V' (Units.map (ρ.appLE V V' e).hom.toMonoidHom r) := by
  apply Units.ext
  rw [Units.coe_map, regularUnitToFunctionField_apply, regularUnitToFunctionField_apply,
    Units.coe_map, Units.coe_map, Units.coe_map]
  exact dominantFunctionFieldMap_germ ρ V V' e (r : Γ(X, V))

end FunctionField

section Pullback

variable (ρ : T ⟶ X) [IsDominant ρ]

/-- A chosen local equation of D at x. -/
noncomputable def cartierChosenEquation (D : CartierDivisor X) (x : X) : X.functionFieldˣ :=
  Classical.choose (D.exists_isLocalEquationAt x)

theorem cartierChosenEquation_spec (D : CartierDivisor X) (x : X) :
    D.IsLocalEquationAt x (cartierChosenEquation D x) :=
  Classical.choose_spec (D.exists_isLocalEquationAt x)

/-- The open neighbourhood of x on which the chosen local equation holds. -/
noncomputable def cartierChosenOpen (D : CartierDivisor X) (x : X) : X.Opens :=
  Classical.choose (CartierDivisor.isLocalEquationAt_iff.mp (cartierChosenEquation_spec D x))

theorem mem_cartierChosenOpen (D : CartierDivisor X) (x : X) : x ∈ cartierChosenOpen D x :=
  (Classical.choose_spec
    (CartierDivisor.isLocalEquationAt_iff.mp (cartierChosenEquation_spec D x))).choose

instance cartierChosenOpen_nonempty (D : CartierDivisor X) (x : X) :
    Nonempty (cartierChosenOpen D x) :=
  ⟨⟨x, mem_cartierChosenOpen D x⟩⟩

theorem cartierChosenOpen_spec (D : CartierDivisor X) (x : X) :
    rationalUnitClass X (cartierChosenOpen D x) (Additive.ofMul (cartierChosenEquation D x)) =
      D |_ (cartierChosenOpen D x) :=
  (Classical.choose_spec
    (CartierDivisor.isLocalEquationAt_iff.mp (cartierChosenEquation_spec D x))).choose_spec

instance cartierPullbackOpen_nonempty (D : CartierDivisor X) (x : X) :
    Nonempty (ρ ⁻¹ᵁ cartierChosenOpen D x) :=
  dominant_preimage_nonempty ρ _

/-- The pulled-back equations differ by units of the sections on the overlaps. -/
theorem cartierPullback_transition (D : CartierDivisor X) (x y : X) :
    letI := integral_opens_inter_nonempty T (ρ ⁻¹ᵁ cartierChosenOpen D x)
      (ρ ⁻¹ᵁ cartierChosenOpen D y)
    ∃ w : Γ(T, ρ ⁻¹ᵁ cartierChosenOpen D x ⊓ ρ ⁻¹ᵁ cartierChosenOpen D y)ˣ,
      Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierChosenEquation D x) =
        Units.map (T.germToFunctionField
          (ρ ⁻¹ᵁ cartierChosenOpen D x ⊓ ρ ⁻¹ᵁ cartierChosenOpen D y)).hom w *
          Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierChosenEquation D y) := by
  let _ := integral_opens_inter_nonempty T (ρ ⁻¹ᵁ cartierChosenOpen D x)
    (ρ ⁻¹ᵁ cartierChosenOpen D y)
  let _ := integral_opens_inter_nonempty X (cartierChosenOpen D x) (cartierChosenOpen D y)
  have hclass : rationalUnitClass X (cartierChosenOpen D x ⊓ cartierChosenOpen D y)
      (Additive.ofMul (cartierChosenEquation D x)) =
        rationalUnitClass X (cartierChosenOpen D x ⊓ cartierChosenOpen D y)
          (Additive.ofMul (cartierChosenEquation D y)) := by
    rw [CartierDivisor.rationalUnitClass_eq_of_le inf_le_left (cartierChosenOpen_spec D x),
      CartierDivisor.rationalUnitClass_eq_of_le inf_le_right (cartierChosenOpen_spec D y)]
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X _ _ _).mp hclass
  have e : ρ ⁻¹ᵁ cartierChosenOpen D x ⊓ ρ ⁻¹ᵁ cartierChosenOpen D y ≤
      ρ ⁻¹ᵁ (cartierChosenOpen D x ⊓ cartierChosenOpen D y) := fun t ht => ht
  refine ⟨Units.map (ρ.appLE _ _ e).hom.toMonoidHom r, ?_⟩
  rw [← hr, map_mul, dominantFunctionFieldMap_regularUnit ρ _ _ e r,
    regularUnitToFunctionField_apply]
  rfl

omit [IsIntegral T] [IsDominant ρ] in
theorem cartierPullback_cover (D : CartierDivisor X) :
    iSup (fun x : X => ρ ⁻¹ᵁ cartierChosenOpen D x) = ⊤ := by
  apply top_unique
  intro t _
  exact Opens.mem_iSup.mpr ⟨ρ t, mem_cartierChosenOpen D (ρ t)⟩

/-- The pullback ρ*D of a Cartier divisor along a dominant morphism of integral schemes. -/
noncomputable def cartierPullback (D : CartierDivisor X) : CartierDivisor T :=
  (cartierDivisor_existsUnique_of_rationalUnits T (fun x : X => ρ ⁻¹ᵁ cartierChosenOpen D x)
    (cartierPullback_cover ρ D)
    (fun x => Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierChosenEquation D x))
    (fun x y => cartierPullback_transition ρ D x y)).exists.choose

theorem cartierPullback_restrict (D : CartierDivisor X) (x : X) :
    (cartierDivisorSheaf T).1.map (homOfLE (show ρ ⁻¹ᵁ cartierChosenOpen D x ≤ ⊤ from le_top)).op
        (cartierPullback ρ D) =
      rationalUnitClass T (ρ ⁻¹ᵁ cartierChosenOpen D x)
        (Additive.ofMul (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
          (cartierChosenEquation D x))) :=
  (cartierDivisor_existsUnique_of_rationalUnits T (fun x : X => ρ ⁻¹ᵁ cartierChosenOpen D x)
    (cartierPullback_cover ρ D)
    (fun x => Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierChosenEquation D x))
    (fun x y => cartierPullback_transition ρ D x y)).exists.choose_spec x

/-- The image φ(f) of a local equation f of D at ρ(t) is a local equation of ρ*D at t. -/
theorem cartierPullback_isLocalEquationAt (D : CartierDivisor X) (t : T) {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt (ρ t) f) :
    (cartierPullback ρ D).IsLocalEquationAt t
      (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f) := by
  have h0 : (cartierPullback ρ D).IsLocalEquationAt t
      (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierChosenEquation D (ρ t))) :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
      (cartierPullback_restrict ρ D (ρ t)).symm (mem_cartierChosenOpen D (ρ t))
  -- f and the chosen equation differ by a regular unit near ρ(t)
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty V := ⟨⟨ρ t, hxV⟩⟩
  have hmem : ρ t ∈ V ⊓ cartierChosenOpen D (ρ t) := ⟨hxV, mem_cartierChosenOpen D (ρ t)⟩
  have : Nonempty (V ⊓ cartierChosenOpen D (ρ t) : X.Opens) := ⟨⟨ρ t, hmem⟩⟩
  obtain ⟨r, hr⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X
    (V ⊓ cartierChosenOpen D (ρ t)) f (cartierChosenEquation D (ρ t))).mp
      ((CartierDivisor.rationalUnitClass_eq_of_le inf_le_left hV).trans
        (CartierDivisor.rationalUnitClass_eq_of_le inf_le_right
          (cartierChosenOpen_spec D (ρ t))).symm)
  have : Nonempty (ρ ⁻¹ᵁ (V ⊓ cartierChosenOpen D (ρ t))) := dominant_preimage_nonempty ρ _
  have h1 := isLocalEquationAt_regularUnit_mul h0 (ρ ⁻¹ᵁ (V ⊓ cartierChosenOpen D (ρ t))) hmem
    (Units.map (ρ.appLE _ _ le_rfl).hom.toMonoidHom r)
  rw [← dominantFunctionFieldMap_regularUnit ρ _ _ le_rfl r, ← map_mul, hr] at h1
  exact h1

theorem cartierPullback_add (D E : CartierDivisor X) :
    cartierPullback ρ (D + E) = cartierPullback ρ D + cartierPullback ρ E := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt (ρ t)
  refine ⟨Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (f * g), ?_, ?_⟩
  · exact cartierPullback_isLocalEquationAt ρ (D + E) t (hf.mul hg)
  · rw [map_mul]
    exact (cartierPullback_isLocalEquationAt ρ D t hf).mul
      (cartierPullback_isLocalEquationAt ρ E t hg)

theorem cartierPullback_principal (f : X.functionFieldˣ) :
    cartierPullback ρ (principalCartierDivisor X f) =
      principalCartierDivisor T (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f) := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  exact ⟨_, cartierPullback_isLocalEquationAt ρ _ t
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor (ρ t) f),
    CartierDivisor.isLocalEquationAt_principalCartierDivisor t _⟩

theorem cartierPullback_zero : cartierPullback ρ (0 : CartierDivisor X) = 0 := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  refine ⟨1, ?_, CartierDivisor.isLocalEquationAt_zero t⟩
  have h := cartierPullback_isLocalEquationAt ρ (0 : CartierDivisor X) t
    (CartierDivisor.isLocalEquationAt_zero (ρ t))
  rwa [map_one] at h

end Pullback

end MixedFujita

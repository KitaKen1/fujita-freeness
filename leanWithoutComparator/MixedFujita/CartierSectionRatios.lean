/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionNonvanishingOpen
public import MixedFujita.CartierOpenCoefficient
public import MixedFujita.PointClosureHyperplaneEquivalence

/-!
Ratios of actual sections of a Cartier divisor as regular functions (steps 1 and 4). Let t be a
nonzero global section of a Cartier divisor D on an integral scheme, with rational function τ, and
U_t the open where t generates. The inverse τ⁻¹ is a local equation of D at every point of U_t,
hence an equation of D on U_t. For another section t' the ratio τ'/τ is therefore the regular
function on U_t given by the coefficient of t' for this equation; its germs are the local
coefficients, it does not vanish exactly on U_t ∩ U_t', the ratio of t with itself is 1, and the
ratios satisfy the cocycle identity (τ_q/τ_j) = (τ_i/τ_j)(τ_q/τ_i) on U_i ∩ U_j. These are the
affine coordinates of the map to projective space defined by a family of sections; no
trivialization of the sheaf of D as a module is chosen.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- A common local equation at every point of an open subset is an equation on it. -/
theorem rationalUnitClass_eq_restrict_of_forall_isLocalEquationAt (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (g : X.functionFieldˣ)
    (h : ∀ x ∈ U, D.IsLocalEquationAt x g) :
    rationalUnitClass X U (Additive.ofMul g) = D |_ U := by
  have key : ∀ x : U, ∃ (W : X.Opens) (hWU : W ≤ U), (x : X) ∈ W ∧
      TopCat.Presheaf.restrictOpen (rationalUnitClass X U (Additive.ofMul g)) W hWU =
        TopCat.Presheaf.restrictOpen (D |_ U) W hWU := by
    intro x
    obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp (h x x.2)
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty (V ⊓ U : X.Opens) := ⟨⟨x, hxV, x.2⟩⟩
    refine ⟨V ⊓ U, inf_le_right, ⟨hxV, x.2⟩, ?_⟩
    rw [rationalUnitClass_restrict X (inf_le_right : V ⊓ U ≤ U),
      TopCat.Presheaf.restrict_restrict inf_le_right le_top]
    exact CartierDivisor.rationalUnitClass_eq_of_le inf_le_left hV
  choose W hWU hxW hW using key
  refine (cartierDivisorSheaf X).eq_of_locally_eq' W U (fun x => homOfLE (hWU x)) ?_ _ _ hW
  intro x hx
  exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩

/-- On the open where a section generates, the inverse of its rational function is a local
equation of the divisor. -/
theorem isLocalEquationAt_inv_cartierSectionUnit (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤))
    (ht : t ≠ 0) (x : X) (hx : x ∈ cartierSectionNonvanishingOpen D t) :
    D.IsLocalEquationAt x (cartierSectionUnit D t ht)⁻¹ := by
  obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen D t x).mp hx
  refine isLocalEquationAt_stalkUnit_mul hf hu.unit⁻¹ ?_
  have him := cartierLocalCoefficient_image D x f hf t
  have hτ : (cartierSectionUnit D t ht : X.functionField) ≠ 0 := Units.ne_zero _
  rw [map_units_inv, IsUnit.unit_spec, him, Units.val_inv_eq_inv_val, cartierSectionUnit_val]
  have hf0 : (f : X.functionField) ≠ 0 := Units.ne_zero f
  have hτ0 : cartierSectionRational D t ≠ 0 := by rwa [cartierSectionUnit_val] at hτ
  field_simp

/-- The inverse of the rational function of a section is an equation of the divisor on the open
where the section generates. -/
theorem rationalUnitClass_inv_cartierSectionUnit (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤))
    (ht : t ≠ 0) :
    haveI := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
    rationalUnitClass X (cartierSectionNonvanishingOpen D t)
        (Additive.ofMul (cartierSectionUnit D t ht)⁻¹) =
      D |_ cartierSectionNonvanishingOpen D t :=
  haveI := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
  rationalUnitClass_eq_restrict_of_forall_isLocalEquationAt D _ _
    (isLocalEquationAt_inv_cartierSectionUnit D t ht)

/-- The ratio t'/t of two actual sections, as a regular function on the open where t
generates. -/
noncomputable def cartierSectionRatio (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤)) (ht : t ≠ 0)
    (t' : Γ(D.sheaf, ⊤)) : Γ(X, cartierSectionNonvanishingOpen D t) :=
  haveI := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
  cartierOpenCoefficient D (cartierSectionNonvanishingOpen D t) (cartierSectionUnit D t ht)⁻¹
    (rationalUnitClass_inv_cartierSectionUnit D t ht) (cartierSectionNonvanishingOpen D t) le_rfl
    (D.sheaf.presheaf.map (homOfLE le_top : cartierSectionNonvanishingOpen D t ⟶ ⊤).op t')

/-- The rational function of the ratio t'/t is τ'/τ. -/
theorem cartierSectionRatio_germToFunctionField (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤))
    (ht : t ≠ 0) (t' : Γ(D.sheaf, ⊤)) :
    haveI := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
    X.germToFunctionField (cartierSectionNonvanishingOpen D t) (cartierSectionRatio D t ht t') =
      (cartierSectionRational D t)⁻¹ * cartierSectionRational D t' := by
  have := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
  unfold cartierSectionRatio
  rw [cartierOpenCoefficient_image, Units.val_inv_eq_inv_val, cartierSectionUnit_val,
    cartierSectionRational_apply D t']
  congr 1
  have h := ConcreteCategory.congr_hom (D.sheafι.mapPresheaf.naturality
    (homOfLE le_top : cartierSectionNonvanishingOpen D t ⟶ ⊤).op) t'
  change Scheme.Modules.Hom.app D.sheafι (cartierSectionNonvanishingOpen D t)
    (D.sheaf.presheaf.map (homOfLE le_top : cartierSectionNonvanishingOpen D t ⟶ ⊤).op t') =
      (rationalFunctions X).presheaf.map
        (homOfLE le_top : cartierSectionNonvanishingOpen D t ⟶ ⊤).op
        (Scheme.Modules.Hom.app D.sheafι ⊤ t') at h
  rw [h, rationalFunctionsEquiv_map]

/-- The germ of the ratio t'/t at a point where t generates is the local coefficient of t' for
the local equation τ⁻¹. -/
theorem cartierSectionRatio_germ (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤)) (ht : t ≠ 0)
    (t' : Γ(D.sheaf, ⊤)) (x : X) (hx : x ∈ cartierSectionNonvanishingOpen D t) :
    X.presheaf.germ (cartierSectionNonvanishingOpen D t) x hx (cartierSectionRatio D t ht t') =
      cartierLocalCoefficient D x (cartierSectionUnit D t ht)⁻¹
        (isLocalEquationAt_inv_cartierSectionUnit D t ht x hx) t' := by
  have := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
  exact cartierOpenCoefficient_germ_global D _ _ (rationalUnitClass_inv_cartierSectionUnit D t ht)
    x hx t'

/-- The ratio t'/t does not vanish exactly where both t and t' generate. -/
theorem basicOpen_cartierSectionRatio (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤)) (ht : t ≠ 0)
    (t' : Γ(D.sheaf, ⊤)) :
    X.basicOpen (cartierSectionRatio D t ht t') =
      cartierSectionNonvanishingOpen D t ⊓ cartierSectionNonvanishingOpen D t' := by
  ext x
  constructor
  · intro hx
    have hxU := X.basicOpen_le _ hx
    refine ⟨hxU, ?_⟩
    have hu := (X.mem_basicOpen _ x hxU).mp hx
    rw [cartierSectionRatio_germ D t ht t' x hxU] at hu
    exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D t' x _ _).mpr hu
  · rintro ⟨hxU, hxU'⟩
    apply (X.mem_basicOpen _ x hxU).mpr
    rw [cartierSectionRatio_germ D t ht t' x hxU]
    exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D t' x _ _).mp hxU'

/-- The ratio of a section with itself is 1. -/
theorem cartierSectionRatio_self (D : CartierDivisor X) (t : Γ(D.sheaf, ⊤)) (ht : t ≠ 0) :
    cartierSectionRatio D t ht t = 1 := by
  have := (cartierSectionNonvanishingOpen_nonempty_iff D t).mpr ht
  apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D t)
  rw [cartierSectionRatio_germToFunctionField, map_one]
  exact inv_mul_cancel₀ (fun h => ht (cartierSectionRational_injective D (h.trans (map_zero _).symm)))

/-- The cocycle identity for ratios on the intersection of two generating opens:
t_q/t_j = (t_i/t_j) (t_q/t_i). -/
theorem cartierSectionRatio_cocycle (D : CartierDivisor X) (ti tj tq : Γ(D.sheaf, ⊤))
    (hi : ti ≠ 0) (hj : tj ≠ 0) :
    X.presheaf.map (homOfLE (inf_le_right :
        cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
          cartierSectionNonvanishingOpen D tj)).op (cartierSectionRatio D tj hj tq) =
      X.presheaf.map (homOfLE (inf_le_right :
        cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
          cartierSectionNonvanishingOpen D tj)).op (cartierSectionRatio D tj hj ti) *
      X.presheaf.map (homOfLE (inf_le_left :
        cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
          cartierSectionNonvanishingOpen D ti)).op (cartierSectionRatio D ti hi tq) := by
  have := (cartierSectionNonvanishingOpen_nonempty_iff D ti).mpr hi
  have := (cartierSectionNonvanishingOpen_nonempty_iff D tj).mpr hj
  have := integral_opens_inter_nonempty X (cartierSectionNonvanishingOpen D ti)
    (cartierSectionNonvanishingOpen D tj)
  have h1 := germToFunctionField_restrict X (inf_le_right :
    cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
      cartierSectionNonvanishingOpen D tj) (cartierSectionRatio D tj hj tq)
  have h2 := germToFunctionField_restrict X (inf_le_right :
    cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
      cartierSectionNonvanishingOpen D tj) (cartierSectionRatio D tj hj ti)
  have h3 := germToFunctionField_restrict X (inf_le_left :
    cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj ≤
      cartierSectionNonvanishingOpen D ti) (cartierSectionRatio D ti hi tq)
  have e1 := cartierSectionRatio_germToFunctionField D tj hj tq
  have e2 := cartierSectionRatio_germToFunctionField D tj hj ti
  have e3 := cartierSectionRatio_germToFunctionField D ti hi tq
  have hτi : cartierSectionRational D ti ≠ 0 := fun h =>
    hi (cartierSectionRational_injective D (h.trans (map_zero _).symm))
  have hτj : cartierSectionRational D tj ≠ 0 := fun h =>
    hj (cartierSectionRational_injective D (h.trans (map_zero _).symm))
  apply X.germToFunctionField_injective
    (cartierSectionNonvanishingOpen D ti ⊓ cartierSectionNonvanishingOpen D tj)
  refine (h1.trans e1).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  refine Eq.trans ?_ (congrArg₂ (fun a b => a * b) (h2.trans e2).symm (h3.trans e3).symm)
  field_simp

end MixedFujita

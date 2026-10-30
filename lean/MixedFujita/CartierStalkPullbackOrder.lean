/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalAdicRestriction
public import MixedFujita.CartierVanishingOrder

/-!
Send the actual local coefficient of a Cartier section through an actual
scheme stalk map. Changing its local equation multiplies the image by a
local unit, so the image order is independent of the frame. The original
intrinsic order is bounded by this actual restricted local order.
This constructs local coefficient restriction, not a global Cartier
divisor pullback or a global section on a chosen curve. In particular,
nonzero source sections can restrict to zero; that requirement is not
silently omitted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {Y X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierStalkPullbackCoefficient (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f) :
    Γ(D.sheaf, ⊤) →+ Y.presheaf.stalk y :=
  (φ.stalkMap y).hom.toAddMonoidHom.comp (cartierLocalCoefficient D (φ y) f hf).toAddMonoidHom

theorem cartierStalkPullbackCoefficient_apply (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f)
    (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackCoefficient D φ y f hf s =
      φ.stalkMap y (cartierLocalCoefficient D (φ y) f hf s) := rfl

theorem cartierStalkPullbackCoefficient_change_frame (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (φ y) f) (hg : D.IsLocalEquationAt (φ y) g) :
    ∃ v : (Y.presheaf.stalk y)ˣ, ∀ s : Γ(D.sheaf, ⊤),
      cartierStalkPullbackCoefficient D φ y f hf s =
        (v : Y.presheaf.stalk y) * cartierStalkPullbackCoefficient D φ y g hg s := by
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D (φ y) f g hf hg
  refine ⟨Units.map (φ.stalkMap y).hom.toMonoidHom v, fun s => ?_⟩
  simp only [cartierStalkPullbackCoefficient_apply, Units.coe_map]
  rw [hv s, map_mul]
  rfl

noncomputable def cartierStalkPullbackOrder (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (s : Γ(D.sheaf, ⊤)) : ℕ∞ :=
  localAdicOrder (Y.presheaf.stalk y) (cartierStalkPullbackCoefficient D φ y
    (Classical.choose (D.exists_isLocalEquationAt (φ y)))
    (Classical.choose_spec (D.exists_isLocalEquationAt (φ y))) s)

theorem cartierStalkPullbackOrder_eq_localCoefficient (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f)
    (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackOrder D φ y s =
      localAdicOrder (Y.presheaf.stalk y) (cartierStalkPullbackCoefficient D φ y f hf s) := by
  obtain ⟨v, hv⟩ := cartierStalkPullbackCoefficient_change_frame D φ y
    (Classical.choose (D.exists_isLocalEquationAt (φ y))) f
    (Classical.choose_spec (D.exists_isLocalEquationAt (φ y))) hf
  change localAdicOrder _ _ = _
  rw [hv s, localAdicOrder_unit_mul]

theorem cartierStalkPullbackOrder_nat_le_iff (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f)
    (s : Γ(D.sheaf, ⊤)) (d : ℕ) :
    (d : ℕ∞) ≤ cartierStalkPullbackOrder D φ y s ↔
      cartierStalkPullbackCoefficient D φ y f hf s ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ d := by
  rw [cartierStalkPullbackOrder_eq_localCoefficient D φ y f hf, localAdicOrder_nat_le_iff]

theorem cartierSectionVanishingOrder_le_stalkPullbackOrder (D : CartierDivisor X)
    (φ : Y ⟶ X) (y : Y) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D (φ y) s ≤ cartierStalkPullbackOrder D φ y s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  rw [cartierSectionVanishingOrder_eq_localCoefficient D (φ y) f hf,
    cartierStalkPullbackOrder_eq_localCoefficient D φ y f hf,
    cartierStalkPullbackCoefficient_apply]
  exact scheme_stalkMap_localAdicOrder_le φ y _

theorem cartierStalkPullbackOrder_eq_top_iff (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackOrder D φ y s = ⊤ ↔ cartierStalkPullbackCoefficient D φ y f hf s = 0 := by
  rw [cartierStalkPullbackOrder_eq_localCoefficient D φ y f hf, localAdicOrder_eq_top_iff]

theorem cartierStalkPullbackOrder_lt_top_iff (D : CartierDivisor X) (φ : Y ⟶ X)
    (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ y) f) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackOrder D φ y s < ⊤ ↔ cartierStalkPullbackCoefficient D φ y f hf s ≠ 0 := by
  rw [lt_top_iff_ne_top, ne_eq, cartierStalkPullbackOrder_eq_top_iff D φ y f hf]

theorem cartierStalkPullbackCoefficient_comp {Z : Scheme.{u}}
    (D : CartierDivisor X) (φ : Y ⟶ X) (ψ : Z ⟶ Y) (z : Z)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt (φ (ψ z)) f) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackCoefficient D (ψ ≫ φ) z f hf s =
      ψ.stalkMap z (cartierStalkPullbackCoefficient D φ (ψ z) f hf s) := by
  change (ψ ≫ φ).stalkMap z (cartierLocalCoefficient D (φ (ψ z)) f hf s) =
    ψ.stalkMap z (φ.stalkMap (ψ z) (cartierLocalCoefficient D (φ (ψ z)) f hf s))
  rw [Scheme.Hom.stalkMap_comp]
  rfl

end MixedFujita

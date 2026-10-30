/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DVRVanishingOrder
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Cartier.Inverse

/-!
Compare the intrinsic maximal-ideal vanishing order of an actual Cartier
section with the coefficient of its actual effective zero divisor as a Weil
divisor. The comparison uses the nonzero actual regular local coefficient
and Mathlib's fraction-field order. It does not assume a coefficient/order
identification. Global curve degree and uniform linear bounds are separate.
-/

@[expose] public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

section LocallyNoetherian

variable [IsLocallyNoetherian X]

theorem scheme_ord_regular_eq_localAdicOrder_nat (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (r : X.presheaf.stalk (x : X)) (hr : r ≠ 0) (d : ℕ)
    (hd : localAdicOrder (X.presheaf.stalk (x : X)) r = d) :
    X.ord (algebraMap (X.presheaf.stalk (x : X)) X.functionField r) (x : X) = (d : ℤ) := by
  have hne : algebraMap (X.presheaf.stalk (x : X)) X.functionField r ≠ 0 :=
    fun h => hr (IsFractionRing.injective (X.presheaf.stalk (x : X)) X.functionField
      (h.trans (map_zero _).symm))
  have hord : Ring.ord (X.presheaf.stalk (x : X)) r = d :=
    (dvr_localAdicOrder_eq_ringOrd r).symm.trans hd
  rw [X.ord_eq_iff x.property hne]
  simp only [AlgebraicGeometry.Scheme.ordHom]
  rw [Ring.ordFrac_eq_ord _ hr,
    Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_iff_ne_zero.mpr hr) hord]

end LocallyNoetherian

variable [IsNoetherian X]

theorem cartier_orderAt_eq_scheme_ord_of_localEquation (D : CartierDivisor X)
    (x : CodimensionOnePoint X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (x : X) f) :
    D.orderAt x = X.ord (f : X.functionField) (x : X) := by
  obtain ⟨U, hx, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  let : Nonempty U := ⟨⟨(x : X), hx⟩⟩
  rw [D.orderAt_eq_of_restrict_eq_rationalUnitClass x U hx (Additive.ofMul f) hU.symm,
    SchemeWeilDivisor.orderAt_apply]
  rfl

theorem cartierSectionZeroDivisor_coeff_eq_vanishingOrder_nat (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] (d : ℕ)
    (hd : cartierSectionVanishingOrder D (x : X) s = d) :
    WeilDivisor.coeff (cartierSectionZeroDivisor D s hs).toWeilDivisor x = (d : ℤ) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (x : X)
  obtain ⟨r, hr, hrimage, heq, hrorder⟩ :=
    cartierSectionZeroDivisor_regular_localEquation D (x : X) f hf s hs
  rw [CartierDivisor.coeff_toWeilDivisor,
    cartier_orderAt_eq_scheme_ord_of_localEquation _ x _ heq, ← hrimage]
  exact scheme_ord_regular_eq_localAdicOrder_nat x r hr d (hrorder.trans hd)

theorem cartierSectionZeroDivisor_exists_coeff_order_nat (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    ∃ d : ℕ, cartierSectionVanishingOrder D (x : X) s = d ∧
      WeilDivisor.coeff (cartierSectionZeroDivisor D s hs).toWeilDivisor x = (d : ℤ) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    ((cartierSectionVanishingOrder_lt_top_iff D (x : X) s).mpr hs).ne
  exact ⟨d, hd.symm,
    cartierSectionZeroDivisor_coeff_eq_vanishingOrder_nat D s hs x d hd.symm⟩

theorem cartierSectionZeroDivisor_vanishingOrder_eq_coeff_toNat (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    cartierSectionVanishingOrder D (x : X) s =
      (WeilDivisor.coeff (cartierSectionZeroDivisor D s hs).toWeilDivisor x).toNat := by
  obtain ⟨d, hd, hc⟩ := cartierSectionZeroDivisor_exists_coeff_order_nat D s hs x
  simpa only [hc, Int.toNat_natCast] using hd

theorem cartierSectionZeroDivisor_toWeilDivisor_isEffective
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    WeilDivisor.IsEffective (cartierSectionZeroDivisor D s hs).toWeilDivisor := by
  apply (WeilDivisor.isEffective_iff _).mpr
  intro x
  obtain ⟨d, _, hc⟩ := cartierSectionZeroDivisor_exists_coeff_order_nat D s hs x
  rw [hc]
  exact Int.natCast_nonneg d

end MixedFujita

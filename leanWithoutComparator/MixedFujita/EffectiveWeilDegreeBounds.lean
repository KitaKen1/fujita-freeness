/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Degree.Order
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
An effective Weil divisor contains the single spike at each point with its
own coefficient. Monotonicity of weighted degree bounds that coefficient
times the point weight by total degree. A positive integer weight also
bounds the coefficient itself. Apply this to actual residue-degree weights.
-/

@[expose] public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace MixedFujita

theorem effectiveWeil_single_coeff_le {S : Type*} (D : WeilDivisor S)
    (hD : WeilDivisor.IsEffective D) (x : S) :
    WeilDivisor.coeff D x • WeilDivisor.ofPoint x ≤ D := by
  change ∀ y, WeilDivisor.coeff (WeilDivisor.coeff D x • WeilDivisor.ofPoint x) y ≤
    WeilDivisor.coeff D y
  intro y
  by_cases h : y = x
  · subst y
    simp
  · simp only [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne h,
      mul_zero]
    exact (WeilDivisor.isEffective_iff D).mp hD y

theorem effectiveWeil_weightedCoeff_le_degree {S : Type*} (D : WeilDivisor S)
    (hD : WeilDivisor.IsEffective D) (w : S → ℤ) (hw : ∀ y, 0 ≤ w y) (x : S) :
    WeilDivisor.coeff D x * w x ≤ WeilDivisor.weightedDegree w D := by
  have h := WeilDivisor.weightedDegree_le_of_le hw (effectiveWeil_single_coeff_le D hD x)
  simpa only [map_zsmul, WeilDivisor.weightedDegree_ofPoint, smul_eq_mul] using h

theorem effectiveWeil_coeff_le_weightedDegree {S : Type*} (D : WeilDivisor S)
    (hD : WeilDivisor.IsEffective D) (w : S → ℤ) (hw : ∀ y, 0 ≤ w y)
    (x : S) (hx : 0 < w x) :
    WeilDivisor.coeff D x ≤ WeilDivisor.weightedDegree w D := by
  have hc := (WeilDivisor.isEffective_iff D).mp hD x
  calc
    WeilDivisor.coeff D x = WeilDivisor.coeff D x * 1 := (mul_one _).symm
    _ ≤ WeilDivisor.coeff D x * w x := mul_le_mul_of_nonneg_left (by omega) hc
    _ ≤ WeilDivisor.weightedDegree w D := effectiveWeil_weightedCoeff_le_degree D hD w hw x

theorem effectiveSchemeWeil_coeff_le_relativeDegree {X Y : Scheme}
    (f : X ⟶ Y) (D : SchemeWeilDivisor X) (hD : WeilDivisor.IsEffective D)
    (x : CodimensionOnePoint X) (hx : 0 < f.residueDegree (x : X)) :
    WeilDivisor.coeff D x ≤ SchemeWeilDivisor.relativeDegree f D := by
  rw [SchemeWeilDivisor.relativeDegree_apply, ← WeilDivisor.weightedDegree_apply]
  apply effectiveWeil_coeff_le_weightedDegree D hD
    (fun y : CodimensionOnePoint X => (f.residueDegree (y : X) : ℤ))
    (fun y => Int.natCast_nonneg _) x
  exact_mod_cast hx

end MixedFujita

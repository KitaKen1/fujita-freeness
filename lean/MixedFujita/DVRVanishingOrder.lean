/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierVanishingOrder
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
The intrinsic maximal-ideal adic order in an actual DVR equals Mathlib's
additive valuation. Apply this to the actual local coefficient of a Cartier
section. This prepares comparison with curve divisor coefficients; the
global divisor degree and the intersection bound are not asserted here.
-/

@[expose] public section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

theorem dvr_localAdicOrder_eq_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (r : R) :
    localAdicOrder R r = IsDiscreteValuationRing.addVal R r := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_prime R
  apply ENat.eq_of_forall_natCast_le_iff
  intro d
  rw [localAdicOrder_nat_le_iff, hp.irreducible.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hp.irreducible.addVal_pow]

theorem dvr_localAdicOrder_eq_ringOrd {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (r : R) : localAdicOrder R r = Ring.ord R r := by
  rw [dvr_localAdicOrder_eq_addVal, Ring.ord_eq_addVal]

universe u
variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierSectionVanishingOrder_eq_DVR_addVal (D : CartierDivisor X)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk x) (cartierLocalCoefficient D x f hf s) := by
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    dvr_localAdicOrder_eq_addVal]

theorem cartierSectionVanishingOrder_eq_DVR_ringOrd (D : CartierDivisor X)
    (x : X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionVanishingOrder D x s =
      Ring.ord (X.presheaf.stalk x) (cartierLocalCoefficient D x f hf s) := by
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    dvr_localAdicOrder_eq_ringOrd]

end MixedFujita

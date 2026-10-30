/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalAdicOrder
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
Restriction cannot lower intrinsic maximal-ideal vanishing order: a local
homomorphism sends each maximal-ideal power into the corresponding power.
Apply this to actual scheme stalk maps and to actual pullbacks of regular
functions on opens. No order inequality is supplied as an input.
The restricted element may be zero, with infinite order. This does not
construct a curve avoiding a zero divisor or prove a Bertini theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MixedFujita

theorem idealAdicOrder_le_of_map_le {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (hIJ : I.map f ≤ J) (r : R) :
    idealAdicOrder I r ≤ idealAdicOrder J (f r) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  apply (idealAdicOrder_nat_le_iff J (f r) d).mpr
  have hp : (I ^ d).map f ≤ J ^ d := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hIJ d
  exact hp (Ideal.mem_map_of_mem f hd)

theorem localAdicOrder_le_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (r : R) :
    localAdicOrder R r ≤ localAdicOrder S (f r) :=
  idealAdicOrder_le_of_map_le f _ _ (IsLocalRing.map_maximalIdeal_le f) r

theorem localAdicOrder_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (r : R) :
    localAdicOrder S (e r) = localAdicOrder R r := by
  let : IsLocalHom e.toRingHom := ⟨fun a ha => by
    simpa using ha.map e.symm.toRingHom⟩
  let : IsLocalHom e.symm.toRingHom := ⟨fun a ha => by
    simpa using ha.map e.toRingHom⟩
  apply le_antisymm
  · simpa using
      localAdicOrder_le_of_isLocalHom e.symm.toRingHom (e r)
  · exact localAdicOrder_le_of_isLocalHom e.toRingHom r

theorem scheme_stalkMap_maximalIdeal_pow_mem {Y X : Scheme} (φ : Y ⟶ X)
    (y : Y) (r : X.presheaf.stalk (φ y)) (d : ℕ)
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (φ y)) ^ d) :
    φ.stalkMap y r ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ d := by
  apply (localAdicOrder_nat_le_iff _ d).mp
  exact ((localAdicOrder_nat_le_iff r d).mpr hr).trans
    (localAdicOrder_le_of_isLocalHom (φ.stalkMap y).hom r)

theorem scheme_stalkMap_localAdicOrder_le {Y X : Scheme} (φ : Y ⟶ X)
    (y : Y) (r : X.presheaf.stalk (φ y)) :
    localAdicOrder (X.presheaf.stalk (φ y)) r ≤
      localAdicOrder (Y.presheaf.stalk y) (φ.stalkMap y r) :=
  localAdicOrder_le_of_isLocalHom (φ.stalkMap y).hom r

theorem scheme_pullback_regularFunction_localAdicOrder_le {Y X : Scheme} (φ : Y ⟶ X)
    (U : X.Opens) (y : Y) (hy : φ y ∈ U) (r : Γ(X, U)) :
    localAdicOrder (X.presheaf.stalk (φ y)) (X.presheaf.germ U (φ y) hy r) ≤
      localAdicOrder (Y.presheaf.stalk y)
        (Y.presheaf.germ (φ ⁻¹ᵁ U) y hy (φ.app U r)) := by
  simpa only [Scheme.Hom.germ_stalkMap_apply] using
    scheme_stalkMap_localAdicOrder_le φ y (X.presheaf.germ U (φ y) hy r)

end MixedFujita

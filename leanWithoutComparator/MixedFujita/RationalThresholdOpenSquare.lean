/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltOpenImmersionLocalDescent
public import MixedFujita.BasePrimeThresholdInvariance
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
Rational klt pullback tests commute with an actual open square covering the
base-open inverse image. On a normal prime of the smaller base, the pulled
base divisor can be replaced by any divisor with the same coefficient. This
compares independently chosen local Cartier equations on a common refinement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

variable {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z]
  [Z.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

variable {Y' : Scheme.{u}} [IsIntegral Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
  (k : Y' ⟶ Y) [IsOpenImmersion k] [IsDominant k]
  (g : X ⟶ Y) [IsDominant g] (g' : Z ⟶ Y') [IsDominant g']
  (hcomm : j ≫ g = g' ≫ k)
  (hcover : g ⁻¹ᵁ k.opensRange ≤ j.opensRange)

include hcomm hcover

/-- The actual open-square comparison identifies every rational klt test. -/
theorem logPairIsKltOverBasePoint_rational_pullback_iff_open_square
    (η : Y') (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (H : CartierDivisor Y)
    (cZ : EtaleChart K Z n) (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsKltOverBasePoint g (k η) c f (q * d)
      (q • D + (d * p) • cartierPullback g H) ↔
    LogPairIsKltOverBasePoint g' η cZ (crepantPullbackFormUnit j hj c f cZ) (q * d)
      (q • cartierPullback j D + (d * p) • cartierPullback g' (cartierPullback k H)) := by
  have h := logPairIsKltOverBasePoint_iff_open_crepant_pullback j hj g (k η)
    k.opensRange ⟨η, rfl⟩ hcover c f (q * d) (Nat.mul_pos (by omega) (by omega))
    (q • D + (d * p) • cartierPullback g H) cZ
  have hbase : cartierPullback j (cartierPullback g H) =
      cartierPullback g' (cartierPullback k H) := by
    rw [← cartierPullback_comp, ← cartierPullback_comp]
    simpa only [hcomm]
  rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul, hbase] at h
  refine h.trans ?_
  simpa only [← hcomm] using
    logPairIsKltOverBasePoint_comp_open_immersion_iff g' k η cZ
      (crepantPullbackFormUnit j hj c f cZ) (q * d)
      (q • cartierPullback j D + (d * p) • cartierPullback g' (cartierPullback k H))

/-- At a normal base prime, only the common-refinement coefficient of the local equation matters. -/
theorem logPairIsKltOverBasePoint_rational_pullback_iff_open_square_coefficient
    (η : CodimensionOnePoint Y') [IsIntegrallyClosed (Y'.presheaf.stalk (η : Y'))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (H' : CartierDivisor Y')
    (hH : cartierCoefficient (cartierPullback k H) (η : Y') = cartierCoefficient H' (η : Y'))
    (cZ : EtaleChart K Z n) (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsKltOverBasePoint g (k (η : Y')) c f (q * d)
      (q • D + (d * p) • cartierPullback g H) ↔
    LogPairIsKltOverBasePoint g' (η : Y') cZ (crepantPullbackFormUnit j hj c f cZ) (q * d)
      (q • cartierPullback j D + (d * p) • cartierPullback g' H') := by
  exact (logPairIsKltOverBasePoint_rational_pullback_iff_open_square j hj k g g' hcomm hcover
    (η : Y') c f d hd D H cZ p q hq).trans
    (logPairIsKltOverBasePoint_rational_pullback_iff_of_base_prime_coefficient_eq
      g' η (cartierPullback k H) H' hH cZ (crepantPullbackFormUnit j hj c f cZ) d
      (cartierPullback j D) p q)

/-- The exact finite endpoint is preserved by the same open-square coefficient comparison. -/
theorem rational_klt_threshold_eq_on_open_square_coefficient
    (η : CodimensionOnePoint Y') [IsIntegrallyClosed (Y'.presheaf.stalk (η : Y'))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (H' : CartierDivisor Y')
    (hH : cartierCoefficient (cartierPullback k H) (η : Y') = cartierCoefficient H' (η : Y'))
    (cZ : EtaleChart K Z n) (a b q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (ha : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g (k (η : Y')) c f (r * d)
        (r • D + (d * p) • cartierPullback g H) ↔ (p : ℚ) / r < (a : ℚ) / q))
    (hb : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g' (η : Y') cZ (crepantPullbackFormUnit j hj c f cZ) (r * d)
        (r • cartierPullback j D + (d * p) • cartierPullback g' H') ↔
          (p : ℚ) / r < (b : ℚ) / s)) :
    (a : ℚ) / q = (b : ℚ) / s := by
  apply rational_threshold_eq_of_natural_tests a b q s hq hs
  intro p r hr
  exact (ha p r hr).symm.trans
    ((logPairIsKltOverBasePoint_rational_pullback_iff_open_square_coefficient
      j hj k g g' hcomm hcover η c f d hd D H H' hH cZ p r hr).trans (hb p r hr))

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothProperCurveSections
public import TauCeti.AlgebraicGeometry.CartierDivisor.Degree
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness

/-!
Actual proper curves have Noetherian underlying schemes. On smooth integral
curves, smoothness supplies codimension-one DVRs and the proper curve theorem
supplies finite-dimensional H1(O). With that derived input, the degree of an
actual principal Cartier divisor is zero. Hence the actual zero divisor of
a nonzero section of O(D) has degree D. No H1 finiteness is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

include K in
theorem properOverField_scheme_isNoetherian : IsNoetherian X := by
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  let : CompactSpace X :=
    (quasiCompact_iff_compactSpace (X ↘ Spec (CommRingCat.of K))).mp inferInstance
  exact {}

variable [IsIntegral X]

noncomputable def properCurveCartierDegree (_hX : topologicalKrullDim X = 1)
    (D : CartierDivisor X) : ℤ :=
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) D

theorem properCurveCartierDegree_add (hX : topologicalKrullDim X = 1)
    (D E : CartierDivisor X) :
    properCurveCartierDegree (K := K) hX (D + E) =
      properCurveCartierDegree (K := K) hX D + properCurveCartierDegree (K := K) hX E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) (D + E) =
    CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) D +
      CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) E
  exact map_add _ D E

theorem properCurveCartierDegree_nsmul (hX : topologicalKrullDim X = 1)
    (j : ℕ) (D : CartierDivisor X) :
    properCurveCartierDegree (K := K) hX (j • D) =
      (j : ℤ) * properCurveCartierDegree (K := K) hX D := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) (j • D) =
    (j : ℤ) * CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) D
  simpa only [nsmul_eq_mul] using
    map_nsmul (CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))) j D

variable [Smooth (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_finiteDimensional_cohomologyOne
    (hX : topologicalKrullDim X = 1) :
    FiniteDimensional K (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (TauCeti.AlgebraicGeometry.InvertibleSheaf.trivial X).obj 1) := by
  let : ∀ x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := fun x =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  exact TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_one_trivial_of_isProper K hX

theorem properSmoothCurve_principalCartierDegree_zero
    (hX : topologicalKrullDim X = 1) (g : X.functionFieldˣ) :
    properCurveCartierDegree (K := K) hX (principalCartierDivisor X g) = 0 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : ∀ x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := fun x =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  let := properSmoothCurve_finiteDimensional_cohomologyOne (K := K) hX
  have hdim (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX.le
  change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
    (principalCartierDivisor X g) = 0
  simpa only [principalCartierDivisorAddHom_apply,
    show Additive.toMul (Additive.ofMul g) = g from rfl] using
    CartierDivisor.relativeDegree_principalCartierDivisor (k := K) hdim (Additive.ofMul g)

theorem properSmoothCurve_sectionZeroDivisor_degree
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    properCurveCartierDegree (K := K) hX (cartierSectionZeroDivisor D s hs) =
      properCurveCartierDegree (K := K) hX D := by
  rw [cartierSectionZeroDivisor, properCurveCartierDegree_add,
    properSmoothCurve_principalCartierDegree_zero, add_zero]

end MixedFujita

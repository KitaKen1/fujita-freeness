/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperCurveDegree
public import MixedFujita.CartierWeilVanishingOrder
public import MixedFujita.EffectiveWeilDegreeBounds
public import MixedFujita.CartierFiniteJets

/-!
On an actual proper smooth integral curve, a nonzero section of O(jA) has
vanishing order at every closed point bounded by j * max(deg A, 0). The
constant depends only on A and the curve, not on the point or degree j.
The proof compares actual zero-divisor coefficients with its total degree,
using derived H1(O) finiteness to obtain principal degree zero. No order
bound or finite-dimensionality is an input. Over an algebraically closed
field, connect this geometric bound to all graded Taylor maps and finite
jets in one coordinate choice, and to a linear section-dimension bound.
This is the curve bound, not the arbitrary-dimensional intersection bound,
the full valuation/discrepancy estimate, or F1/F2.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower

noncomputable def properCurveOrderBound (hX : topologicalKrullDim X = 1)
    (A : CartierDivisor X) : ℕ :=
  (properCurveCartierDegree (K := K) hX A).toNat

theorem properSmoothCurve_vanishingOrder_le_degree
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X) (x : CodimensionOnePoint X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionVanishingOrder D (x : X) s ≤
      (properCurveCartierDegree (K := K) hX D).toNat := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : ∀ y : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := fun y =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) y
  have hdim (y : X) : coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hX.le
  have hclosed : IsClosed ({(x : X)} : Set X) :=
    TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.property
  have hres : 0 < (X ↘ Spec (CommRingCat.of K)).residueDegree (x : X) :=
    Nat.pos_of_ne_zero (Scheme.Hom.residueDegree_ne_zero_of_isClosed _ hclosed)
  let Z := cartierSectionZeroDivisor D s hs
  have heff := cartierSectionZeroDivisor_toWeilDivisor_isEffective D s hs
  have hcoef := effectiveSchemeWeil_coeff_le_relativeDegree
    (X ↘ Spec (CommRingCat.of K)) Z.toWeilDivisor heff x hres
  have hdegree : SchemeWeilDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
      Z.toWeilDivisor = properCurveCartierDegree (K := K) hX D := by
    calc
      _ = properCurveCartierDegree (K := K) hX Z := by
        change SchemeWeilDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
          Z.toWeilDivisor = CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) Z
        exact (CartierDivisor.relativeDegree_apply _ Z).symm
      _ = properCurveCartierDegree (K := K) hX D :=
        properSmoothCurve_sectionZeroDivisor_degree (K := K) hX D s hs
  rw [cartierSectionZeroDivisor_vanishingOrder_eq_coeff_toNat D s hs x]
  exact_mod_cast Int.toNat_le_toNat (hcoef.trans_eq hdegree)

theorem properSmoothCurve_gradedVanishingOrder_le_linearBound
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) (j : ℕ)
    (x : CodimensionOnePoint X) (s : Γ((j • A).sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionVanishingOrder (j • A) (x : X) s ≤
      j * properCurveOrderBound (K := K) hX A := by
  apply le_trans (properSmoothCurve_vanishingOrder_le_degree (K := K) hX (j • A) x s hs)
  change ((properCurveCartierDegree (K := K) hX (j • A)).toNat : ℕ∞) ≤
    (j * (properCurveCartierDegree (K := K) hX A).toNat : ℕ)
  rw [properCurveCartierDegree_nsmul]
  have hInt : (j : ℤ) * properCurveCartierDegree (K := K) hX A ≤
      ((j * (properCurveCartierDegree (K := K) hX A).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Int.self_le_toNat _) (Int.natCast_nonneg j)
  have hNat := Int.toNat_le_toNat hInt
  exact_mod_cast hNat

theorem properSmoothCurve_closedPoint_vanishingOrder_le_degree
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (x : X) (hClosed : IsClosed {x}) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionVanishingOrder D x s ≤ (properCurveCartierDegree (K := K) hX D).toNat := by
  have hx : coheight x = 1 := by
    have h := geometricSmoothScheme_closedPoint_stalk_dimension (K := K) 1 hX x hClosed
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  exact properSmoothCurve_vanishingOrder_le_degree (K := K) hX D ⟨x, hx⟩ s hs

theorem properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) (j : ℕ)
    (x : X) (hClosed : IsClosed {x}) (s : Γ((j • A).sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionVanishingOrder (j • A) x s ≤ j * properCurveOrderBound (K := K) hX A := by
  have hx : coheight x = 1 := by
    have h := geometricSmoothScheme_closedPoint_stalk_dimension (K := K) 1 hX x hClosed
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  exact properSmoothCurve_gradedVanishingOrder_le_linearBound (K := K) hX A j ⟨x, hx⟩ s hs

include K in
theorem properSmoothCurve_exists_positive_uniform_linearBound
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) :
    ∃ C : ℕ, 0 < C ∧ ∀ (j : ℕ) (x : X), IsClosed {x} →
      ∀ s : Γ((j • A).sheaf, ⊤), s ≠ 0 → cartierSectionVanishingOrder (j • A) x s ≤ j * C := by
  refine ⟨properCurveOrderBound (K := K) hX A + 1, Nat.succ_pos _, ?_⟩
  intro j x hc s hs
  apply le_trans
    (properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound (K := K) hX A j x hc s hs)
  exact_mod_cast Nat.mul_le_mul_left j (Nat.le_succ (properCurveOrderBound (K := K) hX A))

variable [IsAlgClosed K]

theorem properSmoothCurve_closedPoint_exists_gradedLinearTaylorBounds
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) (x : X) (hClosed : IsClosed {x}) :
    ∃ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin 1) K,
        (∀ (j : ℕ), Function.Injective (cartierGradedTaylor A x f hf e j)) ∧
        (∀ (j : ℕ) s, (cartierGradedTaylor A x f hf e j s).order =
          cartierSectionVanishingOrder (j • A) x s) ∧
        (∀ (j h : ℕ) s t,
          cartierGradedTaylor A x f hf e (j + h) (cartierGradedSectionProduct A j h s t) =
            cartierGradedTaylor A x f hf e j s * cartierGradedTaylor A x f hf e h t) ∧
        (∀ (j : ℕ) (s : Γ((j • A).sheaf, ⊤)), s ≠ 0 →
          cartierSectionVanishingOrder (j • A) x s ≤ j * properCurveOrderBound (K := K) hX A) ∧
        ∀ (j : ℕ), Function.Injective ((powerSeriesBoxJet 1 (j * properCurveOrderBound (K := K) hX A)).comp
          (cartierGradedTaylor A x f hf e j)) := by
  obtain ⟨f, hf, e, hi, ho, hm⟩ :=
    geometricSmoothCartier_closedPoint_exists_gradedTaylor (K := K) 1 hX A x hClosed
  refine ⟨f, hf, e, hi, ho, hm, ?_, ?_⟩
  · intro j s hs
    exact properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
      (K := K) hX A j x hClosed s hs
  · intro j
    apply linearTaylorBoxJet_injective 1 (j * properCurveOrderBound (K := K) hX A)
    intro s hs
    rw [ho j s]
    exact properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
      (K := K) hX A j x hClosed s hs

theorem properSmoothCurve_gradedSection_finrank_le_linearBound
    (hX : topologicalKrullDim X = 1) (A : CartierDivisor X) (j : ℕ)
    (x : X) (hClosed : IsClosed {x}) :
    Module.finrank K Γ((j • A).sheaf, ⊤) ≤ j * properCurveOrderBound (K := K) hX A + 1 := by
  simpa only [pow_one] using
    geometricSmoothCartier_closedPoint_finrank_le_of_order_bound (K := K) 1 hX (j • A) x hClosed
      (j * properCurveOrderBound (K := K) hX A)
      (properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
        (K := K) hX A j x hClosed)

end MixedFujita

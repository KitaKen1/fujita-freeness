/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGradedPullback

/-!
The degree and linear order constant on a fixed proper smooth integral curve
are intrinsic to the actual pullback line bundle. Euler characteristic identifies
the degrees of all Cartier representations. One representation is chosen only
inside the proof, so the source-order bound takes no representation as input.
The chosen curve and its image-hitting condition are still inputs. No uniform
ambient intersection formula or existence of a pointed Bertini curve is asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
  [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurveCartierDegree_eq_eulerDegree
    (hY : topologicalKrullDim Y = 1) (A : CartierDivisor Y) :
    properCurveCartierDegree (K := K) hY A = A.toInvertibleSheaf.eulerDegree K := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : ∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint Y,
      IsDiscreteValuationRing (Y.presheaf.stalk (y : Y)) := fun y ↦
    smoothOverField_codimensionOne_stalk_DVR (K := K) y
  let := properSmoothCurve_finiteDimensional_cohomologyOne (K := K) hY
  have hdim (y : Y) : coheight y ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hY.le
  change CartierDivisor.relativeDegree (Y ↘ Spec (CommRingCat.of K)) A = _
  rw [CartierDivisor.relativeDegree_apply]
  exact (TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_eq_relativeDegree K hdim
    ((eqToIso (CartierDivisor.toInvertibleSheaf_obj A)) ≪≫
      A.sheafIsoToWeilDivisor hdim)).symm

theorem properSmoothCurveCartierDegree_congr
    (hY : topologicalKrullDim Y = 1) (A B : CartierDivisor Y)
    (e : A.sheaf ≅ B.sheaf) :
    properCurveCartierDegree (K := K) hY A =
      properCurveCartierDegree (K := K) hY B := by
  rw [properSmoothCurveCartierDegree_eq_eulerDegree,
    properSmoothCurveCartierDegree_eq_eulerDegree]
  exact TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_congr K
    ((eqToIso (CartierDivisor.toInvertibleSheaf_obj A)) ≪≫ e ≪≫
      (eqToIso (CartierDivisor.toInvertibleSheaf_obj B)).symm)

theorem properSmoothCurveOrderBound_congr
    (hY : topologicalKrullDim Y = 1) (A B : CartierDivisor Y)
    (e : A.sheaf ≅ B.sheaf) :
    properCurveOrderBound (K := K) hY A = properCurveOrderBound (K := K) hY B := by
  unfold properCurveOrderBound
  rw [properSmoothCurveCartierDegree_congr (K := K) hY A B e]

theorem properSmoothCurveCartierDegree_nonneg_of_nonzero_section
    (hY : topologicalKrullDim Y = 1) (A : CartierDivisor Y)
    (s : Γ(A.sheaf, ⊤)) (hs : s ≠ 0) :
    0 ≤ properCurveCartierDegree (K := K) hY A := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : ∀ y : TauCeti.AlgebraicGeometry.CodimensionOnePoint Y,
      IsDiscreteValuationRing (Y.presheaf.stalk (y : Y)) := fun y ↦
    smoothOverField_codimensionOne_stalk_DVR (K := K) y
  let Z := cartierSectionZeroDivisor A s hs
  have hdeg : 0 ≤ properCurveCartierDegree (K := K) hY Z := by
    change 0 ≤ CartierDivisor.relativeDegree (Y ↘ Spec (CommRingCat.of K)) Z
    rw [CartierDivisor.relativeDegree_apply]
    exact TauCeti.AlgebraicGeometry.SchemeWeilDivisor.relativeDegree_nonneg _
      (cartierSectionZeroDivisor_toWeilDivisor_isEffective A s hs)
  exact hdeg.trans_eq (properSmoothCurve_sectionZeroDivisor_degree (K := K) hY A s hs)

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def cartierCurvePullbackDegree (D : CartierDivisor X) (φ : Y ⟶ X) : ℤ :=
  (cartierPullbackLineBundle D φ).eulerDegree K

noncomputable def cartierCurvePullbackOrderBound (D : CartierDivisor X) (φ : Y ⟶ X) : ℕ :=
  (cartierCurvePullbackDegree (K := K) D φ).toNat

omit [IsIntegral Y] [IsProper (Y ↘ Spec (CommRingCat.of K))]
  [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem cartierCurvePullbackDegree_eq_eulerCharacteristicDifference
    (D : CartierDivisor X) (φ : Y ⟶ X) :
    cartierCurvePullbackDegree (K := K) D φ =
      Scheme.Modules.eulerCharBelow K Y
        ((Scheme.Modules.pullback φ).obj D.sheaf) 2 -
      Scheme.Modules.eulerCharBelow K Y
        (SheafOfModules.unit Y.ringCatSheaf) 2 := by
  rw [cartierCurvePullbackDegree,
    TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_eq_sub_unit,
    cartierPullbackLineBundle_obj]

theorem cartierCurvePullbackDegree_eq_representation_degree
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (A : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) :
    cartierCurvePullbackDegree (K := K) D φ =
      properCurveCartierDegree (K := K) hY A := by
  rw [properSmoothCurveCartierDegree_eq_eulerDegree]
  exact TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_congr K
    ((eqToIso (cartierPullbackLineBundle_obj D φ)) ≪≫ a ≪≫
      (eqToIso (CartierDivisor.toInvertibleSheaf_obj A)).symm)

theorem cartierCurvePullbackOrderBound_eq_representation_bound
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (A : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) :
    cartierCurvePullbackOrderBound (K := K) D φ =
      properCurveOrderBound (K := K) hY A := by
  unfold cartierCurvePullbackOrderBound properCurveOrderBound
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hY D φ A a]

omit [IsIntegral Y] [IsProper (Y ↘ Spec (CommRingCat.of K))]
  [Smooth (Y ↘ Spec (CommRingCat.of K))] in
theorem cartierCurvePullbackDegree_congr (D E : CartierDivisor X) (φ : Y ⟶ X)
    (e : D.sheaf ≅ E.sheaf) :
    cartierCurvePullbackDegree (K := K) D φ = cartierCurvePullbackDegree (K := K) E φ := by
  exact TauCeti.AlgebraicGeometry.InvertibleSheaf.eulerDegree_congr K
    ((eqToIso (cartierPullbackLineBundle_obj D φ)) ≪≫
      (Scheme.Modules.pullback φ).mapIso e ≪≫
        (eqToIso (cartierPullbackLineBundle_obj E φ)).symm)

theorem cartierCurvePullbackDegree_nsmul
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X) (j : ℕ) :
    cartierCurvePullbackDegree (K := K) (j • D) φ =
      (j : ℤ) * cartierCurvePullbackDegree (K := K) D φ := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hY (j • D) φ
    (j • A) (cartierPullbackGradedIso D φ A a j),
    properCurveCartierDegree_nsmul,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hY D φ A a]

theorem cartierCurvePullbackDegree_add
    (hY : topologicalKrullDim Y = 1) (D E : CartierDivisor X) (φ : Y ⟶ X) :
    cartierCurvePullbackDegree (K := K) (D + E) φ =
      cartierCurvePullbackDegree (K := K) D φ + cartierCurvePullbackDegree (K := K) E φ := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  obtain ⟨B, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E φ
  let e : (Scheme.Modules.pullback φ).obj (D + E).sheaf ≅ (A + B).sheaf :=
    (Scheme.Modules.pullback φ).mapIso (cartierTensorSheafIso D E).symm ≪≫
      cartierPullbackTensorIso D φ E.sheaf ≪≫
        CategoryTheory.MonoidalCategory.tensorIso a b ≪≫ cartierTensorSheafIso A B
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hY (D + E) φ
      (A + B) e,
    properCurveCartierDegree_add,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hY D φ A a,
    cartierCurvePullbackDegree_eq_representation_degree (K := K) hY E φ B b]

theorem cartierCurvePullbackDegree_zero
    (hY : topologicalKrullDim Y = 1) (φ : Y ⟶ X) :
    cartierCurvePullbackDegree (K := K) (0 : CartierDivisor X) φ = 0 := by
  simpa only [zero_nsmul, Nat.cast_zero, zero_mul] using
    cartierCurvePullbackDegree_nsmul (K := K) hY (0 : CartierDivisor X) φ 0

noncomputable def cartierCurvePullbackDegreeHom
    (hY : topologicalKrullDim Y = 1) (φ : Y ⟶ X) : CartierDivisor X →+ ℤ where
  toFun D := cartierCurvePullbackDegree (K := K) D φ
  map_zero' := cartierCurvePullbackDegree_zero (K := K) hY φ
  map_add' D E := cartierCurvePullbackDegree_add (K := K) hY D E φ

theorem cartierCurvePullbackDegree_sum {ι : Type*}
    (hY : topologicalKrullDim Y = 1) (φ : Y ⟶ X)
    (S : Finset ι) (D : ι → CartierDivisor X) :
    cartierCurvePullbackDegree (K := K) (∑ i ∈ S, D i) φ =
      ∑ i ∈ S, cartierCurvePullbackDegree (K := K) (D i) φ := by
  exact map_sum (cartierCurvePullbackDegreeHom (K := K) hY φ) D S

theorem cartierCurvePullbackDegree_nonneg_of_image_meets_nonvanishingOpen
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (s : Γ(D.sheaf, ⊤))
    (hHit : ∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen D s) :
    0 ≤ cartierCurvePullbackDegree (K := K) D φ := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hY D φ A a]
  apply properSmoothCurveCartierDegree_nonneg_of_nonzero_section
    (K := K) hY A (cartierPullbackGlobalSectionViaIso D φ A a s)
  exact (cartierPullbackGlobalSectionViaIso_ne_zero_iff D φ A a s).mpr
    ((cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen D φ s).mpr hHit)

theorem cartierCurvePullbackDegree_neg_implies_pullbackSection_zero
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (hneg : cartierCurvePullbackDegree (K := K) D φ < 0) (s : Γ(D.sheaf, ⊤)) :
    modulePullbackGlobalSections φ D.sheaf s = 0 := by
  by_contra hs
  have hHit := (cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen D φ s).mp hs
  exact (not_le_of_gt hneg)
    (cartierCurvePullbackDegree_nonneg_of_image_meets_nonvanishingOpen (K := K) hY D φ s hHit)

theorem cartierCurvePullbackOrderBound_nsmul
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X) (j : ℕ) :
    cartierCurvePullbackOrderBound (K := K) (j • D) φ =
      j * cartierCurvePullbackOrderBound (K := K) D φ := by
  unfold cartierCurvePullbackOrderBound
  rw [cartierCurvePullbackDegree_nsmul (K := K) hY D φ j]
  by_cases h : 0 ≤ cartierCurvePullbackDegree (K := K) D φ
  · rw [Int.toNat_mul (Int.natCast_nonneg j) h, Int.toNat_natCast]
  · have hd : cartierCurvePullbackDegree (K := K) D φ ≤ 0 := le_of_not_ge h
    rw [Int.toNat_of_nonpos hd, mul_zero,
      Int.toNat_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg j) hd)]

theorem cartierSourceOrder_le_intrinsic_fixed_curve_linearBound
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (j : ℕ) (y : Y) (hClosed : IsClosed {y}) (s : Γ((j • D).sheaf, ⊤))
    (hHit : ∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen (j • D) s) :
    cartierSectionVanishingOrder (j • D) (φ y) s ≤
      j * cartierCurvePullbackOrderBound (K := K) D φ := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierCurvePullbackOrderBound_eq_representation_bound (K := K) hY D φ A a]
  exact cartierSourceOrder_le_linearBound_of_one_fixed_curve_representation
    (K := K) hY D φ A a j y hClosed s hHit

include K in
theorem cartierFixedCurve_exists_positive_intrinsic_linearBound
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X) :
    ∃ C : ℕ, 0 < C ∧ ∀ (j : ℕ) (y : Y), IsClosed {y} →
      ∀ s : Γ((j • D).sheaf, ⊤),
        (∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen (j • D) s) →
          cartierSectionVanishingOrder (j • D) (φ y) s ≤ j * C := by
  refine ⟨cartierCurvePullbackOrderBound (K := K) D φ + 1, by omega, ?_⟩
  intro j y hClosed s hHit
  apply (cartierSourceOrder_le_intrinsic_fixed_curve_linearBound
    (K := K) hY D φ j y hClosed s hHit).trans
  exact_mod_cast Nat.mul_le_mul_left j (Nat.le_succ _)

end MixedFujita

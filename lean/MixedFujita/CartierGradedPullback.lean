/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GlobalCartierPullbackTensor
public import MixedFujita.CurveNonvanishingOrderBounds
public import TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct

/-!
One actual Cartier representation of the pullback of O(D) on an integral
target constructs representations of every actual pullback of O(j D)
by O(j A) for the same divisor A. The canonical tensor comparison and
Cartier multiplication tensor isomorphism give a recursive family, with
explicit zero and successor formulas. No per-degree representation input
is supplied. Compatibility with multiplication for arbitrary pairs of
degrees is not asserted by these formulas.
On a fixed actual proper smooth integral curve, this family removes the
per-degree representation input from the proved source-order bound j C,
provided the actual curve image meets the source section nonvanishing open.
Selecting such a curve through a specified point and bounding its degree
uniformly as the curve varies remain separate mathematical obligations.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def cartierZeroSheafIso (X : Scheme.{u}) [IsIntegral X] :
    (0 : CartierDivisor X).sheaf ≅ SheafOfModules.unit X.ringCatSheaf := by
  simpa only [principalCartierDivisor_one] using
    (CartierDivisor.unitIsoSheafPrincipalCartierDivisor X 1).symm

noncomputable def cartierTensorSheafIso (D E : CartierDivisor X) :
    D.sheaf ⊗ E.sheaf ≅ (D + E).sheaf :=
  D.sheaf.tensorUnderlyingIso E.sheaf ≪≫
    (TauCeti.SheafOfModules.tensorProductIso X.sheaf D.sheaf E.sheaf).symm ≪≫
      CartierDivisor.tensorProductSheafIso D E

noncomputable def cartierSuccessorTensorSheafIso (D : CartierDivisor X) (j : ℕ) :
    ((j + 1) • D).sheaf ≅ (j • D).sheaf ⊗ D.sheaf :=
  eqToIso (congrArg CartierDivisor.sheaf (succ_nsmul D j)) ≪≫
    (cartierTensorSheafIso (j • D) D).symm

noncomputable def cartierPullbackGradedIso
    (D : CartierDivisor X) (φ : Y ⟶ X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) :
    ∀ j : ℕ, (Scheme.Modules.pullback φ).obj (j • D).sheaf ≅ (j • A).sheaf
  | 0 =>
    (Scheme.Modules.pullback φ).mapIso
      (eqToIso (congrArg CartierDivisor.sheaf (zero_nsmul D))) ≪≫
        (Scheme.Modules.pullback φ).mapIso (cartierZeroSheafIso X) ≪≫
          Scheme.Modules.pullbackObjUnitIso φ ≪≫ (cartierZeroSheafIso Y).symm ≪≫
            eqToIso (congrArg CartierDivisor.sheaf (zero_nsmul A).symm)
  | j + 1 =>
    (Scheme.Modules.pullback φ).mapIso (cartierSuccessorTensorSheafIso D j) ≪≫
      cartierPullbackTensorIso (j • D) φ D.sheaf ≪≫
        tensorIso (cartierPullbackGradedIso D φ A a j) a ≪≫
          (cartierSuccessorTensorSheafIso A j).symm

theorem cartierPullbackGradedIso_succ
    (D : CartierDivisor X) (φ : Y ⟶ X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) (j : ℕ) :
    cartierPullbackGradedIso D φ A a (j + 1) =
      (Scheme.Modules.pullback φ).mapIso (cartierSuccessorTensorSheafIso D j) ≪≫
        cartierPullbackTensorIso (j • D) φ D.sheaf ≪≫
          tensorIso (cartierPullbackGradedIso D φ A a j) a ≪≫
            (cartierSuccessorTensorSheafIso A j).symm := rfl

theorem cartierPullbackGradedIso_zero
    (D : CartierDivisor X) (φ : Y ⟶ X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf) :
    cartierPullbackGradedIso D φ A a 0 =
      (Scheme.Modules.pullback φ).mapIso
        (eqToIso (congrArg CartierDivisor.sheaf (zero_nsmul D))) ≪≫
          (Scheme.Modules.pullback φ).mapIso (cartierZeroSheafIso X) ≪≫
            Scheme.Modules.pullbackObjUnitIso φ ≪≫ (cartierZeroSheafIso Y).symm ≪≫
              eqToIso (congrArg CartierDivisor.sheaf (zero_nsmul A).symm) := rfl

theorem cartierPullback_exists_fixed_all_degrees_representation
    (D : CartierDivisor X) (φ : Y ⟶ X) :
    ∃ A : CartierDivisor Y, ∀ j : ℕ,
      Nonempty ((Scheme.Modules.pullback φ).obj (j • D).sheaf ≅ (j • A).sheaf) := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  exact ⟨A, fun j ↦ ⟨cartierPullbackGradedIso D φ A a j⟩⟩

variable {K : Type u} [Field K] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem cartierSourceOrder_le_linearBound_of_one_fixed_curve_representation
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (A : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf)
    (j : ℕ) (y : Y) (hClosed : IsClosed {y}) (s : Γ((j • D).sheaf, ⊤))
    (hHit : ∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen (j • D) s) :
    cartierSectionVanishingOrder (j • D) (φ y) s ≤
      j * properCurveOrderBound (K := K) hY A := by
  exact cartierSourceOrder_le_linearBound_of_graded_curve_image_meets_nonvanishingOpen
    (K := K) hY (j • D) φ A j (cartierPullbackGradedIso D φ A a j) y hClosed s hHit

theorem cartierFixedCurve_exists_all_degrees_representation_and_linear_order_bound
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X) :
    ∃ A : CartierDivisor Y,
      (∀ j : ℕ, Nonempty ((Scheme.Modules.pullback φ).obj (j • D).sheaf ≅ (j • A).sheaf)) ∧
      ∀ (j : ℕ) (y : Y), IsClosed {y} → ∀ s : Γ((j • D).sheaf, ⊤),
        (∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen (j • D) s) →
          cartierSectionVanishingOrder (j • D) (φ y) s ≤
            j * properCurveOrderBound (K := K) hY A := by
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  refine ⟨A, (fun j ↦ ⟨cartierPullbackGradedIso D φ A a j⟩), ?_⟩
  intro j y hClosed s hHit
  exact cartierSourceOrder_le_linearBound_of_one_fixed_curve_representation
    (K := K) hY D φ A a j y hClosed s hHit
end MixedFujita

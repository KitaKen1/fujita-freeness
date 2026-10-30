/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InvertibleAffineDenominators
public import MixedFujita.ModuleGlobalGeneration
public import MixedFujita.DominantCartierGlobalGenerationPullback
public import MixedFujita.PrincipalizedGlobalGeneration

/-! On an affine integral scheme every Cartier divisor, with either sign, is
globally generated. Clearing one denominator of a local frame constructs the
actual generating section. Dominant pullbacks therefore have degree zero on
every proper test curve, and adding them preserves nefness. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Clear a denominator of an actual Cartier frame to obtain a global section
whose coefficient remains a unit at the chosen point. -/
theorem cartierIsGloballyGenerated_of_isAffine
    {X : Scheme.{u}} [IsIntegral X] [IsAffine X] (D : CartierDivisor X) :
    CartierIsGloballyGenerated D := by
  classical
  apply (cartierIsGloballyGenerated_iff_module D).mpr
  intro x
  let C := cartierEquationOpenCover D
  let : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
  let e := cartierOpenFrameIso D (C.U x) (C.equation x) (C.equation_eq x)
  obtain ⟨f, hfle, hxf⟩ := (isAffineOpen_top X).exists_basicOpen_le
    (V := C.U x) ⟨x, C.mem x⟩ trivial
  let V := X.basicOpen f
  let d := moduleOverFrameRestrictIso D.sheaf (C.U x) e V hfle
  let c := moduleOverFrameCoefficient D.sheaf V d V le_rfl
  obtain ⟨m, t, ht⟩ := invertibleAffine_clear_denominator D.sheaf D.isInvertible_sheaf
    ⟨⊤, isAffineOpen_top X⟩ f (c.symm 1)
  refine ⟨V, hxf, d, t, ?_⟩
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [ht, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one,
    map_pow, X.presheaf.germ_res_apply]
  exact ((X.mem_basicOpen f x trivial).mp hxf).pow m

/-- Every dominant pullback from an affine integral scheme is globally generated. -/
theorem cartierIsGloballyGenerated_pullback_of_isAffine
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsAffine X]
    (ρ : T ⟶ X) [IsDominant ρ] (D : CartierDivisor X) :
    CartierIsGloballyGenerated (cartierPullback ρ D) :=
  cartierIsGloballyGenerated_dominant_pullback ρ D (cartierIsGloballyGenerated_of_isAffine D)

/-- Even global generation is unchanged by an affine pullback: its inverse
also has actual generating sections. -/
theorem cartierIsGloballyGenerated_add_affine_pullback_iff
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsAffine X]
    (ρ : T ⟶ X) [IsDominant ρ] (D : CartierDivisor X) (A : CartierDivisor T) :
    CartierIsGloballyGenerated (A + cartierPullback ρ D) ↔ CartierIsGloballyGenerated A := by
  constructor
  · intro h
    have hg := cartierIsGloballyGenerated_add _ _ h
      (cartierIsGloballyGenerated_pullback_of_isAffine ρ (-D))
    rwa [add_assoc, ← cartierPullback_add, add_neg_cancel, cartierPullback_zero, add_zero] at hg
  · exact fun h => cartierIsGloballyGenerated_add _ _ h
      (cartierIsGloballyGenerated_pullback_of_isAffine ρ D)

variable {K : Type u} [Field K] {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsAffine X]
  [T.Over (Spec (CommRingCat.of K))]

/-- No positivity on the affine source divisor is needed. -/
theorem cartierIsNef_pullback_of_isAffine (ρ : T ⟶ X) [IsDominant ρ]
    (D : CartierDivisor X) : CartierIsNef K (cartierPullback ρ D) :=
  cartierIsGloballyGenerated_isNef (cartierIsGloballyGenerated_pullback_of_isAffine ρ D)

/-- Both signs are nef, so the actual curve degree of an affine pullback is zero. -/
theorem cartierCurvePullbackDegree_affine_pullback_eq_zero
    (ρ : T ⟶ X) [IsDominant ρ] (D : CartierDivisor X)
    {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (φ : C ⟶ T)
    (hφ : φ ≫ (T ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K)) :
    cartierCurvePullbackDegree (K := K) (cartierPullback ρ D) φ = 0 := by
  have hp := cartierIsNef_pullback_of_isAffine (K := K) ρ D C hC φ hφ
  have hn := cartierIsNef_pullback_of_isAffine (K := K) ρ (-D) C hC φ hφ
  have hz : cartierPullback ρ D + cartierPullback ρ (-D) = 0 := by
    rw [← cartierPullback_add, add_neg_cancel, cartierPullback_zero]
  have he := congrArg (fun A => cartierCurvePullbackDegree (K := K) A φ) hz
  rw [cartierCurvePullbackDegree_add (K := K) hC,
    cartierCurvePullbackDegree_zero (K := K) hC] at he
  omega

/-- Adding an affine pullback does not change the original nef predicate. -/
theorem cartierIsNef_add_affine_pullback_iff (ρ : T ⟶ X) [IsDominant ρ]
    (D : CartierDivisor X) (A : CartierDivisor T) :
    CartierIsNef K (A + cartierPullback ρ D) ↔ CartierIsNef K A := by
  constructor <;> intro h C _ _ _ _ hC φ hφ
  · have hc := h C hC φ hφ
    rwa [cartierCurvePullbackDegree_add (K := K) hC,
      cartierCurvePullbackDegree_affine_pullback_eq_zero ρ D hC φ hφ, add_zero] at hc
  · rw [cartierCurvePullbackDegree_add (K := K) hC,
      cartierCurvePullbackDegree_affine_pullback_eq_zero ρ D hC φ hφ, add_zero]
    exact h C hC φ hφ

end MixedFujita

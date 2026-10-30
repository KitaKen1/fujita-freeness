/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualModuleEulerCharacteristic
public import MixedFujita.MixedForwardDifference
public import MixedFujita.ZeroDimensionalCartierFreeness
public import MixedFujita.CartierCutEuler

/-! 実Cartier混合Euler差分・Picard不変性・打切り非依存と零次元消滅。 See reports/check-219-mixed-euler-intersection-foundation.json for the verified scope. The ordinary mixed-intersection dimension bound in dimension at least two remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Mixed actual Euler differences are computed from the original Cartier
sheaves, with no assumed intersection numbers, Euler polynomial or flag. -/
noncomputable def cartierMixedEulerDifference
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (E : CartierDivisor X) : ℤ :=
  mixedForwardDifference D (fun F => Scheme.Modules.eulerChar
    (X ↘ Spec (CommRingCat.of K)) F.sheaf) E


/-- Actual mixed Euler differences have the Cartier-cut recurrence. -/
theorem cartierMixedEulerDifference_cons
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierMixedEulerDifference K (H :: D) E =
      cartierMixedEulerDifference K D (E + H) - cartierMixedEulerDifference K D E := rfl


/-- The order of the actual Cartier directions does not affect the coefficient. -/
theorem cartierMixedEulerDifference_perm
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    {D F : List (CartierDivisor X)} (h : D.Perm F) (E : CartierDivisor X) :
    cartierMixedEulerDifference K D E = cartierMixedEulerDifference K F E := by
  exact congrFun (mixedForwardDifference_perm h _) E


/-- An actual isomorphism of the base Cartier sheaves preserves every mixed
Euler coefficient, including all translates used in its construction. -/
theorem cartierMixedEulerDifference_base_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) {E F : CartierDivisor X} (a : E.sheaf ≅ F.sheaf) :
    cartierMixedEulerDifference K D E = cartierMixedEulerDifference K D F := by
  induction D generalizing E F with
  | nil => exact moduleEulerChar_congr K a
  | cons H D ih =>
    rw [cartierMixedEulerDifference_cons, cartierMixedEulerDifference_cons]
    exact congrArg₂ (· - ·)
      (ih ((cartierTensorSheafIso E H).symm ≪≫ tensorIso a (Iso.refl H.sheaf) ≪≫
        cartierTensorSheafIso F H)) (ih a)


/-- Actual sheaf isomorphisms of every Cartier direction preserve the mixed
coefficient. In particular the directions depend only on their Picard classes. -/
theorem cartierMixedEulerDifference_direction_isos
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    {D F : List (CartierDivisor X)}
    (h : List.Forall₂ (fun H J : CartierDivisor X => Nonempty (H.sheaf ≅ J.sheaf)) D F)
    (E : CartierDivisor X) :
    cartierMixedEulerDifference K D E = cartierMixedEulerDifference K F E := by
  induction h generalizing E with
  | nil => rfl
  | @cons H J D F hHJ hDF ih =>
    obtain ⟨a⟩ := hHJ
    rw [cartierMixedEulerDifference_cons, cartierMixedEulerDifference_cons]
    have hbase := cartierMixedEulerDifference_base_iso K F
      ((cartierTensorSheafIso E H).symm ≪≫ tensorIso (Iso.refl E.sheaf) a ≪≫
        cartierTensorSheafIso E J)
    exact congrArg₂ (· - ·) ((ih (E + H)).trans hbase) (ih E)


/-- Principal shifts of the base factor leave all actual mixed Euler differences unchanged. -/
theorem cartierMixedEulerDifference_base_principal
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (E : CartierDivisor X) (φ : X.functionFieldˣ) :
    cartierMixedEulerDifference K D (E + principalCartierDivisor X φ) =
      cartierMixedEulerDifference K D E :=
  cartierMixedEulerDifference_base_iso K D (cartierSheafPrincipalShiftIso E φ)


/-- A principal shift of a Cartier direction leaves the mixed Euler difference unchanged. -/
theorem cartierMixedEulerDifference_direction_principal
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) (φ : X.functionFieldˣ) :
    cartierMixedEulerDifference K ((H + principalCartierDivisor X φ) :: D) E =
      cartierMixedEulerDifference K (H :: D) E := by
  apply cartierMixedEulerDifference_direction_isos K
  have hrefl : List.Forall₂ (fun H J : CartierDivisor X => Nonempty (H.sheaf ≅ J.sheaf)) D D := by
    induction D with
    | nil => exact .nil
    | cons J D ih => exact .cons ⟨Iso.refl J.sheaf⟩ ih
  exact List.Forall₂.cons ⟨cartierSheafPrincipalShiftIso H φ⟩ hrefl


/-- Additivity is proved once the actual next difference vanishes. Geometric
vanishing of dimension+1 differences is not supplied by this identity. -/
theorem cartierMixedEulerDifference_add_of_next_vanishing
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H J E : CartierDivisor X)
    (hvan : cartierMixedEulerDifference K (H :: J :: D) E = 0) :
    cartierMixedEulerDifference K ((H + J) :: D) E =
      cartierMixedEulerDifference K (H :: D) E + cartierMixedEulerDifference K (J :: D) E := by
  have h := mixedForwardDifference_add_direction D H J
    (fun F => Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf) E
  change cartierMixedEulerDifference K ((H + J) :: D) E =
    cartierMixedEulerDifference K (H :: D) E + cartierMixedEulerDifference K (J :: D) E +
      cartierMixedEulerDifference K (H :: J :: D) E at h
  simpa only [hvan, add_zero] using h


/-- In ordinary dimension zero every nonempty mixed Cartier Euler difference
vanishes. This is the actual geometric base case for higher nilpotence. -/
theorem zeroDimensional_cartierMixedEulerDifference_vanishes
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 0)
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) :
    cartierMixedEulerDifference K (H :: D) E = 0 := by
  rw [cartierMixedEulerDifference_cons, zeroDimensional_cartierDivisor_eq_zero hdim H,
    add_zero, sub_self]


/-- On a proper source every full mixed Euler difference agrees with the
existing actual truncated Euler construction above the ordinary dimension.
Thus the new coefficients do not depend on a chosen cohomology cutoff. -/
theorem proper_cartierMixedEulerDifference_eq_truncated
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (n : ℕ) (hn : topologicalKrullDim X < n) :
    cartierMixedEulerDifference K D E =
      mixedForwardDifference D (fun F : CartierDivisor X =>
        Scheme.Modules.eulerCharBelow K X F.sheaf n) E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hfun : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (X ↘ Spec (CommRingCat.of K)) F.sheaf) =
      fun F : CartierDivisor X => Scheme.Modules.eulerCharBelow K X F.sheaf n := by
    funext F
    exact moduleEulerChar_eq_eulerCharBelow_of_dim_lt K F.sheaf n hn
  unfold cartierMixedEulerDifference
  rw [hfun]

end MixedFujita

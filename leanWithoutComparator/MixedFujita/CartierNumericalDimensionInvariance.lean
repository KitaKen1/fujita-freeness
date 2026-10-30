/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalDimension
public import MixedFujita.TopMixedEulerHomogeneity

/-! 元数値次元の実層同型・正整数倍・主因子不変性。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Mixed powers respect any actual isomorphism of the ORIGINAL Cartier
line bundles in the first factor. -/
theorem cartierMixedPowerIntersection_direction_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D F J : CartierDivisor X)
    (a : D.sheaf ≅ F.sheaf) (k : Fin (n + 1)) :
    cartierMixedPowerIntersection K n hdim D J k = cartierMixedPowerIntersection K n hdim F J k := by
  have hrep : ∀ r : ℕ, List.Forall₂ (fun H L : CartierDivisor X => Nonempty (H.sheaf ≅ L.sheaf))
      (List.replicate r D) (List.replicate r F) := by
    intro r
    induction r with
    | zero => exact .nil
    | succ r ih => exact .cons ⟨a⟩ ih
  have href : ∀ r : ℕ, List.Forall₂ (fun H L : CartierDivisor X => Nonempty (H.sheaf ≅ L.sheaf))
      (List.replicate r J) (List.replicate r J) := by
    intro r
    induction r with
    | zero => exact .nil
    | succ r ih => exact .cons ⟨Iso.refl J.sheaf⟩ ih
  have hcat : ∀ r : ℕ, List.Forall₂ (fun H L : CartierDivisor X => Nonempty (H.sheaf ≅ L.sheaf))
      (List.replicate r D ++ List.replicate (n - k.val) J)
      (List.replicate r F ++ List.replicate (n - k.val) J) := by
    intro r
    induction r with
    | zero => exact href (n - k.val)
    | succ r ih => exact .cons ⟨a⟩ ih
  exact cartierMixedEulerDifference_direction_isos K (hcat k.val) 0


/-- The original numerical dimension respects actual Cartier line-bundle
isomorphism, independently of section-growth definitions. -/
theorem cartierNumericalDimension_direction_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D F J : CartierDivisor X)
    (a : D.sheaf ≅ F.sheaf) :
    cartierNumericalDimension K n hdim D J = cartierNumericalDimension K n hdim F J := by
  unfold cartierNumericalDimension
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    cartierMixedPowerIntersection_direction_iso K n hdim D F J a]


/-- Positive scaling of D scales its kth original mixed power by q^k. -/
theorem cartierMixedPowerIntersection_nsmul
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X)
    (q : ℕ) (k : Fin (n + 1)) :
    cartierMixedPowerIntersection K n hdim (q • D) J k =
      (q : ℤ) ^ k.val * cartierMixedPowerIntersection K n hdim D J k := by
  have hlen : (List.replicate k.val D).length + (List.replicate (n - k.val) J).length = n := by
    simp only [List.length_replicate]
    omega
  change cartierMixedEulerDifference K (List.replicate k.val (q • D) ++
      List.replicate (n - k.val) J) 0 =
    (q : ℤ) ^ k.val * cartierMixedEulerDifference K
      (List.replicate k.val D ++ List.replicate (n - k.val) J) 0
  simpa only [List.map_replicate, List.length_replicate] using
    proper_cartierMixedEulerDifference_top_nsmul_prefix K n hdim.le
      (List.replicate k.val D) (List.replicate (n - k.val) J) hlen 0 q


/-- The original maximum of positive mixed powers is invariant under
positive multiples, by actual factor homogeneity. -/
theorem cartierNumericalDimension_nsmul
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X)
    (q : ℕ) (hq : 0 < q) :
    cartierNumericalDimension K n hdim (q • D) J = cartierNumericalDimension K n hdim D J := by
  unfold cartierNumericalDimension
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, cartierMixedPowerIntersection_nsmul]
  exact mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hq : (0 : ℤ) < q) k.val)


/-- Actual Cartier principal shifts preserve the original numerical dimension. -/
theorem cartierNumericalDimension_principal_shift
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X) (f : X.functionFieldˣ) :
    cartierNumericalDimension K n hdim (D + principalCartierDivisor X f) J =
      cartierNumericalDimension K n hdim D J :=
  cartierNumericalDimension_direction_iso K n hdim _ D J (cartierSheafPrincipalShiftIso D f)

end MixedFujita

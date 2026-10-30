/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalDimensionPullbackBound
public import MixedFujita.SemiampleContractionProof
public import MixedFujita.CartierIitakaMultiples
public import MixedFujita.ProjectiveCartierPullbackDictionary

/-! 実semiample収縮の内部構成による全飯高次元での元ν≤κとκ=0の等号。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- For EVERY original semiample divisor on a normal projective source,
the manuscript numerical dimension is at most its original Iitaka exponent.
The contraction, base dimension, Cartier comparison and positive multiple
are constructed internally; the reverse inequality remains separate. -/
theorem proper_semiample_cartierNumericalDimension_le_iitaka
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) :
    cartierNumericalDimension K n hdim D J ≤ k := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  obtain ⟨q, hq, hgen⟩ := hD
  have hkq : CartierIitakaDimension K (q • D) k :=
    (cartierIitakaDimension_nsmul_iff_of_ample_ambient hdim hn hJ D hq k).mp hkappa
  have hfree : ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → CartierIsGloballyGenerated (t • (q • D)) :=
    ⟨0, fun t _ => cartierIsGloballyGenerated_nsmul (q • D) hgen t⟩
  obtain ⟨B, hB, hBN, hBO, hBft, p, hpdom, hpo, H, f, hp, hpropB, hconn,
      hdimB, hnormB, hcovB, happ, hH, hEq⟩ :=
    eventuallyGloballyGenerated_exists_normal_ample_cartier_contraction
      hdim hn hJ (q • D) hfree hnorm hkq
  let := hB
  let := hBN
  let := hBO
  let := hBft
  let := hpdom
  let := hpo
  let := hpropB
  let a : (Scheme.Modules.pullback p).obj H.sheaf ≅ (q • D).sheaf :=
    projectiveCartierPullbackIso ⟨H, hH⟩ p H ≪≫
      (cartierSheafPrincipalShiftIso (cartierPullback p H) f).symm ≪≫
        eqToIso (congrArg CartierDivisor.sheaf hEq.symm)
  exact cartierNumericalDimension_le_base_dimension_of_multiple_pullback
    K n hdim k hdimB.le p H D J q hq a


/-- The original intersection-theoretic numerical dimension equals zero
for every original semiample divisor of original Iitaka exponent zero. -/
theorem proper_semiample_iitaka_zero_cartierNumericalDimension_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (hkappa : CartierIitakaDimension K D 0) :
    cartierNumericalDimension K n hdim D J = 0 := by
  exact Nat.eq_zero_of_le_zero
    (proper_semiample_cartierNumericalDimension_le_iitaka K n hdim hn hnorm D J hJ hD 0 hkappa)

end MixedFujita

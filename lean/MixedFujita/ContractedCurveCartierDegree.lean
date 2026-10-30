/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierPullbackNonvanishing
public import MixedFujita.CartierCurveIntrinsicDegree
public import MixedFujita.CartierSectionsAtlas

/-! 実射影切断写像が収縮する曲線の元の内在的次数零。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A smooth proper curve mapping entirely into one section's actual
nonvanishing open has original intrinsic pullback degree zero. -/
theorem cartierCurvePullbackDegree_zero_of_image_nonvanishing
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (D : CartierDivisor X) (φ : C ⟶ X) (s : Γ(D.sheaf, ⊤))
    (h : ∀ c : C, φ c ∈ cartierSectionNonvanishingOpen D s) :
    cartierCurvePullbackDegree (K := K) D φ = 0 := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  obtain ⟨f, hf⟩ := cartierPullback_representation_principal_of_image_nonvanishing D φ E a s h
  rw [cartierCurvePullbackDegree_eq_representation_degree (K := K) hC D φ E a, hf]
  exact properSmoothCurve_principalCartierDegree_zero hC f


/-- Every curve contracted by the ACTUAL Cartier section morphism has
zero original intrinsic degree. A tautological pullback comparison is unnecessary. -/
theorem cartierSectionsMap_contracted_curve_degree_zero
    (K : Type u) [Field K] {X C : Scheme.{u}} [IsIntegral X] [IsIntegral C]
    [X.Over (Spec (CommRingCat.of K))] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (D : CartierDivisor X)
    {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
    (hne : ∀ i, t (idx i) ≠ 0)
    (hcover : (⨆ i, cartierSectionNonvanishingOpen D (t (idx i))) = ⊤)
    (φ : C ⟶ X) (y : polynomialProjectiveScheme M K)
    (hconst : ∀ c : C, cartierSectionsMap K D t idx hne hcover (φ c) = y) :
    cartierCurvePullbackDegree (K := K) D φ = 0 := by
  obtain ⟨q, hq⟩ := polynomialProjective_exists_coordinate_chart M K y
  apply cartierCurvePullbackDegree_zero_of_image_nonvanishing K hC D φ (t q)
  intro c
  rw [← cartierSectionsMap_preimage (K := K) D t idx hne hcover q]
  change cartierSectionsMap K D t idx hne hcover (φ c) ∈ Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X q)
  rw [hconst c]
  exact hq

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionsNumericalFiniteness
public import MixedFujita.NefAmpleFiniteCurveDegree
public import MixedFujita.CartierGlobalGenerationFiniteFamily

/-! 元semiamplenessと有限曲線次数正値性から元ampleness・nef＋ampleへの接続。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Semiampleness and strict positive degree on every finite smooth
curve imply ORIGINAL ampleness. The projective map, all fiber curves,
finiteness and the positive ample multiple are constructed internally. -/
theorem cartierIsAmpleProj_of_semiample_of_positive_finite_curve_degree
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hsemi : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (hpos : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ (φ : C ⟶ X) [IsFinite φ] [φ.IsOver (Spec (CommRingCat.of K))],
        0 < cartierCurvePullbackDegree (K := K) D φ) :
    CartierIsAmpleProj K D := by
  classical
  obtain ⟨q, hq, hqgen⟩ := hsemi
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨M, t, ht⟩ := cartierIsGloballyGenerated_exists_fin_basePointFree (q • D) hqgen
  let I := ULift.{u} {i : Fin M // t i ≠ 0}
  let idx : I → Fin M := fun i => i.down.val
  have hne (i : I) : t (idx i) ≠ 0 := i.down.property
  have hcover : (⨆ i : I, cartierSectionNonvanishingOpen (q • D) (t (idx i))) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := ht x
    have hix : x ∈ cartierSectionNonvanishingOpen (q • D) (t i) :=
      (mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x _ _).mpr hi
    have hni : t i ≠ 0 := (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp ⟨⟨x, hix⟩⟩
    exact Opens.mem_iSup.mpr ⟨ULift.up ⟨i, hni⟩, hix⟩
  have hposq : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ (φ : C ⟶ X) [IsFinite φ] [φ.IsOver (Spec (CommRingCat.of K))],
        0 < cartierCurvePullbackDegree (K := K) (q • D) φ := by
    intro C _ _ _ _ hC φ _ _
    rw [cartierCurvePullbackDegree_nsmul (K := K) hC]
    exact mul_pos (by exact_mod_cast hq) (hpos C hC φ)
  let : IsFinite (cartierSectionsMap K (q • D) t idx hne hcover) :=
    cartierSectionsMap_isFinite_of_positive_finite_curve_degree K hProj (q • D) t idx hne hcover hposq
  exact cartierIsAmpleProj_of_positive_nsmul hq
    (cartierIsAmpleProj_of_finite_sectionsMap K (q • D) t idx hne hcover)


/-- An ORIGINAL nef plus ample Cartier class is originally ample once
its semiampleness is proved; no contraction or finite-map witness is input. -/
theorem nef_add_ample_isAmpleProj_of_semiample
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X) (hN : CartierIsNef K N) (hA : CartierIsAmpleProj K A)
    (hsemi : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • (N + A))) :
    CartierIsAmpleProj K (N + A) := by
  apply cartierIsAmpleProj_of_semiample_of_positive_finite_curve_degree K ⟨A, hA⟩ (N + A) hsemi
  intro C _ _ _ _ hC φ _ _
  exact nef_add_ample_finite_curve_pullback_degree_pos K hC N A hN hA φ

end MixedFujita

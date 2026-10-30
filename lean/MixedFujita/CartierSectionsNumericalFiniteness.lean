/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ContractedCurveCartierDegree
public import MixedFujita.ProjectiveClosedSourcesWithoutCurves
public import MixedFujita.ProperMapFiniteClosedFibers
public import MixedFujita.IntegralProjectiveCurveSmoothCover
public import MixedFujita.CartierAffineSectionAmpleness

/-! 有限smooth曲線上の元の次数正値性から実射影切断写像の有限性。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Strict positive degree on all actual finite smooth curve maps forces
the ACTUAL section morphism to be finite. Nonreduced fibers and component
curve extraction are handled internally, without supplied fiber witnesses. -/
theorem cartierSectionsMap_isFinite_of_positive_finite_curve_degree
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A) (D : CartierDivisor X)
    {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
    (hne : ∀ i, t (idx i) ≠ 0)
    (hcover : (⨆ i, cartierSectionNonvanishingOpen D (t (idx i))) = ⊤)
    (hpos : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ (φ : C ⟶ X) [IsFinite φ] [φ.IsOver (Spec (CommRingCat.of K))],
        0 < cartierCurvePullbackDegree (K := K) D φ) :
    IsFinite (cartierSectionsMap K D t idx hne hcover) := by
  let e := cartierSectionsMap K D t idx hne hcover
  let P := polynomialProjectiveScheme M K
  let : IsProper e := cartierSectionsMap_isProper D t idx hne hcover
  let : IsProper (polynomialProjectiveToBase M K) := polynomialProjectiveToBase_isProper M K
  let : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveToBase M K)
  apply properMap_isFinite_of_finite_closed_fibers e
  intro y hy
  let : IsClosedImmersion (P.fromSpecResidueField y) := isClosed_singleton_iff_isClosedImmersion.mp hy
  let F := e.fiber y
  let j : F ⟶ X := e.fiberι y
  let : IsClosedImmersion j := by
    change IsClosedImmersion (pullback.fst e (P.fromSpecResidueField y))
    infer_instance
  let : Finite F := projective_closed_source_finite_of_no_integral_curves K hProj j (by
    intro C hC i hi hdimC
    let := hC
    let := hi
    let k := i ≫ j
    let : C.Over (Spec (CommRingCat.of K)) := ⟨k ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : k.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (C ↘ Spec (CommRingCat.of K)) := by
      change IsProper (k ≫ (X ↘ Spec (CommRingCat.of K)))
      infer_instance
    have hProjC := integral_closed_source_exists_original_ample_cartier K k hProj
    obtain ⟨S, hS, hSo, r, hr, hrd, hro, hSp, hSs, hdimS⟩ :=
      proper_integral_curve_exists_finite_smooth_cover K hdimC hProjC
    let := hS
    let := hSo
    let := hr
    let := hro
    let := hSp
    let := hSs
    let φ := r ≫ k
    have hpositive := hpos S hdimS φ
    have hconstant : ∀ s : S, e (φ s) = y := by
      intro s
      change e (j (i (r s))) = y
      have hmem : j (i (r s)) ∈ e ⁻¹' {y} := by
        rw [← e.range_fiberι y]
        exact Set.mem_range_self (i (r s))
      exact hmem
    have hzero := cartierSectionsMap_contracted_curve_degree_zero K hdimS D t idx hne hcover φ y hconstant
    exact (ne_of_gt hpositive) hzero)
  have hfinite : (Set.range j).Finite := Set.finite_range j
  rwa [e.range_fiberι y] at hfinite


/-- Actual finiteness of the section map gives ORIGINAL Cartier
ampleness through its internally computed hyperplane and principal shift. -/
theorem cartierIsAmpleProj_of_finite_sectionsMap
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X)
    {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
    (hne : ∀ i, t (idx i) ≠ 0)
    (hcover : (⨆ i, cartierSectionNonvanishingOpen D (t (idx i))) = ⊤)
    [IsFinite (cartierSectionsMap K D t idx hne hcover)] : CartierIsAmpleProj K D := by
  let e := cartierSectionsMap K D t idx hne hcover
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show genericPoint X ∈ ⨆ i, cartierSectionNonvanishingOpen D (t (idx i)) by
    rw [hcover]; exact Opens.mem_top _)
  have hg : MvPolynomial.X (idx i) ∉ (e (genericPoint X)).asHomogeneousIdeal := by
    change genericPoint X ∈ e ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X (idx i))
    rw [cartierSectionsMap_preimage]
    exact hi
  rw [cartierSectionsMap_hyperplane D t idx hne hcover i hg]
  exact cartierIsAmpleProj_add_principal
    (projectiveHyperplaneCartier_isAmpleProj_of_finite e (MvPolynomial.X (idx i))
      (MvPolynomial.isHomogeneous_X K (idx i)) hg (cartierSectionsMap_over D t idx hne hcover)) _

end MixedFujita

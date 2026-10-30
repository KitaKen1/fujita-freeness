/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectivePointedFirstOrder
public import MixedFujita.LocalJetSpan
public import MixedFujita.ProjectiveHomogenization

/-!
Jets at a closed point of an actual closed subscheme of polynomial projective
space over an algebraically closed field are realized by actual pulled-back
homogeneous equations. For every degree D ≥ m, each stalk element agrees with
the germ of some f/X_k^D modulo the (m+1)-st power of the maximal ideal.
The translated coordinates generate the maximal ideal, the residue field is K,
and the answer polynomial is homogenized explicitly. Together with
JetHilbertBound this replaces pointed Bertini flags and ambient cohomology
windows in the uniform order bound by Hilbert bounds and jet dimensions.
Smoothness and integrality of the source are not used here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

/-- Every jet at a closed point of an actual closed projective subscheme is the jet
of an actual pulled-back homogeneous equation of any degree D ≥ m. -/
theorem polynomialProjective_closedImmersion_jet_realized
    (k : Fin n) (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k) (hx : IsClosed {x})
    {m D : ℕ} (hmD : m ≤ D) (y : Y.presheaf.stalk x) :
    ∃ (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous D),
      y - Y.presheaf.germ _ x hxk (projectivePullbackHomogeneousEquation e k D F hF) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ (m + 1) := by
  let U := projectivePullbackCoordinateOpen e k
  have hU : IsAffineOpen U := (Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X k)
    (MvPolynomial.isHomogeneous_X K k) Nat.zero_lt_one).preimage e
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨x, hxk⟩ : U)
  let p := (hU.primeIdealOf ⟨x, hxk⟩).asIdeal
  let : p.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxk⟩ hx
  let : IsLocalization.AtPrime (Y.presheaf.stalk x) p := hU.isLocalization_stalk ⟨x, hxk⟩
  let φ := projectivePullbackAffinePolynomialMap e k
  have hφ : Function.Surjective φ := projectivePullbackAffinePolynomialMap_surjective e k
  let ψ : MvPolynomial {j : Fin n // j ≠ k} K →+* Y.presheaf.stalk x :=
    (algebraMap Γ(Y, U) (Y.presheaf.stalk x)).comp φ
  obtain ⟨a, ha⟩ := polynomial_quotient_localization_maximalIdeal_generators
    (S := Y.presheaf.stalk x) φ hφ p
  have hmax : IsLocalRing.maximalIdeal (Y.presheaf.stalk x) =
      Ideal.span (Set.range fun i ↦ ψ (MvPolynomial.X i - MvPolynomial.C (a i))) := ha
  -- The residue field is K: every element is a constant modulo the maximal ideal.
  have hres : ∀ z : Y.presheaf.stalk x, ∃ c : K,
      z - ψ (MvPolynomial.C c) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
    intro z
    let eqv := IsLocalization.AtPrime.equivQuotMaximalIdeal p (Y.presheaf.stalk x)
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (eqv.symm (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) z))
    obtain ⟨P, rfl⟩ := hφ w
    have hz : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) z =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) (ψ P) := by
      have h1 : eqv (Ideal.Quotient.mk p (φ P)) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk x)) z := by
        rw [hw, AlgEquiv.apply_symm_apply]
      rw [← h1]
      have h2 := eqv.commutes (φ P)
      rw [Ideal.Quotient.algebraMap_eq] at h2
      rw [h2, IsScalarTower.algebraMap_apply Γ(Y, U) (Y.presheaf.stalk x),
        Ideal.Quotient.algebraMap_eq]
      rfl
    refine ⟨MvPolynomial.eval a P, ?_⟩
    have h3 : z - ψ P ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x) :=
      Ideal.Quotient.eq.mp hz
    have h4 : ψ P - ψ (MvPolynomial.C (MvPolynomial.eval a P)) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
      rw [← map_sub, hmax]
      have hmem := Ideal.mem_map_of_mem ψ (polynomial_eval_remainder_mem_linearIdeal a P)
      rw [Ideal.map_span, ← Set.range_comp] at hmem
      exact hmem
    have h5 := Ideal.add_mem _ h3 h4
    simpa only [sub_add_sub_cancel] using h5
  obtain ⟨P, hPdeg, hP⟩ := localJet_exists_polynomial ψ a hmax hres m y
  have hPD : P.totalDegree ≤ D := hPdeg.trans hmD
  refine ⟨projectiveHomogenize k D P, projectiveHomogenize_isHomogeneous k P hPD, ?_⟩
  have hgerm : Y.presheaf.germ U x hxk
      (projectivePullbackHomogeneousEquation e k D (projectiveHomogenize k D P)
        (projectiveHomogenize_isHomogeneous k P hPD)) = ψ P := by
    change algebraMap Γ(Y, U) (Y.presheaf.stalk x)
        (projectivePullbackHomogeneousEquation e k D (projectiveHomogenize k D P)
          (projectiveHomogenize_isHomogeneous k P hPD)) =
      algebraMap Γ(Y, U) (Y.presheaf.stalk x) (φ P)
    rw [← projectivePullbackAffinePolynomialMap_dehomogenize e k D _
      (projectiveHomogenize_isHomogeneous k P hPD), projectiveDehomogenize_homogenize]
  rw [hgerm]
  exact hP

end MixedFujita

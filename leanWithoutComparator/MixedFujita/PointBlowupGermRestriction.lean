/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupChartStalk
public import MixedFujita.LocalPointBlowupLeadingRestriction

/-!
Every actual point over the centre of the original scheme blow-up has an exceptional
coordinate map. Its actual exceptional stalk ideal and projection stalk map satisfy the
leading-form formula for every source germ. The m-th transform representative is unique.
The coordinate/filtration hypotheses are supplied here and constructed for smooth closed
points in the Cartier-section application.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {n : ℕ}

theorem stalkMapAtEq_comap_stalkIdeal {Y : Scheme.{u}} (I : X.IdealSheafData)
    (ρ : Y ⟶ X) (q : Y) (x : X) (hq : ρ q = x) :
    (I.comap ρ).stalkIdeal q = (I.stalkIdeal x).map (stalkMapAtEq ρ q x hq) := by
  subst x
  exact Scheme.IdealSheafData.stalkIdeal_comap I ρ q

theorem leadingJet_unique_exceptional {R B : Type u} [CommRing R] [Algebra K R]
    [IsLocalRing R] [CommRing B]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (β : R →+* B) (τ : MvPolynomial (Fin n) K →+* B) (k : Fin n)
    (hI : (IsLocalRing.maximalIdeal R).map β = Ideal.span {τ (MvPolynomial.X k)})
    (hcomp : ∀ g, β (ψ g) = τ (polynomialPointBlowupMap k g))
    (hreg : τ (MvPolynomial.X k) ∈ nonZeroDivisors B)
    (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    ∃! r : B, β s = τ (MvPolynomial.X k) ^ m * r ∧
      Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) r =
        pointBlowupExceptionalEvaluation τ k
          (projectiveDehomogenize K k (homogeneousTaylorForm m (T s))) := by
  obtain ⟨r, hr, hres⟩ := localLeadingJet_strictTransform_exceptional
    ψ T hX hord β τ k hI hcomp s m hs
  refine ⟨r, ⟨hr, hres⟩, ?_⟩
  intro r' hr'
  exact IsLeftRegular.pow m (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left
    (hr'.1.symm.trans hr)

set_option maxHeartbeats 1000000 in
theorem pointBlowup_germ_chart_data (x : X) [Algebra K (X.presheaf.stalk x)]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →+* (pointClosureIdeal x).blowUp.presheaf.stalk q),
      ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
        Ideal.span {τ (MvPolynomial.X k)} ∧
      τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
      ∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (ψ g) =
        τ (polynomialPointBlowupMap k g) := by
  obtain ⟨k, hk, p, hq', hp⟩ := pointBlowupLocalMap_exists_chart_over x
    (fun i => ψ (MvPolynomial.X i)) hmax q hq
  subst q
  let a : IsLocalRing.maximalIdeal (X.presheaf.stalk x) := ⟨ψ (MvPolynomial.X k), hk⟩
  let B : CommRingCat := (pointClosureIdeal x).blowUp.presheaf.stalk
    (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p))
  let ν : affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (ψ (MvPolynomial.X k)) →+* B := pointBlowupChartToStalk x a p
  have hψ : ∀ i, ψ (MvPolynomial.X i) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro i
    rw [hmax]
    exact Ideal.subset_span ⟨i, rfl⟩
  let τ := ν.comp (localPointBlowupPolynomialMap _ ψ hψ k)
  have hτ : τ (MvPolynomial.X k) = ν (algebraMap (X.presheaf.stalk x) _ a) := by
    change ν (localPointBlowupPolynomialMap _ ψ hψ k (MvPolynomial.X k)) = _
    rw [localPointBlowupPolynomialMap_X_self]
  have hreg : τ (MvPolynomial.X k) ∈ nonZeroDivisors _ := by
    rw [hτ]
    exact pointBlowupChartToStalk_exceptional_nonZeroDivisor x a p
  refine ⟨k, τ, ?_, hreg, ?_⟩
  · rw [hτ]
    exact pointBlowupChartToStalk_exceptionalIdeal x a p
  · intro g
    exact (pointBlowupChartToStalk_algebraMap x a p hp (ψ g)).symm.trans
      (congrArg ν (localPointBlowupPolynomialMap_substitution _ ψ hψ k g)).symm

set_option maxHeartbeats 500000 in
theorem pointBlowup_germs_exceptional_restriction (x : X) [Algebra K (X.presheaf.stalk x)]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder (X.presheaf.stalk x) r)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →+* (pointClosureIdeal x).blowUp.presheaf.stalk q),
      ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
        Ideal.span {τ (MvPolynomial.X k)} ∧
      τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
      (∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (ψ g) =
        τ (polynomialPointBlowupMap k g)) ∧
      ∀ (s : X.presheaf.stalk x) (m : ℕ), (m : ℕ∞) ≤ (T s).order →
        ∃! r : (pointClosureIdeal x).blowUp.presheaf.stalk q,
          stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq s = τ (MvPolynomial.X k) ^ m * r ∧
          Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) r =
            pointBlowupExceptionalEvaluation τ k
              (projectiveDehomogenize K k (homogeneousTaylorForm m (T s))) := by
  obtain ⟨k, τ, hE, hreg, hcomp⟩ := pointBlowup_germ_chart_data x ψ hmax q hq
  have hI : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
      (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq) = Ideal.span {τ (MvPolynomial.X k)} := by
    have h := stalkMapAtEq_comap_stalkIdeal (pointClosureIdeal x) (pointClosureIdeal x).blowUpπ q x hq
    rw [pointClosureIdeal_stalkIdeal_self] at h
    exact h.symm.trans hE
  exact ⟨k, τ, hE, hreg, hcomp, fun s m hs => leadingJet_unique_exceptional
    ψ T hX hord (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq) τ k hI hcomp hreg s m hs⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleDomainNormality
public import MixedFujita.EtaleChartTaylorCoordinates
public import MixedFujita.GenericSmoothCharts
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
Actual affine rings of étale charts on an integral scheme are integrally closed.
Localization at the point gives normality of its actual stalk. The smooth chart
cover therefore supplies normality, with no integral-closure hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open scoped nonZeroDivisors

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- An actual affine étale-chart ring is normal, via its generic fiber. -/
theorem etaleChart_isIntegrallyClosed (c : EtaleChart K X n) :
    IsIntegrallyClosed Γ(X, c.U) := by
  let := c.coords.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U) := etaleChart_coords_etale c
  exact etaleDomain_isIntegrallyClosed (R := MvPolynomial (Fin n) K)

/-- Normality of the actual stalk at every point in an étale chart. -/
theorem etaleChart_stalk_isIntegrallyClosed (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : c.U)
  have := c.isAffine.isLocalization_stalk (⟨x, hx⟩ : c.U)
  have := etaleChart_isIntegrallyClosed c
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- Smoothness of relative dimension n supplies normality of every actual stalk. -/
theorem smoothScheme_stalk_isIntegrallyClosed
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  have hx : x ∈ iSup (fun c : EtaleChart K X n => c.U) := by
    rw [etaleCharts_cover]
    trivial
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp hx
  exact etaleChart_stalk_isIntegrallyClosed c x hc

/-- General smoothness also supplies normality, without fixing a relative dimension. -/
theorem smooth_stalk_isIntegrallyClosed [Smooth (X ↘ Spec (CommRingCat.of K))] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  have hx : x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  obtain ⟨m, c, hc⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hx
  exact etaleChart_stalk_isIntegrallyClosed c x hc

end MixedFujita

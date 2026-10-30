/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleChartRelation

/-!
Normalizing an ample relation (step 10, R4-3).

* `projectiveHyperplaneCartier_eq_add_principal`: hyperplane divisors of two degree-one forms differ
  by the principal divisor of their ratio (the ratio is independent of the chart, so the local
  equations agree).
* `exists_eq_hyperplane_add_principal_normalize`: a relation
  `m' • (m (Q − K_T) − Σ a_k E_k) = H_g + div f` (with `K_T` the canonical divisor of a chart `c_T`)
  becomes `m' • (m (Q − div q − K_0) − Σ a_k E_k) = H_{X_{k₀}} + div f''` for any rational function `q`,
  any reference chart `c_0` of the canonical divisor and any coordinate `X_{k₀}` not vanishing at the
  generic point (`canonicalDivisor_change_reference`).

On `T_K` this puts the ample relation in the form of check 541, with `Q` shifted by its local
equation on the first chart (check 534).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- **Hyperplane divisors of two degree-one forms differ by the principal divisor of the ratio.** -/
theorem projectiveHyperplaneCartier_eq_add_principal {n : ℕ} {R : Type u} [CommRing R]
    {Y : Scheme.{u}} [IsIntegral Y] (e : Y ⟶ polynomialProjectiveScheme n R)
    (g g' : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1) (hg' : g'.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (hggen' : g' ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    projectiveHyperplaneCartier e g hg hggen = projectiveHyperplaneCartier e g' hg' hggen' +
      principalCartierDivisor Y
        (projectivePullbackHomogeneousRatio e j 1 g hg g' hg' Nat.one_pos hggen hggen') := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n R (e t)
  let j' : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k, ⟨⟨t, hk⟩⟩⟩
  refine ⟨projectiveHyperplaneUnit e g hg hggen j',
    projectiveHyperplane_isLocalEquationAt e g hg hggen j' t hk, ?_⟩
  have h := (projectiveHyperplane_isLocalEquationAt e g' hg' hggen' j' t hk).mul
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor t
      (projectivePullbackHomogeneousRatio e j 1 g hg g' hg' Nat.one_pos hggen hggen'))
  convert h using 1
  rw [projectivePullbackHomogeneousRatio_chart_independent e j j' 1 g hg g' hg' Nat.one_pos hggen
    hggen', projectivePullbackHomogeneousRatio, projectiveHyperplaneUnit, projectiveHyperplaneUnit,
    mul_comm, inv_mul_cancel_right]

/-- **Normalizing an ample relation**: shifting `Q` by a principal divisor, changing the reference
chart of the canonical divisor and replacing the hyperplane by a coordinate hyperplane. -/
theorem exists_eq_hyperplane_add_principal_normalize {K : Type u} [Field K] {Y : Scheme.{u}}
    [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] {d : ℕ}
    [SmoothOfRelativeDimension d (Y ↘ Spec (CommRingCat.of K))] {P : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme P K) (cT c₀ : EtaleChart K Y d)
    (hcover : iSup (fun c : EtaleChart K Y d => c.U) = ⊤) {r : ℕ} (E : Fin r → CartierDivisor Y)
    (Q : CartierDivisor Y) (m m' : ℕ) (a : Fin r → ℕ) (g : MvPolynomial (Fin P) K)
    (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (f : Y.functionFieldˣ)
    (heq : m' • (m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k) =
      projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y f)
    (q : Y.functionFieldˣ) (k₀ : Fin P)
    (hk₀ : MvPolynomial.X k₀ ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    ∃ f'' : Y.functionFieldˣ,
      m' • (m • (Q + principalCartierDivisor Y q⁻¹ - canonicalDivisor d c₀ hcover) -
          ∑ k, a k • E k) =
        projectiveHyperplaneCartier e (MvPolynomial.X k₀) (MvPolynomial.isHomogeneous_X K k₀) hk₀ +
          principalCartierDivisor Y f'' := by
  have hj : Nonempty (projectivePullbackCoordinateOpen e k₀) :=
    ⟨⟨genericPoint Y, (Proj.mem_basicOpen _ _ _).2 hk₀⟩⟩
  have hH := projectiveHyperplaneCartier_eq_add_principal e g (MvPolynomial.X k₀) hg
    (MvPolynomial.isHomogeneous_X K k₀) hggen hk₀ ⟨k₀, hj⟩
  refine ⟨f * projectivePullbackHomogeneousRatio e ⟨k₀, hj⟩ 1 g hg (MvPolynomial.X k₀)
    (MvPolynomial.isHomogeneous_X K k₀) Nat.one_pos hggen hk₀ *
      (etaleChartCanonicalEquation cT c₀ * q⁻¹) ^ (m * m'), ?_⟩
  have hK : smoothCanonicalDivisor cT = canonicalDivisor d c₀ hcover +
      principalCartierDivisor Y (etaleChartCanonicalEquation cT c₀) :=
    canonicalDivisor_change_reference c₀ cT hcover
  have h1 : m' • (m • (Q + principalCartierDivisor Y q⁻¹ - canonicalDivisor d c₀ hcover) -
      ∑ k, a k • E k) = m' • (m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k) +
        (m * m') • (principalCartierDivisor Y (etaleChartCanonicalEquation cT c₀) +
          principalCartierDivisor Y q⁻¹) := by
    rw [hK]
    module
  rw [h1, heq, hH, principalCartierDivisor_mul, principalCartierDivisor_mul,
    principalCartierDivisor_power, principalCartierDivisor_mul]
  module

end MixedFujita

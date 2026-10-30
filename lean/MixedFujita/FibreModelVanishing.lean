/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreAtlasVanishing
public import MixedFujita.FibreAmpleFromClosure

/-!
Vanishing on the closed fibre of a model (step 10, R4-7).

On the fibre `Y` over a finite field of an atlas `V_0, …, V_N` of `X` as in check 552, let `Q` be a
Cartier divisor whose local equations on the fibre charts are the germs of functions `u_i` on
`V_i ∩ V_0`, satisfying the relation of check 545 with the coordinate monomials, units, chart
equations and Jacobians. Then `m (Q − K_Y) − Σ_k a_k E_k` is ample (check 545), so with
`D = Q − K_Y`, whose local equations are those of `Q` divided by the canonical equations, check 552
gives `H^j(Y, 𝒪(Q)) = 0` for `j ≥ 1` (`subsingleton_cohomology_of_fibreModel`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra structureSectionsAlgebra sectionsRingModule
  Classical.propDecidable cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower sectionsBaseModule

universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))]
  [IsIntegral Y] {g : Y ⟶ X} [IsAffineHom g]
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  {n N : ℕ} {V : Fin (N + 1) → X.Opens} (hV : ∀ i, IsAffineOpen (V i))
  (y : ∀ i, MvPolynomial (Fin n) A →ₐ[A] Γ(X, V i)) (hy : ∀ i, (y i).toRingHom.FormallyEtale)
  (hne : ∀ i, Nonempty (g ⁻¹ᵁ V i))
  {V' : Fin (N + 1) → X.Opens} (hV' : ∀ i, IsAffineOpen (V' i)) (hV'V : ∀ i, V' i ≤ V i)
  (hne' : ∀ i, Nonempty (g ⁻¹ᵁ V' i))
  [Flat (X ↘ Spec (CommRingCat.of A))]

include h hV' hne' in
/-- **Vanishing on the closed fibre of a model**: for a divisor `Q` on the fibre whose local
equations satisfy the ampleness relation of check 545, `H^j(Y, 𝒪(Q)) = 0` for `j ≥ 1`. -/
theorem subsingleton_cohomology_of_fibreModel [Finite κ] [IsLocallyNoetherian Y]
    [∀ z : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (z : Y))]
    [IsProper (Y ↘ Spec (CommRingCat.of κ))] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hnorm : ∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z))
    {r : ℕ} (ξ : Fin r → Y) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (E : Fin r → CartierDivisor Y)
    (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint Y),
      cartierCoefficient (E k) (z : Y) = if (z : Y) = ξ k then 1 else 0)
    (hsnc : IsSNCFamily κ n ξ) (hcover : iSup (fun c : EtaleChart κ Y n => c.U) = ⊤)
    (hpn : n < p) (σs : Fin (N + 1) → Fin r → Option (Fin n))
    (hcs : ∀ i, IsSNCChart (fibreAtlasCharts κ H hV y hy hne i) ξ (σs i))
    (hcov : ⨆ i, (fibreAtlasCharts κ H hV y hy hne i).U = ⊤)
    (hunit : ∀ i, ∀ j ∈ logSetOf (σs i),
      IsUnit ((fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).coords
        (MvPolynomial.X j)))
    (hbd : ∀ a b (k : Fin r), ∃ w : Γ(X, V a ⊓ V b)ˣ,
      X.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op
          (componentSection (y a) (σs a) k) =
        (w : Γ(X, V a ⊓ V b)) * X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op
          (componentSection (y b) (σs b) k))
    (hVc : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen V x))
    (hV'c : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (haffY : ∀ q (x : Fin (q + 1) → Fin (N + 1)),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin (N + 1)),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (haffY' : ∀ q (x : Fin (q + 1) → Fin (N + 1)),
      IsAffineOpen (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    (hneY' : ∀ q (x : Fin (q + 1) → Fin (N + 1)),
      Nonempty (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    {P : ℕ} (ι : X ⟶ polynomialProjectiveScheme P A) (eY : Y ⟶ polynomialProjectiveScheme P κ)
    [IsClosedImmersion eY]
    (heY : eY ≫ polynomialProjectiveToBase P κ = Y ↘ Spec (CommRingCat.of κ))
    (heYk : ∀ k, projectivePullbackCoordinateOpen eY k = g ⁻¹ᵁ projectivePullbackCoordinateOpen ι k)
    (k₀ : Fin P)
    (heYeq : ∀ k, projectivePullbackHomogeneousEquation eY k 1 (MvPolynomial.X k₀)
        (MvPolynomial.isHomogeneous_X κ k₀) =
      g.appLE _ _ (heYk k).le (projectivePullbackHomogeneousEquation ι k 1 (MvPolynomial.X k₀)
        (MvPolynomial.isHomogeneous_X A k₀)))
    (kk : Fin (N + 1) → Fin P) (hk₀ : kk 0 = k₀)
    (hVk : ∀ i, V i ≤ projectivePullbackCoordinateOpen ι (kk i))
    {W : Fin (N + 1) → X.Opens} (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V i)
    (hWV₀ : ∀ i, W i ≤ V 0) [∀ i, Nonempty (g ⁻¹ᵁ W i)]
    (u : ∀ i, Γ(X, V i ⊓ V 0)) (w : ∀ i, Γ(X, V i)ˣ) (Q : CartierDivisor Y)
    (gQ : Fin (N + 1) → Y.functionFieldˣ)
    (hgQ : ∀ i, ∀ z ∈ (fibreAtlasCharts κ H hV y hy hne i).U, Q.IsLocalEquationAt z (gQ i))
    (hgQu : ∀ i, haveI : Nonempty (g ⁻¹ᵁ (V i ⊓ V 0)) := ⟨⟨(Classical.arbitrary (g ⁻¹ᵁ W i)).1,
        (Opens.map g.base).monotone (le_inf (hWV i) (hWV₀ i)) (Classical.arbitrary (g ⁻¹ᵁ W i)).2⟩⟩
      (gQ i : Y.functionField) = pullbackGerm g (V i ⊓ V 0) (u i))
    (m m' : ℕ) (hm : 1 ≤ m) (hm' : 1 ≤ m') (a : Fin r → ℕ) (ha : ∀ k, a k < m)
    (hrelA : ∀ i,
      (X.presheaf.map (homOfLE (le_inf (hWV i) (hWV₀ i))).op (u i)) ^ (m * m') *
          (X.presheaf.map (homOfLE (hWV₀ i)).op
            (∏ j ∈ logSetOf (σs 0), y 0 (MvPolynomial.X j) ^ logTwistExponent (σs 0) a j)) ^ m' *
          X.presheaf.map (homOfLE (hWV₀ i)).op (w 0 : Γ(X, V 0)) =
        X.presheaf.map (homOfLE (hWV i)).op (w i : Γ(X, V i)) *
          X.presheaf.map (homOfLE ((hWV i).trans (hVk i))).op
            (projectivePullbackHomogeneousEquation ι (kk i) 1 (MvPolynomial.X k₀)
              (MvPolynomial.isHomogeneous_X A k₀)) *
          ringJacobianOn (hV i) (hV 0) (hW i) (hWV i) (hWV₀ i) (y i) (y 0) (hy i) (hy 0) ^
            (m * m') *
          (X.presheaf.map (homOfLE (hWV i)).op
            (∏ j ∈ logSetOf (σs i), y i (MvPolynomial.X j) ^ logTwistExponent (σs i) a j)) ^ m')
    {j : ℕ} (hj : 1 ≤ j) : Subsingleton (Scheme.Modules.Cohomology Q.sheaf j) := by
  have hamp := fibre_cartierIsAmpleProj_of_closureRelation H hnorm ξ hinj hξ E hEc ι eY heY heYk
    k₀ heYeq hV kk hk₀ hVk y hy hne σs hcs hcov hcover hW hWV hWV₀ u w Q gQ hgQ hgQu m m' hm' a
    hrelA
  have hvan := canonical_vanishing_of_fibreAtlas p κ h H hV y hy hne hV' hV'V hne' hnorm ξ hinj hξ E
    hEc hsnc (fibreAtlasCharts κ H hV y hy hne 0) hcover hpn σs hcs hcov hunit hbd hVc hV'c haffY
    hneY haffY' hneY' (Q - canonicalDivisor n (fibreAtlasCharts κ H hV y hy hne 0) hcover)
    (fun i => gQ i * (etaleChartCanonicalEquation (fibreAtlasCharts κ H hV y hy hne 0)
      (fibreAtlasCharts κ H hV y hy hne i))⁻¹)
    (fun i z hz => by
      rw [sub_eq_add_neg]
      exact (hgQ i z hz).mul (canonicalDivisor_isLocalEquationAt _ hcover _ hz).inv)
    m hm a ha hamp hj
  rw [show canonicalDivisor n (fibreAtlasCharts κ H hV y hy hne 0) hcover +
      (Q - canonicalDivisor n (fibreAtlasCharts κ H hV y hy hne 0) hcover) = Q by abel] at hvan
  exact hvan

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreAtlasLiftData

/-!
Kawamata–Viehweg vanishing on the fibre of an atlas (step 10, R4-6).

Let `V_i` be an atlas of affine opens of `X` with étale coordinates and `V'_i ≤ V_i` smaller affine
opens as in check 551, whose fibre charts are simple normal crossing charts covering the fibre `Y`
over a finite field `κ` of characteristic `p > n`, with the logarithmic coordinates units on the
`V'_i` and the boundary relations of check 547 on the `V_a ∩ V_b`. The lifts of check 551 are lift
data for check 491. So if `m • D − Σ_k a_k • E_k` is ample with `0 ≤ a_k < m` and `D` has local
equations on the charts, then `H^j(Y, O(K_Y + D)) = 0` for `j ≥ 1`
(`canonical_vanishing_of_fibreAtlas`). The local equations of the `E_k` are the component equations
of the charts (check 547), and the étale coordinates of a chart are nonzero
(`etaleCoordFun_ne_zero`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule Classical.propDecidable
  cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower sectionsBaseModule

universe u

/-- **Étale coordinates are nonzero** on a nontrivial ring: their differentials form a basis. -/
theorem etaleCoordFun_ne_zero {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Nontrivial S]
    {n : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) (j : Fin n) :
    etaleCoordFun y j ≠ 0 := by
  intro h0
  apply (etaleCoordinateBasis y hy).ne_zero j
  rw [etaleCoordinateBasis_apply]
  change KaehlerDifferential.D K S (etaleCoordFun y j) = 0
  rw [h0, map_zero]

section Vanishing

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))]
  [IsIntegral Y] {g : Y ⟶ X} [IsAffineHom g]
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  {n N : ℕ} {V : Fin N → X.Opens} (hV : ∀ i, IsAffineOpen (V i))
  (y : ∀ i, MvPolynomial (Fin n) A →ₐ[A] Γ(X, V i)) (hy : ∀ i, (y i).toRingHom.FormallyEtale)
  (hne : ∀ i, Nonempty (g ⁻¹ᵁ V i))
  {V' : Fin N → X.Opens} (hV' : ∀ i, IsAffineOpen (V' i)) (hV'V : ∀ i, V' i ≤ V i)
  (hne' : ∀ i, Nonempty (g ⁻¹ᵁ V' i))
  [Flat (X ↘ Spec (CommRingCat.of A))]

include h hV' hne' in
/-- **Kawamata–Viehweg vanishing on the fibre of an atlas**: over a finite field of characteristic
`p > n`, with the atlas data of check 551, if `m • D − Σ_k a_k • E_k` is ample with `0 ≤ a_k < m`
then `H^j(O(K_Y + D)) = 0` for `j ≥ 1`. -/
theorem canonical_vanishing_of_fibreAtlas [Finite κ] [IsLocallyNoetherian Y]
    [∀ z : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (z : Y))]
    [IsProper (Y ↘ Spec (CommRingCat.of κ))] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (hnorm : ∀ z : Y, IsIntegrallyClosed (Y.presheaf.stalk z))
    {r : ℕ} (ξ : Fin r → Y) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (E : Fin r → CartierDivisor Y)
    (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint Y),
      cartierCoefficient (E k) (z : Y) = if (z : Y) = ξ k then 1 else 0)
    (hsnc : IsSNCFamily κ n ξ) (c₀ : EtaleChart κ Y n)
    (hcover : iSup (fun c : EtaleChart κ Y n => c.U) = ⊤) (hpn : n < p)
    (σs : Fin N → Fin r → Option (Fin n))
    (hcs : ∀ i, IsSNCChart (fibreAtlasCharts κ H hV y hy hne i) ξ (σs i))
    (hcov : ⨆ i, (fibreAtlasCharts κ H hV y hy hne i).U = ⊤)
    (hunit : ∀ i, ∀ j ∈ logSetOf (σs i),
      IsUnit ((fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).coords
        (MvPolynomial.X j)))
    (hrel : ∀ a b (k : Fin r), ∃ w : Γ(X, V a ⊓ V b)ˣ,
      X.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op
          (componentSection (y a) (σs a) k) =
        (w : Γ(X, V a ⊓ V b)) * X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op
          (componentSection (y b) (σs b) k))
    (hVc : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V x))
    (hV'c : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (haffY : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (haffY' : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    (hneY' : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    (D : CartierDivisor Y) (gD : Fin N → Y.functionFieldˣ)
    (hgD : ∀ i, ∀ z ∈ (fibreAtlasCharts κ H hV y hy hne i).U, D.IsLocalEquationAt z (gD i))
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (a : Fin r → ℕ) (ha : ∀ k, a k < m₀)
    (hamp : CartierIsAmpleProj κ (m₀ • D - ∑ k, a k • E k)) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + D).sheaf j) :=
  canonical_vanishing_of_logCechLifts (hnorm := hnorm) (ξ := ξ) (hinj := hinj) (hξ := hξ) (E := E)
    (hEc := hEc) (cs := fibreAtlasCharts κ H hV y hy hne) (σs := σs) (hcs := hcs) (haff := haffY)
    (hne := hneY) (cs' := fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') (haff' := haffY')
    (hne' := hneY') (hsub := fun i => (Opens.map g.base).monotone (hV'V i)) (hunit := hunit)
    (hcoords := fun _ t => etaleChartCoordinateRationalUnit_etaleChartRestrict _ _ _ _ _ t)
    (L := fun _ x => WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' x))
    (π := fun q x => fibreCechπ p κ h H V' x (hV'c q x))
    (hπ := fun q x => fibreCechπ_surjective p κ h H V' x (hV'c q x)) (p := p)
    (F := fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY')
    (hF := fibreAtlasπ_frobenius p κ h H hV y hy hV'V hV'c hneY')
    (hker := fun q x => fibreCechπ_exists_eq_p_mul p κ h H V' x (hV'c q x))
    (hΦ := fibreAtlas_hΦ p κ h H hV y hy hne hV' hV'V hne' hVc hV'c haffY hneY haffY' hneY' σs
      hunit hrel)
    (hH := fibreAtlas_hH p κ h H hV y hy hne hV' hV'V hne' hVc hV'c haffY hneY haffY' hneY' σs
      hunit hrel)
    (R := fun _ x k =>
      fibreWittRestrict p κ (TopCat.Presheaf.cechOpen_le_comp V' x (Fin.succAbove k)))
    (hR := fun q x k z => fibreCechπ_map p κ h H V' V' (x ∘ Fin.succAbove k) x (hV'c q _)
      (hV'c (q + 1) x) _ _ z)
    (hRF := fibreAtlasFrobenius_restrict p κ h H hV y hy hV'V hV'c hneY')
    (hann := fun q x z hz => fibreCechπ_eq_zero_of_p_mul_eq_zero p κ h H V' x (hV'c q x) z hz)
    (hp2 := fun _ _ => fibreWitt_p_mul_p p κ)
    (hK := exists_fibreAtlas_teichmuller p κ h H hV y hy hV'V hV'c hneY')
    (hft := fun q x => sectionsBaseOpen_finiteType (haffY' q x))
    (c₀ := c₀) (hcover := hcover) (hsnc := hsnc)
    (hΦ0 := fibreAtlas_hΦ0 p κ h H hV y hy hne hV' hV'V hne' hV'c haffY hneY haffY' hneY' σs
      hunit)
    (hy0 := fun q x t =>
      etaleCoordFun_ne_zero _ (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q
        x).formallyEtale t)
    (hftU := fun q x => sectionsBaseOpen_finiteType (haffY q x))
    hpn hcov D (fun _ x => gD (x 0))
    (fun _ x z hz => hgD (x 0) z (TopCat.Presheaf.cechOpen_le (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x 0
      hz))
    (fun k _ x => sncChartComponentEquation (fibreAtlasCharts κ H hV y hy hne (x 0)) (σs (x 0)) k)
    (fun k _ x z hz => sncChartComponentEquation_isLocalEquationAt hnorm ξ hinj hξ E hEc _
      (σs (x 0)) (hcs (x 0)) k z (TopCat.Presheaf.cechOpen_le (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x 0
      hz))
    m₀ hm₀ a ha hamp hj

end Vanishing

end MixedFujita

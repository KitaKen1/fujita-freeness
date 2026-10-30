/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreCechLifts
public import MixedFujita.LogHomotopyRegularity
public import MixedFujita.BoundaryRatioUnits
public import MixedFujita.LogCechDIComparison
public import MixedFujita.LogCechRestriction

/-!
The lift data of check 491 on the fibre of an atlas (step 10, R4-6).

Let `V_i` be affine opens of `X` with étale coordinates `y_i` and fibre charts `c_i` on `g⁻¹V_i`
(`fibreAtlasCharts`), and let `V'_i ≤ V_i` be affine opens whose fibre charts `c'_i`
(`fibreAtlasRestrictCharts`, the restrictions of the `c_i`) have the logarithmic coordinates as
units. On the lifts of the functions on the Čech intersections of `V'` take the vertex Frobenius
lifts of check 550 (`fibreAtlasFrobenius`). Then:
* `fibreAtlas_hΦ0`: the vertex-zero formula `Φ_{F_0}(θ'_i) = C₀(θ_i)` (check 520);
* `fibreAtlas_hH`: the homotopies `h_{F_jF_{j'}}(θ'_i)` are regular on the Čech intersections of the
  `c_i`, given units `w` on `V_a ∩ V_b` with `z_{a,k} = w z_{b,k}` for the component sections of
  check 547. Check 549 applies to the lifts on the Čech intersections of `V`: in a logarithmic
  direction `y_i = u z_j` on the fibre, and `z_j = w z_{j'}` holds exactly in the lifts
  (`exists_fibreAtlas_boundaryLifts`);
* `fibreAtlas_hΦ`: the Frobenius forms `Φ_{F_j}(θ'_i)` have regular logarithmic coefficients.
These are the hypotheses `hΦ0`, `hH` and `hΦ` of check 491.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule Classical.propDecidable
  cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

universe u

section Reduction

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))

omit [PerfectRing κ p] in
/-- The reduction of `1 ⊗ s` is the pullback of `s`. -/
theorem fibreCechπ_one_tmul {ι : Type*} (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x)) (s : Γ(X, TopCat.Presheaf.cechOpen U x)) :
    fibreCechπ p κ h H U x hU ((1 : WittTwo p κ) ⊗ₜ[A] s) =
      g.appLE (TopCat.Presheaf.cechOpen U x) (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x)
        (CohomologyAux.cechOpen_preimage g U x).le s := by
  change (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
    (fibreWittπ p κ h H hU ((1 : WittTwo p κ) ⊗ₜ[A] s)) = _
  rw [fibreWittπ_tmul, map_one, map_one, one_mul]
  exact appLE_restrict_apply (g := g) le_rfl _ s

end Reduction

section Atlas

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

/-- **The fibre charts of an atlas** on the preimages `g⁻¹V_i`. -/
noncomputable def fibreAtlasCharts (i : Fin N) : EtaleChart κ Y n :=
  fibreEtaleChart H (hV i) (y i) (hy i) (hne i)

/-- **The fibre charts restricted to the preimages of smaller opens** `V'_i ≤ V_i`. -/
noncomputable def fibreAtlasRestrictCharts (i : Fin N) : EtaleChart κ Y n :=
  etaleChartRestrict (fibreAtlasCharts κ H hV y hy hne i) (g ⁻¹ᵁ V' i) ((hV' i).preimage g)
    (hne' i) ((Opens.map g.base).monotone (hV'V i))

omit [IsIntegral Y] in
/-- The Čech intersections of the restricted charts lie in those of the charts. -/
theorem fibreAtlas_cechOpen_restrict_le {m : ℕ} (x : Fin m → Fin N) :
    TopCat.Presheaf.cechOpen (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U)
        x ≤
      TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x :=
  iInf_mono fun a => (Opens.map g.base).monotone (hV'V (x a))

omit [IsIntegral Y] in
/-- The coordinates of the Čech charts are the pullbacks of the coordinates of the first vertex. -/
theorem fibreAtlas_cechEtaleChart_coords_X
    (haffY : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (t : Fin n) :
    (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).coords (MvPolynomial.X t) =
      g.appLE (V (x 0)) (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U
        (TopCat.Presheaf.cechOpen_le (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x 0)
        (y (x 0) (MvPolynomial.X t)) := by
  change (Y.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le
      (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x 0)).op).hom
    ((fibreEtaleChart H (hV (x 0)) (y (x 0)) (hy (x 0)) (hne (x 0))).coords (MvPolynomial.X t)) = _
  rw [fibreEtaleChart_coords_X]
  exact appLE_restrict_apply (g := g) le_rfl _ _

omit [IsIntegral Y] in
/-- The coordinates of the Čech charts of the restricted charts. -/
theorem fibreAtlas_cechEtaleChart_restrict_coords_X
    (haffY' : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    (hneY' : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen
        (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (t : Fin n) :
    (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY' q x).coords
        (MvPolynomial.X t) =
      g.appLE (V (x 0))
        (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY' q x).U
        ((TopCat.Presheaf.cechOpen_le
          (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x 0).trans
          ((Opens.map g.base).monotone (hV'V (x 0))))
        (y (x 0) (MvPolynomial.X t)) := by
  change (Y.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le
      (fun i => (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).U) x 0)).op).hom
    ((Y.presheaf.map (homOfLE ((Opens.map g.base).monotone (hV'V (x 0)))).op).hom
      ((fibreEtaleChart H (hV (x 0)) (y (x 0)) (hy (x 0)) (hne (x 0))).coords
        (MvPolynomial.X t))) = _
  rw [fibreEtaleChart_coords_X, appLE_restrict_apply]
  exact appLE_restrict_apply (g := g) _ _ _

/-- **The vertex Frobenius lifts** on the lifts of the Čech intersections of `V'`. -/
noncomputable def fibreAtlasFrobenius
    (hV'c : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (hne'c : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ V' i) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (j : Fin (q + 1)) :
    WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' x) →+*
      WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' x) :=
  haveI := nontrivial_fibreCech κ H V' x (hV'c q x) (hne'c q x)
  fibreCechFrobenius p κ h V y hV hy V' hV'V x (hV'c q x) j

omit [IsIntegral Y] [IsAffineHom g] in
/-- The vertex Frobenius lifts lift the `p`-th power map (`hF`). -/
theorem fibreAtlasπ_frobenius
    (hV'c : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (hne'c : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ V' i) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (j : Fin (q + 1))
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' x)) :
    fibreCechπ p κ h H V' x (hV'c q x)
        (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hne'c q x j z) =
      fibreCechπ p κ h H V' x (hV'c q x) z ^ p := by
  have := nontrivial_fibreCech κ H V' x (hV'c q x) (hne'c q x)
  exact fibreCechπ_frobenius p κ h H V y hV hy V' hV'V x (hV'c q x) j z

omit [IsIntegral Y] [IsAffineHom g] in
/-- The vertex Frobenius lifts commute with restriction to faces (`hRF`). -/
theorem fibreAtlasFrobenius_restrict
    (hV'c : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (hne'c : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ V' i) x))
    (q : ℕ) (x : Fin (q + 2) → Fin N) (k : Fin (q + 2)) (j : Fin (q + 1))
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' (x ∘ Fin.succAbove k))) :
    fibreWittRestrict p κ (TopCat.Presheaf.cechOpen_le_comp V' x (Fin.succAbove k))
        (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hne'c q (x ∘ Fin.succAbove k) j z) =
      fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hne'c (q + 1) x (Fin.succAbove k j)
        (fibreWittRestrict p κ (TopCat.Presheaf.cechOpen_le_comp V' x (Fin.succAbove k)) z) := by
  have := nontrivial_fibreCech κ H V' x (hV'c (q + 1) x) (hne'c (q + 1) x)
  have := nontrivial_fibreCech κ H V' (x ∘ Fin.succAbove k) (hV'c q _) (hne'c q _)
  exact fibreCechFrobenius_restrict p κ h V y hV hy V' hV'V x (Fin.succAbove k) (hV'c (q + 1) x)
    (hV'c q _) j z

omit [IsIntegral Y] [IsAffineHom g] in
/-- The constants have lifts fixed by the vertex Frobenius lifts (`hK`). -/
theorem exists_fibreAtlas_teichmuller
    (hV'c : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V' x))
    (hne'c : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ V' i) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (k : κ) :
    ∃ k' : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V' x),
      fibreCechπ p κ h H V' x (hV'c q x) k' =
        algebraMap κ Γ(Y, TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ V' i) x) k ∧
      ∀ j, fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hne'c q x j k' = k' ^ p := by
  have := nontrivial_fibreCech κ H V' x (hV'c q x) (hne'c q x)
  exact exists_fibreCech_teichmuller p κ h H V y hV hy V' hV'V x (hV'c q x) k

/-- The reduction of the lifts on the Čech intersections of `V`, valued in the functions on the
Čech charts. -/
noncomputable def fibreAtlasπ
    (hVc : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V x))
    (haffY : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) :
    WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V x) →+*
      Γ(Y, (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U) :=
  fibreCechπ p κ h H V x (hVc q x)

omit [IsIntegral Y] [PerfectRing κ p] in
theorem fibreAtlasπ_one_tmul
    (hVc : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V x))
    (haffY : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (s : Γ(X, TopCat.Presheaf.cechOpen V x)) :
    fibreAtlasπ p κ h H hV y hy hne hVc haffY hneY q x ((1 : WittTwo p κ) ⊗ₜ[A] s) =
      g.appLE (TopCat.Presheaf.cechOpen V x)
        (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U
        (CohomologyAux.cechOpen_preimage g V x).le s :=
  fibreCechπ_one_tmul p κ h H V x (hVc q x) s

variable [Flat (X ↘ Spec (CommRingCat.of A))]

include hV' hne' in
/-- **The vertex-zero formula** `Φ_{F_0}(θ'_i) = C₀(θ_i)` on the fibre (`hΦ0` of check 491). -/
theorem fibreAtlas_hΦ0
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
    {r : ℕ} (σs : Fin N → Fin r → Option (Fin n))
    (hunit : ∀ i, ∀ j ∈ logSetOf (σs i),
      IsUnit ((fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).coords
        (MvPolynomial.X j)))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (i : Fin n) :
    KaehlerDifferential.map κ κ
        Γ(Y, (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
          q x).U) Y.functionField
        (frobeniusLiftOneFormAux
          (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
            q x).coords
          (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
            q x).formallyEtale
          (fibreCechπ p κ h H V' x (hV'c q x)) (fibreCechπ_surjective p κ h H V' x (hV'c q x)) p
          (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY' q x 0)
          (fibreAtlasπ_frobenius p κ h H hV y hy hV'V hV'c hneY' q x 0)
          (fibreCechπ_exists_eq_p_mul p κ h H V' x (hV'c q x))
          (localLogBasis (σs (x 0))
            (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
              q x)
            (cechEtaleChart_logUnit (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne')
              haffY' hneY' σs hunit q x) i)) =
      logCartierCoeff (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x)
          (σs (x 0)) p i •
        logChartBasis (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x)
          (σs (x 0)) i := by
  have := nontrivial_fibreCech κ H V' x (hV'c q x) (hneY' q x)
  refine map_frobeniusLiftOneFormAux_localLogBasis _ (σs (x 0)) _ _ _ _ p _ _ _
    (fibreCechπ_eq_zero_of_p_mul_eq_zero p κ h H V' x (hV'c q x)) (fibreWitt_p_mul_p p κ) ?_
    (cechEtaleChart_coords_eq (fibreAtlasCharts κ H hV y hy hne)
      (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY hneY haffY' hneY'
      (fun i j => etaleChartCoordinateRationalUnit_etaleChartRestrict _ _ _ _ _ j) q x) i
  intro t
  refine ⟨(1 : WittTwo p κ) ⊗ₜ[A] fibreCechCoordinates V y V' hV'V x 0 (MvPolynomial.X t), ?_,
    fibreCechFrobenius_coordinate p κ h V y hV hy V' hV'V x (hV'c q x) 0 t⟩
  refine (fibreCechπ_one_tmul p κ h H V' x (hV'c q x) _).trans ?_
  rw [fibreCechCoordinates_X, appLE_of_restrict_apply]
  exact (fibreAtlas_cechEtaleChart_restrict_coords_X κ H hV y hy hne hV' hV'V hne' haffY' hneY' q x
    t).symm

omit [IsIntegral Y] [Flat (X ↘ Spec (CommRingCat.of A))] in
/-- **Lifts of the boundary relations**: in a logarithmic direction `i` of the first vertex,
`y_i = u z_j` on the fibre and `Z_j = W Z_{j'}` in the lifts on the Čech intersection of `V`, with
`F_j Z_j = Z_j^p`, `F_{j'} Z_{j'} = Z_{j'}^p` and `π W` a unit. -/
theorem exists_fibreAtlas_boundaryLifts
    (hVc : ∀ q (x : Fin (q + 1) → Fin N), IsAffineOpen (TopCat.Presheaf.cechOpen V x))
    (haffY : ∀ q (x : Fin (q + 1) → Fin N),
      IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    (hneY : ∀ q (x : Fin (q + 1) → Fin N),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x))
    {r : ℕ} (σs : Fin N → Fin r → Option (Fin n))
    (hrel : ∀ a b (k : Fin r), ∃ w : Γ(X, V a ⊓ V b)ˣ,
      X.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op
          (componentSection (y a) (σs a) k) =
        (w : Γ(X, V a ⊓ V b)) * X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op
          (componentSection (y b) (σs b) k))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (j j' : Fin (q + 1)) (i : Fin n)
    (hi : i ∈ logSetOf (σs (x 0))) :
    haveI := nontrivial_fibreCech κ H V x (hVc q x) (hneY q x)
    ∃ (u : Γ(Y, (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U)ˣ)
      (Z Z' W : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen V x)),
      (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).coords
          (MvPolynomial.X i) = u * fibreAtlasπ p κ h H hV y hy hne hVc haffY hneY q x Z ∧
        Z = W * Z' ∧
        fibreCechFrobenius p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) j Z = Z ^ p ∧
        fibreCechFrobenius p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) j' Z' = Z' ^ p ∧
        IsUnit (fibreAtlasπ p κ h H hV y hy hne hVc haffY hneY q x W) := by
  have := nontrivial_fibreCech κ H V x (hVc q x) (hneY q x)
  obtain ⟨k, hk⟩ := (mem_logSetOf (σs (x 0)) i).mp hi
  obtain ⟨w₁, hw₁⟩ := hrel (x 0) (x j) k
  obtain ⟨w₂, hw₂⟩ := hrel (x j) (x j') k
  have e₀ : (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U ≤
      g ⁻¹ᵁ (V (x 0) ⊓ V (x j)) :=
    (le_inf (TopCat.Presheaf.cechOpen_le (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x 0)
      (TopCat.Presheaf.cechOpen_le (fun i => (fibreAtlasCharts κ H hV y hy hne i).U) x j) :
      (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U ≤
        g ⁻¹ᵁ V (x 0) ⊓ g ⁻¹ᵁ V (x j))
  have e₁ : TopCat.Presheaf.cechOpen V x ≤ V (x j) ⊓ V (x j') :=
    le_inf (TopCat.Presheaf.cechOpen_le V x j) (TopCat.Presheaf.cechOpen_le V x j')
  -- the Frobenius lifts fix the component sections of their own vertex
  have hfix : ∀ b : Fin (q + 1),
      fibreCechFrobenius p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) b
          ((1 : WittTwo p κ) ⊗ₜ[A] X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le V x b)).op
            (componentSection (y (x b)) (σs (x b)) k)) =
        ((1 : WittTwo p κ) ⊗ₜ[A] X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le V x b)).op
          (componentSection (y (x b)) (σs (x b)) k)) ^ p := by
    intro b
    rcases hσ : σs (x b) k with _ | t
    · simp only [componentSection, hσ, Option.elim, map_one, ← Algebra.TensorProduct.one_def,
        one_pow]
    · simp only [componentSection, hσ, Option.elim]
      exact fibreCechFrobenius_coordinate p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) b t
  refine ⟨Units.map (g.appLE (V (x 0) ⊓ V (x j))
      (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x).U e₀).hom.toMonoidHom w₁,
    (1 : WittTwo p κ) ⊗ₜ[A] X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le V x j)).op
      (componentSection (y (x j)) (σs (x j)) k),
    (1 : WittTwo p κ) ⊗ₜ[A] X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le V x j')).op
      (componentSection (y (x j')) (σs (x j')) k),
    (1 : WittTwo p κ) ⊗ₜ[A] X.presheaf.map (homOfLE e₁).op (w₂ : Γ(X, V (x j) ⊓ V (x j'))),
    ?_, ?_, hfix j, hfix j', ?_⟩
  · -- the relation on the fibre
    have hcs0 : componentSection (y (x 0)) (σs (x 0)) k = y (x 0) (MvPolynomial.X i) := by
      rw [componentSection, hk]
      rfl
    rw [fibreAtlas_cechEtaleChart_coords_X, ← hcs0, ← appLE_of_restrict_apply e₀ inf_le_left, hw₁,
      map_mul, fibreAtlasπ_one_tmul, appLE_of_restrict_apply, appLE_of_restrict_apply]
    rfl
  · -- the exact relation in the lifts
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    have h2 := congrArg (fun s => X.presheaf.map (homOfLE e₁).op s) hw₂
    simp only [map_mul] at h2
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp] at h2
    exact h2
  · rw [fibreAtlasπ_one_tmul]
    exact (w₂.isUnit.map (X.presheaf.map (homOfLE e₁).op).hom).map _

include hV' hne' in
/-- **The homotopies on the logarithmic basis are regular** on the Čech intersections of the
charts (`hH` of check 491). -/
theorem fibreAtlas_hH
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
    {r : ℕ} (σs : Fin N → Fin r → Option (Fin n))
    (hunit : ∀ i, ∀ j ∈ logSetOf (σs i),
      IsUnit ((fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).coords
        (MvPolynomial.X j)))
    (hrel : ∀ a b (k : Fin r), ∃ w : Γ(X, V a ⊓ V b)ˣ,
      X.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op
          (componentSection (y a) (σs a) k) =
        (w : Γ(X, V a ⊓ V b)) * X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op
          (componentSection (y b) (σs b) k))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (j j' : Fin (q + 1)) (i : Fin n) :
    algebraMap Γ(Y, (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY'
        hneY' q x).U) Y.functionField
      (frobeniusLiftHomotopyAux
        (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
          q x).coords
        (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
          q x).formallyEtale
        (fibreCechπ p κ h H V' x (hV'c q x)) (fibreCechπ_surjective p κ h H V' x (hV'c q x)) p
        (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY' q x j)
        (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY' q x j')
        (fibreAtlasπ_frobenius p κ h H hV y hy hV'V hV'c hneY' q x j)
        (fibreAtlasπ_frobenius p κ h H hV y hy hV'V hV'c hneY' q x j')
        (fibreCechπ_exists_eq_p_mul p κ h H V' x (hV'c q x))
        (localLogBasis (σs (x 0))
          (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
            q x)
          (cechEtaleChart_logUnit (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne')
            haffY' hneY' σs hunit q x) i)) ∈
      chartRegularFunctions (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x) := by
  have := nontrivial_fibreCech κ H V x (hVc q x) (hneY q x)
  have := nontrivial_fibreCech κ H V' x (hV'c q x) (hneY' q x)
  have hle : TopCat.Presheaf.cechOpen V' x ≤ TopCat.Presheaf.cechOpen V x :=
    iInf_mono fun a => hV'V (x a)
  refine algebraMap_frobeniusLiftHomotopyAux_localLogBasis_mem
    (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x)
    (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY' q x)
    (fibreAtlas_cechOpen_restrict_le κ H hV y hy hne hV' hV'V hne' x) ?_ (σs (x 0)) _
    (fibreAtlasπ p κ h H hV y hy hne hVc haffY hneY q x)
    (fibreCechπ_surjective p κ h H V x (hVc q x)) _ _ p
    (fibreCechFrobenius p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) j)
    (fibreCechFrobenius p κ h V y hV hy V (fun _ => le_rfl) x (hVc q x) j')
    (fibreCechπ_frobenius p κ h H V y hV hy V (fun _ => le_rfl) x (hVc q x) j)
    (fibreCechπ_frobenius p κ h H V y hV hy V (fun _ => le_rfl) x (hVc q x) j')
    _ _ _ _ (fibreCechπ_exists_eq_p_mul p κ h H V x (hVc q x)) _
    (fibreCechπ_eq_zero_of_p_mul_eq_zero p κ h H V x (hVc q x))
    (fibreCechπ_eq_zero_of_p_mul_eq_zero p κ h H V' x (hV'c q x))
    (fibreWitt_p_mul_p p κ) (fibreWittRestrict p κ hle)
    (fun z => fibreCechπ_map p κ h H V V' x x (hVc q x) (hV'c q x) hle _ z)
    (fun z => fibreCechFrobenius_mono p κ h V y hV hy V (fun _ => le_rfl) V' hV'V x (hVc q x)
      (hV'c q x) hle j z)
    (fun z => fibreCechFrobenius_mono p κ h V y hV hy V (fun _ => le_rfl) V' hV'V x (hVc q x)
      (hV'c q x) hle j' z)
    (fun i hi => exists_fibreAtlas_boundaryLifts p κ h H hV y hy hne hVc haffY hneY σs hrel q x j
      j' i hi) i
  intro t
  rw [fibreAtlas_cechEtaleChart_restrict_coords_X, fibreAtlas_cechEtaleChart_coords_X]
  exact (appLE_restrict_apply (g := g) _ _ _).symm

include hV' hne' in
/-- **The Frobenius forms have regular logarithmic coefficients** on the Čech intersections of
the charts (`hΦ` of check 491). -/
theorem fibreAtlas_hΦ
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
    {r : ℕ} (σs : Fin N → Fin r → Option (Fin n))
    (hunit : ∀ i, ∀ j ∈ logSetOf (σs i),
      IsUnit ((fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne' i).coords
        (MvPolynomial.X j)))
    (hrel : ∀ a b (k : Fin r), ∃ w : Γ(X, V a ⊓ V b)ˣ,
      X.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op
          (componentSection (y a) (σs a) k) =
        (w : Γ(X, V a ⊓ V b)) * X.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op
          (componentSection (y b) (σs b) k))
    (q : ℕ) (x : Fin (q + 1) → Fin N) (j : Fin (q + 1)) (i t : Fin n) :
    (logChartBasis (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x)
        (σs (x 0))).repr
      (KaehlerDifferential.map κ κ
        Γ(Y, (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
          q x).U) Y.functionField
        (frobeniusLiftOneFormAux
          (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
            q x).coords
          (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
            q x).formallyEtale
          (fibreCechπ p κ h H V' x (hV'c q x)) (fibreCechπ_surjective p κ h H V' x (hV'c q x)) p
          (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY' q x j)
          (fibreAtlasπ_frobenius p κ h H hV y hy hV'V hV'c hneY' q x j)
          (fibreCechπ_exists_eq_p_mul p κ h H V' x (hV'c q x))
          (localLogBasis (σs (x 0))
            (cechEtaleChart (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne') haffY' hneY'
              q x)
            (cechEtaleChart_logUnit (fibreAtlasRestrictCharts κ H hV y hy hne hV' hV'V hne')
              haffY' hneY' σs hunit q x) i))) t ∈
      chartRegularFunctions (cechEtaleChart (fibreAtlasCharts κ H hV y hy hne) haffY hneY q x) :=
  logChartBasis_repr_frobeniusLiftOneFormAux_mem _ _ (σs (x 0)) _ _ _ p
    (fibreAtlasFrobenius p κ h H hV y hy hV'V hV'c hneY' q x 0) _ _ _ _
    (fibreCechπ_eq_zero_of_p_mul_eq_zero p κ h H V' x (hV'c q x)) (fibreWitt_p_mul_p p κ) i
    (fibreAtlas_hΦ0 p κ h H hV y hy hne hV' hV'V hne' hV'c haffY hneY haffY' hneY' σs hunit q x i)
    (fibreAtlas_hH p κ h H hV y hy hne hV' hV'V hne' hVc hV'c haffY hneY haffY' hneY' σs hunit hrel
      q x 0 j i) t

end Atlas

end MixedFujita

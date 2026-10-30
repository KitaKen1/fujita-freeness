/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogCechRestriction

/-!
The logarithmic Deligne–Illusie components on Čech cochains (step 10, R2).

Let `cs` be a cover by simple normal crossing charts and `cs'` a cover by smaller charts
`(cs' i).U ⊆ (cs i).U` with the same coordinates in `K(X)`, on which the logarithmic coordinates of
`cs i` are units (away from the boundary). Take lift data on the Čech intersections of `cs'`, as in
check 466. A logarithmic Čech cochain `y` of `Ω^b(log E)(M)` on `cs` restricts to a Čech cochain
`ρ y` of `Ω^b(M)` on `cs'` (check 488), and check 466 gives the components
`Ψ'_{b → i}(ρ y)` with values in `Ω^i(p • M)`.

If the lift data have regular logarithmic coefficients (the hypotheses of check 484), the rational
values of `Ψ'_{b → i}(ρ y)` are logarithmic with poles bounded by `p • M + Σ_k r_k • E_k` at every
point of the larger intersections. They define the logarithmic components
`Ψ_{b → i}(y)` (`logCechDIComponent`), with the rational values of `Ψ'_{b → i}(ρ y)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower sectionsBaseModule

section Charts

variable {N : ℕ} (cs cs' : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (haff' : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  (hne' : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  {r : ℕ} (σs : Fin N → Fin r → Option (Fin n))
  (hunit : ∀ i, ∀ j ∈ logSetOf (σs i), IsUnit ((cs' i).coords (MvPolynomial.X j)))
  (hcoords : ∀ i j, etaleChartCoordinateRationalUnit (cs' i) j =
    etaleChartCoordinateRationalUnit (cs i) j)

omit [IsIntegral X] in
include hunit in
/-- The logarithmic coordinates of the first chart are units on the Čech intersections of the
smaller cover. -/
theorem cechEtaleChart_logUnit (q : ℕ) (x : Fin (q + 1) → Fin N) :
    ∀ j ∈ logSetOf (σs (x 0)),
      IsUnit ((cechEtaleChart cs' haff' hne' q x).coords (MvPolynomial.X j)) :=
  fun j hj => (hunit (x 0) j hj).map
    (sectionRestrict K (TopCat.Presheaf.cechOpen_le (fun i => (cs' i).U) x 0))

include hcoords in
/-- **The Čech charts of the two covers have the same coordinates in `K(X)`.** -/
theorem cechEtaleChart_coords_eq (q : ℕ) (x : Fin (q + 1) → Fin N) (j : Fin n) :
    sectionGermAlgHom (K := K) (cechEtaleChart cs' haff' hne' q x).U
        ((cechEtaleChart cs' haff' hne' q x).coords (MvPolynomial.X j)) =
      (etaleChartCoordinateRationalUnit (cechEtaleChart cs haff hne q x) j : X.functionField) := by
  have h1 : etaleChartCoordinateRationalUnit (cechEtaleChart cs haff hne q x) j =
      etaleChartCoordinateRationalUnit (cs (x 0)) j :=
    etaleChartCoordinateRationalUnit_etaleChartRestrict (cs (x 0)) _ _ _ _ j
  have h2 : etaleChartCoordinateRationalUnit (cechEtaleChart cs' haff' hne' q x) j =
      etaleChartCoordinateRationalUnit (cs' (x 0)) j :=
    etaleChartCoordinateRationalUnit_etaleChartRestrict (cs' (x 0)) _ _ _ _ j
  calc sectionGermAlgHom (K := K) (cechEtaleChart cs' haff' hne' q x).U
        ((cechEtaleChart cs' haff' hne' q x).coords (MvPolynomial.X j)) =
        (etaleChartCoordinateRationalUnit (cechEtaleChart cs' haff' hne' q x) j :
          X.functionField) := rfl
    _ = _ := by rw [h2, hcoords, h1]

include hunit hcoords in
/-- The logarithmic coordinates are units in the local rings of the points of the smaller
charts. -/
theorem logUnit_stalk (i : Fin N) (z : X) (hz : z ∈ (cs' i).U) (j : Fin n)
    (hj : j ∈ logSetOf (σs i)) :
    ∃ u : (X.presheaf.stalk z)ˣ, algebraMap (X.presheaf.stalk z) X.functionField
      (u : X.presheaf.stalk z) = (etaleChartCoordinateRationalUnit (cs i) j : X.functionField) := by
  refine ⟨Units.map (X.presheaf.germ (cs' i).U z hz).hom.toMonoidHom (hunit i j hj).unit, ?_⟩
  rw [Units.coe_map, IsUnit.unit_spec]
  change algebraMap _ _ ((X.presheaf.germ (cs' i).U z hz).hom ((cs' i).coords (MvPolynomial.X j))) =
    _
  have := (cs' i).nonempty
  rw [Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := (cs' i).U) hz, ← hcoords i j]
  rfl

end Charts

section Twist

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
/-- The component equations of a simple normal crossing chart are regular on the chart. -/
theorem sncChartComponentEquation_mem_stalkFunctions (c : EtaleChart K X n)
    (σ : Fin r → Option (Fin n)) (w : X) (hw : w ∈ c.U) (k : Fin r) :
    (sncChartComponentEquation c σ k : X.functionField) ∈ stalkFunctions w := by
  rw [sncChartComponentEquation]
  cases σ k with
  | none => exact ⟨1, by rw [Option.elim_none, Units.val_one, map_one]⟩
  | some j =>
    refine ⟨X.presheaf.germ c.U w hw (c.coords (MvPolynomial.X j)), ?_⟩
    rw [Option.elim_some, etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
    have := c.nonempty
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hw _

include hnorm hinj hξ hEc in
/-- **Logarithmic forms with poles bounded by `p • M` have poles bounded by
`p • M + Σ_k r_k • E_k`**, at a point of a simple normal crossing chart. -/
theorem smul_mem_logFormsLattice_logTwist (c : EtaleChart K X n) (σ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (w : X) (hw : w ∈ c.U) (p : ℕ) (M : CartierDivisor X)
    (rr : Fin r → ℕ) {g : X.functionFieldˣ} (hg : M.IsLocalEquationAt w g) {f : X.functionFieldˣ}
    (hf : (p • M + ∑ k, rr k • E k).IsLocalEquationAt w f) {b : ℕ} (v : RationalForms K X b)
    (hv : (g : X.functionField) ^ p • v ∈ logFormsLattice K E w b) :
    (f : X.functionField) • v ∈ logFormsLattice K E w b := by
  choose h hh u hu using fun k =>
    exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation hnorm ξ hinj hξ E hEc c σ hc w
      hw k
  have hf₀ := isLocalEquationAt_logTwist E p M rr hg hh
  rw [smul_mem_logFormsLattice_iff_of_isLocalEquationAt E hf hf₀]
  have hreg : ∀ k, ((h k : X.functionFieldˣ) : X.functionField) ∈ stalkFunctions w := fun k => by
    rw [hu k]
    exact Subring.mul_mem _ ⟨_, rfl⟩ (sncChartComponentEquation_mem_stalkFunctions c σ w hw k)
  have hprod : ((∏ k, h k ^ rr k : X.functionFieldˣ) : X.functionField) ∈ stalkFunctions w := by
    rw [Units.coe_prod]
    exact Subring.prod_mem _ fun k _ => by
      rw [Units.val_pow_eq_pow_val]
      exact Subring.pow_mem _ (hreg k) _
  obtain ⟨s, hs⟩ := hprod
  rw [Units.val_mul, mul_comm, mul_smul, ← hs, algebraMap_smul, Units.val_pow_eq_pow_val]
  exact Submodule.smul_mem _ s hv

end Twist

section Lift

variable {r : ℕ} (E : Fin r → CartierDivisor X)
  {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (𝒰' : Fin N → X.Opens)
  (hne' : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰' x))

/-- **A Čech cochain of `Ω^i(N')` on the smaller cover whose rational values are logarithmic with
poles bounded by `N` on the larger intersections**, as a logarithmic Čech cochain. -/
noncomputable def logCechLift (N' Nt : CartierDivisor X) (i q : ℕ)
    (z : TopCat.Presheaf.CechCochain 𝒰' (twistedFormsSheaf K N' i).presheaf q)
    (hz : ∀ x, ∀ w ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x, ∀ f : X.functionFieldˣ,
      Nt.IsLocalEquationAt w f →
        (f : X.functionField) • cechRationalValue K (twistedFormsSubmodule K N' i) 𝒰' hne' q z x ∈
          logFormsLattice K E w i) :
    TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E Nt i).presheaf q := fun x =>
  haveI := hne q x
  ⟨(rationalFormsSectionsEquiv K i (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)).symm
      (cechRationalValue K (twistedFormsSubmodule K N' i) 𝒰' hne' q z x), fun w hw f hf => by
    rw [AddEquiv.apply_symm_apply]
    exact hz x w hw f hf⟩

theorem cechRationalValue_logCechLift (N' Nt : CartierDivisor X) (i q : ℕ)
    (z : TopCat.Presheaf.CechCochain 𝒰' (twistedFormsSheaf K N' i).presheaf q)
    (hz : ∀ x, ∀ w ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x, ∀ f : X.functionFieldˣ,
      Nt.IsLocalEquationAt w f →
        (f : X.functionField) • cechRationalValue K (twistedFormsSubmodule K N' i) 𝒰' hne' q z x ∈
          logFormsLattice K E w i) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (logFormsSubmodule K E Nt i) (fun i => (cs i).U) hne q
        (logCechLift E cs hne 𝒰' hne' N' Nt i q z hz) x =
      cechRationalValue K (twistedFormsSubmodule K N' i) 𝒰' hne' q z x := by
  have := hne q x
  exact AddEquiv.apply_symm_apply _ _

end Lift


section CechValues

variable {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (L : ∀ q, (Fin (q + 1) → Fin N) → Type u) [∀ q x, CommRing (L q x)]
  (π : ∀ q x, L q x →+* Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hπ : ∀ q x, Function.Surjective (π q x)) (p : ℕ) [Fact p.Prime] [CharP K p]
  (F : ∀ q x, Fin (q + 1) → (L q x →+* L q x)) (hF : ∀ q x k y, π q x (F q x k y) = π q x y ^ p)
  (hker : ∀ q x y, π q x y = 0 → ∃ z, y = (p : L q x) * z)
  {M : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x, M.IsLocalEquationAt y (g q x))

theorem cechRationalValue_apply {b : ℕ} (S : (rationalFormsSheaf K X b).Submodule) {N : ℕ}
    (𝒰 : Fin N → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x)) (q : ℕ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K S 𝒰 hne q y x =
      haveI := hne q x
      rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰 x) (y x).1 := rfl


theorem cechRationalValue_cechD_log {r : ℕ} (E : Fin r → CartierDivisor X) (N : CartierDivisor X)
    (b : ℕ) {N' : ℕ} (𝒰 : Fin N' → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N'), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x)) (q : ℕ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (logFormsSheaf K E N b).presheaf q)
    (x : Fin (q + 2) → Fin N') :
    cechRationalValue K (logFormsSubmodule K E N b) 𝒰 hne (q + 1)
        (TopCat.Presheaf.cechD 𝒰 (logFormsSheaf K E N b).presheaf q y) x =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        cechRationalValue K (logFormsSubmodule K E N b) 𝒰 hne q y (x ∘ Fin.succAbove k) :=
  cechRationalValue_cechD (logFormsSubmodule K E N b) 𝒰 hne q y x

theorem cechRationalValue_cechD_twisted (D : CartierDivisor X) (b : ℕ) {N' : ℕ}
    (𝒰 : Fin N' → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N'), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x)) (q : ℕ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q + 2) → Fin N') :
    cechRationalValue K (twistedFormsSubmodule K D b) 𝒰 hne (q + 1)
        (TopCat.Presheaf.cechD 𝒰 (twistedFormsSheaf K D b).presheaf q y) x =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        cechRationalValue K (twistedFormsSubmodule K D b) 𝒰 hne q y (x ∘ Fin.succAbove k) :=
  cechRationalValue_cechD (twistedFormsSubmodule K D b) 𝒰 hne q y x

/-- The rational value of an integer multiple of a section of `Ω^i(D)`. -/
theorem rationalFormsSectionsEquiv_twistedForms_zsmul (D : CartierDivisor X) (i : ℕ) (U : X.Opens)
    [Nonempty U] (k : ℤ) (Θ : twistedFormsSections K D i U) :
    rationalFormsSectionsEquiv K i U (k • Θ).1 = k • rationalFormsSectionsEquiv K i U Θ.1 := by
  rw [← map_zsmul]
  rfl

/-- **The rational values of the Čech Deligne–Illusie map** of check 464. -/
theorem cechRationalValue_cechDIMap (b i a : ℕ) (hi : i + a = b) (q q' : ℕ) (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K M b).presheaf q)
    (x : Fin (q' + 1) → Fin N) :
    cechRationalValue K (twistedFormsSubmodule K (p • M) i) (fun i => (cs i).U) hne q'
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b i a hi q q' hq y) x =
      haveI := hne q' x
      (-1 : ℤ) ^ (a * q) • rationalFormsSectionsEquiv K i
        (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
        (twistedChartDIComponent (cechEtaleChart cs haff hne q' x) (π q' x) (hπ q' x) p (F q' x)
          (hF q' x) (hker q' x) (hg q' x) b i a hi (cechFront q')
          ((twistedFormsSheaf K M b).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp _ x
            (cechBack a q q' hq))).op (y (x ∘ cechBack a q q' hq)))).1 := by
  have := hne q' x
  rw [cechRationalValue_apply, cechDIMap_apply, rationalFormsSectionsEquiv_twistedForms_zsmul]

end CechValues

section Components

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  {N : ℕ} (cs : Fin N → EtaleChart K X n) (σs : Fin N → Fin r → Option (Fin n))
  (hcs : ∀ i, IsSNCChart (cs i) ξ (σs i))
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (cs' : Fin N → EtaleChart K X n)
  (haff' : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  (hne' : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  (hsub : ∀ i, (cs' i).U ≤ (cs i).U)
  (hunit : ∀ i, ∀ j ∈ logSetOf (σs i), IsUnit ((cs' i).coords (MvPolynomial.X j)))
  (hcoords : ∀ i j, etaleChartCoordinateRationalUnit (cs' i) j =
    etaleChartCoordinateRationalUnit (cs i) j)
  (L : ∀ q, (Fin (q + 1) → Fin N) → Type u) [∀ q x, CommRing (L q x)]
  (π : ∀ q x, L q x →+* Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  (hπ : ∀ q x, Function.Surjective (π q x)) (p : ℕ) [Fact p.Prime] [CharP K p]
  (F : ∀ q x, Fin (q + 1) → (L q x →+* L q x)) (hF : ∀ q x k y, π q x (F q x k y) = π q x y ^ p)
  (hker : ∀ q x y, π q x y = 0 → ∃ z, y = (p : L q x) * z)
  (hΦ : ∀ q (x : Fin (q + 1) → Fin N) (j : Fin (q + 1)) (i t : Fin n),
    (logChartBasis (cechEtaleChart cs haff hne q x) (σs (x 0))).repr
      (KaehlerDifferential.map K K Γ(X, (cechEtaleChart cs' haff' hne' q x).U) X.functionField
        (frobeniusLiftOneFormAux (cechEtaleChart cs' haff' hne' q x).coords (cechEtaleChart cs' haff' hne' q x).formallyEtale (π q x) (hπ q x) p
          (F q x j) (hF q x j) (hker q x)
          (localLogBasis (σs (x 0)) (cechEtaleChart cs' haff' hne' q x) (cechEtaleChart_logUnit cs' haff' hne' σs hunit q x)
            i))) t ∈ chartRegularFunctions (cechEtaleChart cs haff hne q x))
  (hH : ∀ q (x : Fin (q + 1) → Fin N) (j j' : Fin (q + 1)) (i : Fin n),
    algebraMap Γ(X, (cechEtaleChart cs' haff' hne' q x).U) X.functionField
      (frobeniusLiftHomotopyAux (cechEtaleChart cs' haff' hne' q x).coords (cechEtaleChart cs' haff' hne' q x).formallyEtale (π q x) (hπ q x) p
        (F q x j) (F q x j') (hF q x j) (hF q x j') (hker q x)
        (localLogBasis (σs (x 0)) (cechEtaleChart cs' haff' hne' q x) (cechEtaleChart_logUnit cs' haff' hne' σs hunit q x) i)) ∈
      chartRegularFunctions (cechEtaleChart cs haff hne q x))
  {M : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x, M.IsLocalEquationAt y (g q x))
  (rr : Fin r → ℕ)

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
include hsub hg in
/-- The local equations on the larger intersections restrict to the smaller ones. -/
theorem cechLift_hg (q : ℕ) (x : Fin (q + 1) → Fin N) :
    ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x, M.IsLocalEquationAt y (g q x) :=
  fun y hy => hg q x y (cechOpen_le_of_le cs (fun i => (cs' i).U) hsub x hy)

include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg in
/-- **The values of the Deligne–Illusie components of the smaller cover on cochains with
logarithmic values are logarithmic** with poles bounded by `p • M + Σ_k r_k • E_k` on the larger
intersections. -/
theorem cechDIComponent_mem_of_log (b i q q' : ℕ) (h : q + b = q' + i)
    (y' : TopCat.Presheaf.CechCochain (fun i => (cs' i).U) (twistedFormsSheaf K M b).presheaf q)
    (hy' : ∀ (x : Fin (q + 1) → Fin N), ∀ z ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
      ∀ f : X.functionFieldˣ, M.IsLocalEquationAt z f →
        (f : X.functionField) • cechRationalValue K (twistedFormsSubmodule K M b)
          (fun i => (cs' i).U) hne' q y' x ∈ logFormsLattice K E z b)
    (x : Fin (q' + 1) → Fin N) (w : X) (hw : w ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
    (f : X.functionFieldˣ) (hf : (p • M + ∑ k, rr k • E k).IsLocalEquationAt w f) :
    (f : X.functionField) • cechRationalValue K (twistedFormsSubmodule K (p • M) i)
        (fun i => (cs' i).U) hne' q' (cechDIComponent cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) b i q q' h y') x ∈ logFormsLattice K E w i := by
  have hcx : IsSNCChart (cechEtaleChart cs haff hne q' x) ξ (σs (x 0)) := isSNCChart_etaleChartRestrict (hcs (x 0)) _ _ _ _
  refine smul_mem_logFormsLattice_logTwist hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q' x) (σs (x 0)) hcx w hw p M
    rr (hg q' x w hw) hf _ ?_
  by_cases hi : i ≤ b
  · obtain ⟨a, rfl⟩ : ∃ a, b = i + a := ⟨b - i, by omega⟩
    have hq : q + a = q' := by omega
    have key : cechRationalValue K (twistedFormsSubmodule K (p • M) i) (fun i => (cs' i).U) hne' q'
        (cechDIComponent cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) (i + a) i
          q q' h y') x =
        haveI := hne' q' x
        (-1 : ℤ) ^ (a * q) • rationalFormsSectionsEquiv K i
          (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x)
          (twistedChartDIComponent (cechEtaleChart cs' haff' hne' q' x) (π q' x) (hπ q' x) p (F q' x)
            (hF q' x) (hker q' x) (cechLift_hg cs cs' hsub g hg q' x) (i + a) i a rfl (cechFront q')
            ((twistedFormsSheaf K M (i + a)).presheaf.map (homOfLE
              (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs' i).U) x (cechBack a q q' hq))).op
              (y' (x ∘ cechBack a q q' hq)))).1 := by
      rw [cechDIComponent_eq cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg)
        (i + a) i a q q' h rfl hq]
      exact cechRationalValue_cechDIMap cs' haff' hne' L π hπ p F hF hker g
        (cechLift_hg cs cs' hsub g hg) (i + a) i a rfl q q' hq y' x
    rw [key, smul_comm]
    refine Submodule.smul_of_tower_mem _ _ ?_
    have := hne' q' x
    refine twistedChartDIComponent_mem_logFormsLattice hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q' x) (σs (x 0))
      hcx (cechEtaleChart cs' haff' hne' q' x) (cechEtaleChart_logUnit cs' haff' hne' σs hunit q' x)
      (cechEtaleChart_coords_eq cs cs' haff hne haff' hne' hcoords q' x) (π q' x) (hπ q' x) p
      (F q' x) (hF q' x) (hker q' x) (hΦ q' x) (hH q' x) (cechLift_hg cs cs' hsub g hg q' x)
      (i + a) i a rfl (cechFront q') _ ?_ w hw
    intro z hz
    have hz' : z ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) (x ∘ cechBack a q q' hq) :=
      TopCat.Presheaf.cechOpen_le_comp _ x _ hz
    have := hne' q (x ∘ cechBack a q q' hq)
    have hval : rationalFormsSectionsEquiv K (i + a) (TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x)
        ((twistedFormsSheaf K M (i + a)).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp
          (fun i => (cs' i).U) x (cechBack a q q' hq))).op (y' (x ∘ cechBack a q q' hq))).1 =
        cechRationalValue K (twistedFormsSubmodule K M (i + a)) (fun i => (cs' i).U) hne' q y'
          (x ∘ cechBack a q q' hq) :=
      rationalFormsSectionsEquiv_twistedFormsSheaf_map M (i + a)
        (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs' i).U) x (cechBack a q q' hq))
        (y' (x ∘ cechBack a q q' hq))
    have h2 := hy' (x ∘ cechBack a q q' hq) z hz' (g q' x) (hg q' x z hz)
    rw [← hval] at h2
    exact h2
  · rw [cechDIComponent_of_lt cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) b i
      q q' h (by omega), AddMonoidHom.zero_apply, cechRationalValue_zero, smul_zero]
    exact Submodule.zero_mem _

include hnorm hinj hξ hEc hcs hsub hunit hcoords in
/-- **Restricted logarithmic cochains have logarithmic values on the larger intersections.** -/
theorem logCechRestrict_log (b q : ℕ)
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q)
    (x : Fin (q + 1) → Fin N) (z : X) (hz : z ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
    (f : X.functionFieldˣ) (hf : M.IsLocalEquationAt z f) :
    (f : X.functionField) • cechRationalValue K (twistedFormsSubmodule K M b) (fun i => (cs' i).U)
      hne' q (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y) x ∈ logFormsLattice K E z b := by
  rw [cechRationalValue_logCechRestrict]
  have := hne q x
  exact (y x).2 z hz f hf


theorem logCechRestrict_zero (b q : ℕ) :
    logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub
      (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q 0 = 0 := by
  refine cechRationalValue_injective (twistedFormsSubmodule K M b) (fun i => (cs' i).U) hne' q
    fun x => ?_
  rw [cechRationalValue_logCechRestrict, cechRationalValue_zero, cechRationalValue_zero]

/-- **The logarithmic Deligne–Illusie components** `Ψ_{b → i}`: the components of check 466 on the
smaller cover, applied to the restricted cochain, with values lifted to
`Ω^i(log E)(p • M + Σ_k r_k • E_k)`. -/
noncomputable def logCechDIComponent (b i q q' : ℕ) (h : q + b = q' + i) :
    (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q →+
      (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) i) (fun i => (cs i).U)).X q' where
  toFun y := logCechLift E cs hne (fun i => (cs' i).U) hne' (p • M) (p • M + ∑ k, rr k • E k) i q' (cechDIComponent cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) b i q q' h (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y))
    (fun x w hw f hf => cechDIComponent_mem_of_log hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b i q q' h (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y)
      (logCechRestrict_log hnorm ξ hinj hξ E hEc cs σs hcs hne cs' hne' hsub hunit hcoords b q y) x w hw f hf)
  map_zero' := by
    refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) i) (fun i => (cs i).U) hne q'
      fun x => ?_
    rw [cechRationalValue_logCechLift, cechRationalValue_zero]
    have h0 := logCechRestrict_zero hnorm ξ hinj hξ E hEc cs σs hcs hne cs' hne' hsub hunit hcoords
      (M := M) b q
    rw [h0, map_zero, cechRationalValue_zero]
  map_add' y y' := by
    refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) i) (fun i => (cs i).U) hne q'
      fun x => ?_
    rw [cechRationalValue_add, cechRationalValue_logCechLift, cechRationalValue_logCechLift,
      cechRationalValue_logCechLift, logCechRestrict_add, map_add, cechRationalValue_add]

/-- The rational values of the logarithmic components are those of the components of the smaller
cover. -/
theorem cechRationalValue_logCechDIComponent (b i q q' : ℕ) (h : q + b = q' + i)
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q)
    (x : Fin (q' + 1) → Fin N) :
    cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) i) (fun i => (cs i).U) hne q'
        (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b i q q' h y) x =
      cechRationalValue K (twistedFormsSubmodule K (p • M) i) (fun i => (cs' i).U) hne' q'
        (cechDIComponent cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) b i q q' h (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y)) x := by
  have := hne q' x
  exact AddEquiv.apply_symm_apply _ _

/-- **The components do not raise the row.** -/
theorem logCechDIComponent_of_lt (b i q q' : ℕ) (h : q + b = q' + i) (hb : b < i) :
    logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b i q q' h = 0 := by
  ext y
  refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) i) (fun i => (cs i).U) hne q'
    fun x => ?_
  rw [cechRationalValue_logCechDIComponent, cechDIComponent_of_lt cs' haff' hne' L π hπ p F hF hker
    g (cechLift_hg cs cs' hsub g hg) b i q q' h hb, AddMonoidHom.zero_apply, cechRationalValue_zero, AddMonoidHom.zero_apply,
    cechRationalValue_zero]


variable (R : ∀ q (x : Fin (q + 2) → Fin N) (k : Fin (q + 2)),
    L q (x ∘ Fin.succAbove k) →+* L (q + 1) x)
  (hR : ∀ q x k z, π (q + 1) x (R q x k z) =
    (X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs' i).U) x
      (Fin.succAbove k))).op).hom (π q (x ∘ Fin.succAbove k) z))
  (hRF : ∀ q x k j z, R q x k (F q (x ∘ Fin.succAbove k) j z) =
    F (q + 1) x (Fin.succAbove k j) (R q x k z))
  (hann : ∀ q x z, (p : L q x) * z = 0 → π q x z = 0) (hp2 : ∀ q x, (p : L q x) * p = 0)
  (hK : ∀ q x (k : K), ∃ k' : L q x,
    π q x k' = algebraMap K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x) k ∧
      ∀ j, F q x j k' = k' ^ p)
  (hft : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs' i).U) x))
  (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
  (hsnc : IsSNCFamily K n ξ)

include hann hp2 hK hft hcover in
/-- **The diagonal values of the logarithmic components are closed.** -/
theorem logCechDIComponent_closed (b q q' : ℕ) (h : q + b = q' + b)
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q) :
    ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b (fun i => (cs i).U)).f q').hom
      (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b b q q' h y) = 0 := by
  refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (b + 1)) (fun i => (cs i).U) hne q'
    fun x => ?_
  rw [cechRationalValue_logFormsCechDiff, cechRationalValue_logCechDIComponent,
    ← cechRationalValue_twistedFormsCechDiff (fun i => (cs' i).U) hne' p c₀ hcover M b q',
    cechDIComponent_closed cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) hann hp2 hK hft c₀ hcover b q
      q' h, cechRationalValue_zero, cechRationalValue_zero]

include hR hRF hann hp2 hK hft in
/-- **The relation (H3) for the logarithmic components**: `δ Ψ_{b → 0} = Ψ_{b → 0} δ`. -/
theorem logCechDIComponent_relation_zero (b q q' : ℕ) (h : q + b = q' + 0)
    (h' : q + 1 + b = q' + 1 + 0)
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q) :
    ((cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U)).d q' (q' + 1)).hom
        (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b 0 q q' h y) =
      logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b 0 (q + 1) (q' + 1) h'
        (((cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).d q (q + 1)).hom y) := by
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply]
  refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U) hne (q' + 1)
    fun x => ?_
  rw [cechRationalValue_cechD_log, cechRationalValue_logCechDIComponent]
  simp only [cechRationalValue_logCechDIComponent]
  have h466 := cechDIComponent_relation_zero cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) R hR hRF hann
    hp2 hK hft b q q' h h' (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y)
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply] at h466
  rw [logCechRestrict_cechD, ← h466, cechRationalValue_cechD_twisted]

include hR hRF hann hp2 hK hft hcover in
/-- **The relation (H2) for the logarithmic components**:
`δ Ψ_{b → i+1} + (-1)^{q'+1} d Ψ_{b → i} = Ψ_{b → i+1} δ`. -/
theorem logCechDIComponent_relation_succ (b i q q' : ℕ) (h : q + b = q' + (i + 1))
    (h' : q + b = q' + 1 + i) (h'' : q + 1 + b = q' + 1 + (i + 1))
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q) :
    ((cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (i + 1)) (fun i => (cs i).U)).d q'
          (q' + 1)).hom (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b (i + 1) q q' h y) +
        ((-1 : ℤ) ^ (q' + 1)) • ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr i (fun i => (cs i).U)).f (q' + 1)).hom
          (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b i q (q' + 1) h' y) =
      logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b (i + 1) (q + 1) (q' + 1) h''
        (((cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).d q (q + 1)).hom y) := by
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply]
  refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (i + 1)) (fun i => (cs i).U) hne
    (q' + 1) fun x => ?_
  rw [cechRationalValue_add, cechRationalValue_zsmul, cechRationalValue_cechD_log,
    cechRationalValue_logFormsCechDiff, cechRationalValue_logCechDIComponent,
    cechRationalValue_logCechDIComponent]
  simp only [cechRationalValue_logCechDIComponent]
  have h466 := cechDIComponent_relation_succ cs' haff' hne' L π hπ p F hF hker g (cechLift_hg cs cs' hsub g hg) R hR hRF hann
    hp2 hK hft c₀ hcover b i q q' h h' h'' (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y)
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply] at h466
  rw [logCechRestrict_cechD, ← h466, cechRationalValue_add, cechRationalValue_zsmul,
    cechRationalValue_cechD_twisted, cechRationalValue_twistedFormsCechDiff]

/-- **The diagonal logarithmic component is `b! · Φ`** in rational values, with `Φ` the twisted
Frobenius lift of check 442 at the first vertex on the smaller cover. -/
theorem cechRationalValue_logCechDIComponent_diag (b q : ℕ)
    (y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q)
    (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) b) (fun i => (cs i).U) hne q
        (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b b q q rfl y) x =
      (b.factorial : ℤ) • cechRationalValue K (twistedFormsSubmodule K (p • M) b)
        (fun i => (cs' i).U) hne' q (cechTwistedFrobeniusLift cs' haff' hne' L π hπ p
          (fun q x => F q x 0) (fun q x => hF q x 0) hker g (cechLift_hg cs cs' hsub g hg) b q (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y)) x := by
  rw [cechRationalValue_logCechDIComponent, cechDIComponent_diag cs' haff' hne' L π hπ p F hF hker g
    (cechLift_hg cs cs' hsub g hg) b q (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U) hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q y), cechRationalValue_zsmul]

end Components

end MixedFujita

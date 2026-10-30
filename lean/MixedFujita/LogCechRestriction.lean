/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogKawamataViehwegIteration
public import MixedFujita.CechDeligneIllusieComparison

/-!
Restricting logarithmic Čech cochains to a cover away from the boundary (step 10, R2).

* Simple normal crossing position survives restriction to an affine open subset
  (`isSNCChart_etaleChartRestrict`), and restriction does not change the coordinates in `K(X)`.
* In every degree, the logarithmic wedge basis of a chart is the coordinate wedge basis rescaled
  by the products of the weights (`logChartFormsBasis_eq_unitsSMul`). So at a point where the
  logarithmic coordinates are units, the logarithmic forms are the regular forms
  (`logFormsLattice_eq_range_of_units`).
* The **rational value** of a Čech cochain of a subsheaf of the rational forms
  (`cechRationalValue`) is injective, additive, and computes the Čech differential
  (`cechRationalValue_cechD`) and the logarithmic and twisted de Rham differentials without
  restriction maps.
* A Čech cochain of `Ω^b(log E)(M)` on a cover by simple normal crossing charts gives a Čech
  cochain of `Ω^b(M)` with the same rational values on a cover by smaller opens where the
  logarithmic coordinates are units (`logCechRestrict`).

These are the tools to transfer the Deligne–Illusie components of check 466 on the smaller cover
to the logarithmic Čech complexes.
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

section Restrict

omit [IsIntegral X] in
/-- **Simple normal crossing position survives restriction to an affine open subset.** -/
theorem isSNCChart_etaleChartRestrict {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (h : IsSNCChart c ξ σ) (V : X.Opens) (hV : IsAffineOpen V)
    (hne : Nonempty V) (e : V ≤ c.U) : IsSNCChart (etaleChartRestrict c V hV hne e) ξ σ := by
  refine ⟨h.1, fun i => ?_⟩
  have hle : ((V : X.Opens) : Set X) ⊆ c.U := e
  have hi := h.2 i
  change closure ({ξ i} : Set X) ∩ V = (σ i).elim ∅ (fun a => X.zeroLocus
    ({(sectionRestrict K e) (c.coords (MvPolynomial.X a))} : Set Γ(X, V)) ∩ V)
  have hsub : closure ({ξ i} : Set X) ∩ V = (closure ({ξ i} : Set X) ∩ c.U) ∩ V := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle]
  rw [hsub, hi]
  cases σ i with
  | none => simp
  | some a =>
    simp only [Option.elim_some]
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle, Scheme.zeroLocus_singleton,
      Scheme.zeroLocus_singleton]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hx, hV'⟩
      refine ⟨fun hx' => hx ?_, hV'⟩
      change x ∈ X.basicOpen (X.presheaf.map (homOfLE e).op (c.coords (MvPolynomial.X a))) at hx'
      rw [Scheme.basicOpen_res] at hx'
      exact hx'.2
    · rintro ⟨hx, hV'⟩
      refine ⟨fun hx' => hx ?_, hV'⟩
      change x ∈ X.basicOpen (X.presheaf.map (homOfLE e).op (c.coords (MvPolynomial.X a)))
      rw [Scheme.basicOpen_res]
      exact ⟨hV', hx'⟩

/-- **Restriction does not change the coordinates in `K(X)`.** -/
theorem etaleChartCoordinateRationalUnit_etaleChartRestrict (c : EtaleChart K X n) (V : X.Opens)
    (hV : IsAffineOpen V) (hne : Nonempty V) (e : V ≤ c.U) (j : Fin n) :
    etaleChartCoordinateRationalUnit (etaleChartRestrict c V hV hne e) j =
      etaleChartCoordinateRationalUnit c j := by
  apply Units.ext
  rw [etaleChartCoordinateRationalUnit, etaleChartCoordinateRationalUnit,
    regularEquationRationalUnit_val, regularEquationRationalUnit_val]
  exact germToFunctionField_restrict (X := X) e _

end Restrict

section Basis

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))

/-- **The logarithmic wedge basis is the coordinate wedge basis rescaled by the products of the
weights.** -/
theorem logChartFormsBasis_eq_unitsSMul (b : ℕ) :
    logChartFormsBasis c σ b = (chartFormsBasis c b).unitsSMul (fun t =>
      ∏ i, logChartWeight c σ (Set.powersetCard.ofFinEmbEquiv.symm t i)) := by
  refine Module.Basis.eq_of_apply_eq fun t => ?_
  rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.coe_prod]
  exact basisExteriorPower_unitsSMul_apply (etaleChartBasis c) (logChartWeight c σ) b t

theorem logChartFormsBasis_repr_eq_mul (b : ℕ) (ω : RationalForms K X b)
    (t : Set.powersetCard (Fin n) b) :
    (logChartFormsBasis c σ b).repr ω t =
      (∏ i, ((logChartWeight c σ (Set.powersetCard.ofFinEmbEquiv.symm t i))⁻¹ :
        X.functionFieldˣ) : X.functionField) * (chartFormsBasis c b).repr ω t := by
  rw [logChartFormsBasis_eq_unitsSMul, Module.Basis.repr_unitsSMul, Units.smul_def, smul_eq_mul,
    ← Finset.prod_inv_distrib, Units.coe_prod]

/-- **At a point where the logarithmic coordinates are units, the logarithmic forms are the regular
forms.** -/
theorem logFormsLattice_eq_range_of_units [IsLocallyNoetherian X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (E : Fin r → CartierDivisor X)
    (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
      cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
    (hc : IsSNCChart c ξ σ) (x : X) (hx : x ∈ c.U)
    (hu : ∀ j ∈ logSetOf σ, ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) =
        (etaleChartCoordinateRationalUnit c j : X.functionField))
    (b : ℕ) : logFormsLattice K E x b = LinearMap.range (stalkFormsMap K b x) := by
  have hw : ∀ j, ∃ u : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) =
        (((logChartWeight c σ j)⁻¹ : X.functionFieldˣ) : X.functionField) := by
    intro j
    by_cases hj : ∃ k, σ k = some j
    · obtain ⟨u, hu'⟩ := hu j ((mem_logSetOf σ j).mpr hj)
      refine ⟨u, ?_⟩
      simp only [logChartWeight, hj, ↓reduceIte, inv_inv]
      exact hu'
    · refine ⟨1, ?_⟩
      simp only [logChartWeight, hj, ↓reduceIte, inv_one, Units.val_one, map_one]
  choose u hu' using hw
  ext ω
  rw [mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b ω,
    mem_range_stalkFormsMap_iff c b x hx ω]
  refine forall_congr' fun t => ?_
  rw [logChartFormsBasis_repr_eq_mul]
  have hprod : ∏ i, (((logChartWeight c σ (Set.powersetCard.ofFinEmbEquiv.symm t i))⁻¹ :
      X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((∏ i, u (Set.powersetCard.ofFinEmbEquiv.symm t i) : (X.presheaf.stalk x)ˣ) :
          X.presheaf.stalk x) := by
    rw [Units.coe_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => (hu' _).symm
  rw [hprod, mem_range_algebraMap_unit_mul_iff]

end Basis

section Value

variable (K) in
/-- A subsheaf of the rational `b`-forms, as a sheaf of modules on `X`. -/
noncomputable abbrev formsSubsheaf {b : ℕ} (S : (rationalFormsSheaf K X b).Submodule) : X.Modules :=
  S.toSheafOfModules

variable (K) in
/-- **The rational value of a Čech cochain** of a subsheaf of the rational `b`-forms. -/
noncomputable def cechRationalValue {b : ℕ} (S : (rationalFormsSheaf K X b).Submodule) {N : ℕ}
    (𝒰 : Fin N → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x)) (q : ℕ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q)
    (x : Fin (q + 1) → Fin N) : RationalForms K X b :=
  haveI := hne q x
  rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰 x) (y x).1

variable {b : ℕ} (S : (rationalFormsSheaf K X b).Submodule) {N : ℕ} (𝒰 : Fin N → X.Opens)
  (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x))

theorem cechRationalValue_injective (q : ℕ)
    {y y' : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q}
    (h : ∀ x, cechRationalValue K S 𝒰 hne q y x = cechRationalValue K S 𝒰 hne q y' x) : y = y' := by
  funext x
  have h' := h x
  unfold cechRationalValue at h'
  have := hne q x
  exact Subtype.ext ((rationalFormsSectionsEquiv K b _).injective h')

theorem cechRationalValue_add (q : ℕ)
    (y y' : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K S 𝒰 hne q (y + y') x =
      cechRationalValue K S 𝒰 hne q y x + cechRationalValue K S 𝒰 hne q y' x := by
  unfold cechRationalValue
  rw [← map_add]
  rfl

theorem cechRationalValue_zero (q : ℕ) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K S 𝒰 hne q 0 x = 0 := by
  unfold cechRationalValue
  rw [← map_zero (rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰 x))]
  rfl

theorem cechRationalValue_zsmul (q : ℕ) (k : ℤ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K S 𝒰 hne q (k • y) x = k • cechRationalValue K S 𝒰 hne q y x := by
  unfold cechRationalValue
  rw [← map_zsmul]
  rfl

/-- **The rational values compute the Čech differential** without restriction maps. -/
theorem cechRationalValue_cechD (q : ℕ)
    (y : TopCat.Presheaf.CechCochain 𝒰 (formsSubsheaf K S).presheaf q) (x : Fin (q + 2) → Fin N) :
    cechRationalValue K S 𝒰 hne (q + 1) (TopCat.Presheaf.cechD 𝒰 (formsSubsheaf K S).presheaf q y) x =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        cechRationalValue K S 𝒰 hne q y (x ∘ Fin.succAbove k) := by
  have := hne (q + 1) x
  let φ : Γ(formsSubsheaf K S, TopCat.Presheaf.cechOpen 𝒰 x) →+ RationalForms K X b :=
    (rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰 x)).toAddMonoidHom.comp
      (S.obj (op (TopCat.Presheaf.cechOpen 𝒰 x))).subtype.toAddMonoidHom
  change φ (TopCat.Presheaf.cechD 𝒰 (formsSubsheaf K S).presheaf q y x) = _
  rw [TopCat.Presheaf.cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1

end Value

section Differentials

variable {N : ℕ} (𝒰 : Fin N → X.Opens)
  (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x))

/-- **The rational values compute the twisted de Rham differential.** -/
theorem cechRationalValue_twistedFormsCechDiff (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰).X q) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (twistedFormsSubmodule K (p • D) (b + 1)) 𝒰 hne q
        (((twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰).f q).hom y) x =
      rationalFormsDiff c₀ b (cechRationalValue K (twistedFormsSubmodule K (p • D) b) 𝒰 hne q y x) := by
  have := hne q x
  unfold cechRationalValue
  exact rationalFormsSectionsEquiv_twistedFormsDiffApp p c₀ hcover D b _ (y x)

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hsnc : IsSNCFamily K n ξ)

/-- **The rational values compute the logarithmic de Rham differential.** -/
theorem cechRationalValue_logFormsCechDiff (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (M : CartierDivisor X) (rr : Fin r → ℕ) (b q : ℕ)
    (y : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰).X q) (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (b + 1)) 𝒰 hne q
        (((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰).f q).hom y) x =
      rationalFormsDiff c₀ b (cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) b) 𝒰 hne q y x) := by
  have := hne q x
  unfold cechRationalValue
  exact rationalFormsSectionsEquiv_logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b _ (y x)

end Differentials

section Refinement

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  {N : ℕ} (cs : Fin N → EtaleChart K X n) (σs : Fin N → Fin r → Option (Fin n))
  (hcs : ∀ i, IsSNCChart (cs i) ξ (σs i)) (𝒰' : Fin N → X.Opens) (hsub : ∀ i, 𝒰' i ≤ (cs i).U)
  (hlog : ∀ i, ∀ z ∈ 𝒰' i, ∀ j ∈ logSetOf (σs i), ∃ u : (X.presheaf.stalk z)ˣ,
    algebraMap (X.presheaf.stalk z) X.functionField (u : X.presheaf.stalk z) =
      (etaleChartCoordinateRationalUnit (cs i) j : X.functionField))
  (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne' : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰' x))

omit [IsIntegral X] [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
include hsub in
theorem cechOpen_le_of_le {α : Type*} (x : α → Fin N) :
    TopCat.Presheaf.cechOpen 𝒰' x ≤ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x :=
  iInf_mono fun a => hsub (x a)

include hnorm hinj hξ hEc hcs hsub hlog in
/-- **Away from the boundary the logarithmic forms are the regular forms.** -/
theorem logFormsLattice_eq_range_of_mem_refinement (i : Fin N) (z : X) (hz : z ∈ 𝒰' i) (b : ℕ) :
    logFormsLattice K E z b = LinearMap.range (stalkFormsMap K b z) :=
  logFormsLattice_eq_range_of_units (cs i) (σs i) hnorm ξ hinj hξ E hEc (hcs i) z (hsub i hz)
    (hlog i z hz) b

include hnorm hinj hξ hEc hcs hsub hlog in
theorem logCechRestrict_mem (M : CartierDivisor X) (b q : ℕ)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q)
    (x : Fin (q + 1) → Fin N) :
    haveI := hne' q x
    (rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰' x)).symm
        (cechRationalValue K (logFormsSubmodule K E M b) (fun i => (cs i).U) hne q y x) ∈
      twistedFormsSections K M b (TopCat.Presheaf.cechOpen 𝒰' x) := by
  intro z hz f hf
  rw [AddEquiv.apply_symm_apply]
  have hz0 : z ∈ 𝒰' (x 0) := TopCat.Presheaf.cechOpen_le 𝒰' x 0 hz
  rw [← logFormsLattice_eq_range_of_mem_refinement hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog
    (x 0) z hz0 b]
  exact (y x).2 z (cechOpen_le_of_le cs 𝒰' hsub x hz) f hf

/-- **The restriction of a logarithmic Čech cochain to the cover away from the boundary**: the
Čech cochain of `Ω^b(M)` with the same rational values. -/
noncomputable def logCechRestrict (M : CartierDivisor X) (b q : ℕ)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q) :
    TopCat.Presheaf.CechCochain 𝒰' (twistedFormsSheaf K M b).presheaf q := fun x =>
  haveI := hne' q x
  ⟨(rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰' x)).symm
      (cechRationalValue K (logFormsSubmodule K E M b) (fun i => (cs i).U) hne q y x),
    logCechRestrict_mem hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q y x⟩

theorem cechRationalValue_logCechRestrict (M : CartierDivisor X) (b q : ℕ)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q)
    (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (twistedFormsSubmodule K M b) 𝒰' hne' q
        (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q y) x =
      cechRationalValue K (logFormsSubmodule K E M b) (fun i => (cs i).U) hne q y x := by
  have := hne' q x
  exact AddEquiv.apply_symm_apply _ _

theorem logCechRestrict_add (M : CartierDivisor X) (b q : ℕ)
    (y y' : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q) :
    logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q (y + y') =
      logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q y +
        logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q y' := by
  refine cechRationalValue_injective (twistedFormsSubmodule K M b) 𝒰' hne' q fun x => ?_
  rw [cechRationalValue_add, cechRationalValue_logCechRestrict, cechRationalValue_logCechRestrict,
    cechRationalValue_logCechRestrict, cechRationalValue_add]

/-- **Restriction commutes with the Čech differential.** -/
theorem logCechRestrict_cechD (M : CartierDivisor X) (b q : ℕ)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q) :
    logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b (q + 1)
        (TopCat.Presheaf.cechD (fun i => (cs i).U) (logFormsSheaf K E M b).presheaf q y) =
      TopCat.Presheaf.cechD 𝒰' (twistedFormsSheaf K M b).presheaf q
        (logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs 𝒰' hsub hlog hne hne' M b q y) := by
  refine cechRationalValue_injective (twistedFormsSubmodule K M b) 𝒰' hne' (q + 1) fun x => ?_
  rw [cechRationalValue_logCechRestrict]
  refine (cechRationalValue_cechD (logFormsSubmodule K E M b) (fun i => (cs i).U) hne q y x).trans
    ((Finset.sum_congr rfl fun k _ => ?_).trans
      (cechRationalValue_cechD (twistedFormsSubmodule K M b) 𝒰' hne' q _ x).symm)
  rw [cechRationalValue_logCechRestrict]

end Refinement

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogChartFrobeniusCartier

/-!
The logarithmic Deligne–Illusie comparison from lift data, and Kawamata–Viehweg vanishing in
characteristic `p` (step 10, R2).

On each Čech intersection of the cover by simple normal crossing charts, the sections of
`Ω^b(log E)(M)` are model forms `Σ_t (a_t g⁻¹) θ_t` (check 482). With the coordinate Frobenius
lift at the first vertex, the diagonal logarithmic component of check 489 is `b!` times the
logarithmic inverse Cartier operator on model forms (check 490,
`cechRationalValue_logCechDIComponent_diag_model`). So the Cartier isomorphism of check 482 on
each chart gives the Cartier conditions for the diagonal components (`b!` is a unit for
`b ≤ n < p`).
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

section Values

/-- **A logarithmic Čech cochain with prescribed rational values.** -/
noncomputable def logCechOfValues {r : ℕ} (E : Fin r → CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x))
    (Nt : CartierDivisor X) (b q : ℕ) (v : (Fin (q + 1) → Fin N) → RationalForms K X b)
    (hv : ∀ x, ∀ w ∈ TopCat.Presheaf.cechOpen 𝒰 x, ∀ f : X.functionFieldˣ,
      Nt.IsLocalEquationAt w f → (f : X.functionField) • v x ∈ logFormsLattice K E w b) :
    TopCat.Presheaf.CechCochain 𝒰 (logFormsSheaf K E Nt b).presheaf q := fun x =>
  haveI := hne q x
  ⟨(rationalFormsSectionsEquiv K b (TopCat.Presheaf.cechOpen 𝒰 x)).symm (v x), fun w hw f hf => by
    rw [AddEquiv.apply_symm_apply]
    exact hv x w hw f hf⟩

theorem cechRationalValue_logCechOfValues {r : ℕ} (E : Fin r → CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens)
    (hne : ∀ q (x : Fin (q + 1) → Fin N), Nonempty (TopCat.Presheaf.cechOpen 𝒰 x))
    (Nt : CartierDivisor X) (b q : ℕ) (v : (Fin (q + 1) → Fin N) → RationalForms K X b)
    (hv : ∀ x, ∀ w ∈ TopCat.Presheaf.cechOpen 𝒰 x, ∀ f : X.functionFieldˣ,
      Nt.IsLocalEquationAt w f → (f : X.functionField) • v x ∈ logFormsLattice K E w b)
    (x : Fin (q + 1) → Fin N) :
    cechRationalValue K (logFormsSubmodule K E Nt b) 𝒰 hne q
      (logCechOfValues E 𝒰 hne Nt b q v hv) x = v x := by
  have := hne q x
  exact AddEquiv.apply_symm_apply _ _

/-- The de Rham differential of rational forms does not depend on the reference chart. -/
theorem rationalFormsDiff_eq_of_chart (c₀ c₁ : EtaleChart K X n) (b : ℕ) (ω : RationalForms K X b) :
    rationalFormsDiff c₀ b ω = rationalFormsDiff c₁ b ω :=
  Subtype.ext (by rw [rationalFormsDiff_coe, rationalFormsDiff_coe, rationalDeRhamDiff_eq c₀ c₁])

end Values


section Assembly

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hsnc : IsSNCFamily K n ξ)

/-- **The logarithmic Deligne–Illusie comparison data from components** (the logarithmic version of
check 445). -/
theorem logDeligneIllusieStaircaseData_of_components (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ} (𝒰 : Fin N → X.Opens)
    (Ψ : ∀ b i q q', q + b = q' + i → (cechComplexLinear K (logFormsSheaf K E M b) 𝒰).X q →+
      (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) i) 𝒰).X q')
    (hΨlt : ∀ b i q q' h, b < i → Ψ b i q q' h = 0)
    (hΨclosed : ∀ b q q' h y, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰).f q').hom (Ψ b b q q' h y) = 0)
    (hΨ0 : ∀ b q q' h h' y,
      ((cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) 0) 𝒰).d q' (q' + 1)).hom (Ψ b 0 q q' h y) =
        Ψ b 0 (q + 1) (q' + 1) h'
          (((cechComplexLinear K (logFormsSheaf K E M b) 𝒰).d q (q + 1)).hom y))
    (hΨsucc : ∀ b i q q' h h' h'' y,
      ((cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (i + 1)) 𝒰).d q' (q' + 1)).hom
          (Ψ b (i + 1) q q' h y) + ((-1 : ℤ) ^ (q' + 1)) •
          ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr i 𝒰).f (q' + 1)).hom (Ψ b i q (q' + 1) h' y) =
        Ψ b (i + 1) (q + 1) (q' + 1) h''
          (((cechComplexLinear K (logFormsSheaf K E M b) 𝒰).d q (q + 1)).hom y))
    (hsurj0 : ∀ q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 0 𝒰).f q).hom z = 0 → ∃ y, z = Ψ 0 0 q q rfl y)
    (hsurj : ∀ c q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Ψ (c + 1) (c + 1) q q rfl y + ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w)
    (hinj0 : ∀ q y, Ψ 0 0 q q rfl y = 0 → y = 0)
    (hinj' : ∀ c q y w, Ψ (c + 1) (c + 1) q q rfl y = ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w → y = 0) :
    LogDeligneIllusieStaircaseData K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰 := by
  refine ⟨coneAssemble (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰)
      (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰)
      (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n Ψ,
    fun c q => Ψ c c q q rfl, ?_, ?_, ?_, hsurj0, hsurj, hinj0, hinj'⟩
  · exact coneAssemble_d _ _ _ _ n Ψ hΨlt hΨclosed hΨ0 hΨsucc
  · exact fun m c x hx => coneAssemble_rowsLE _ _ _ _ n Ψ hΨlt m c x hx
  · intro m c q h x hx
    by_cases hc : c ≤ n
    · exact coneAssemble_diag _ _ _ _ n Ψ hΨlt m c q h hc x hx
    · rw [LinearMap.congr_fun (coneRowComp_of_lt _ _ _ c n 0 c q m _ h (by omega)) _,
        LinearMap.congr_fun (coneRowComp_of_lt _ _ _ c n 0 c q m _ h (by omega)) x,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end Assembly

section Comparison

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
  (hΦ0 : ∀ q (x : Fin (q + 1) → Fin N) (i : Fin n),
    KaehlerDifferential.map K K Γ(X, (cechEtaleChart cs' haff' hne' q x).U) X.functionField
      (frobeniusLiftOneFormAux (cechEtaleChart cs' haff' hne' q x).coords (cechEtaleChart cs' haff' hne' q x).formallyEtale (π q x) (hπ q x) p (F q x 0)
        (hF q x 0) (hker q x)
        (localLogBasis (σs (x 0)) (cechEtaleChart cs' haff' hne' q x) (cechEtaleChart_logUnit cs' haff' hne' σs hunit q x) i)) =
      logCartierCoeff (cechEtaleChart cs haff hne q x) (σs (x 0)) p i • logChartBasis (cechEtaleChart cs haff hne q x) (σs (x 0)) i)
  (hy0 : ∀ q (x : Fin (q + 1) → Fin N) (j : Fin n),
    etaleCoordFun (cechEtaleChart cs haff hne q x).coords j ≠ 0)
  (hftU : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hrr : ∀ k, rr k < p)

include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg hΦ0 in
/-- **The diagonal logarithmic component on model forms**: if the rational value of `Y` at `x` is
`Σ_t (a_t g⁻¹) θ_t`, then the diagonal component has the rational value `b! · C⁻¹(a)`. -/
theorem cechRationalValue_logCechDIComponent_diag_model (b q : ℕ)
    (Y : (cechComplexLinear K (logFormsSheaf K E M b) (fun i => (cs i).U)).X q)
    (x : Fin (q + 1) → Fin N) (a : Set.powersetCard (Fin n) b → Γ(X, (cechEtaleChart cs haff hne q x).U))
    (ha : cechRationalValue K (logFormsSubmodule K E M b) (fun i => (cs i).U) hne q Y x =
      logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (((g q x)⁻¹ : X.functionFieldˣ) : X.functionField) a) :
    cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) b) (fun i => (cs i).U) hne q
        (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b b q q rfl Y) x =
      (b.factorial : ℤ) • logChartInverseCartierForm (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a := by
  rw [cechRationalValue_logCechDIComponent_diag]
  congr 1
  rw [cechRationalValue_apply, cechTwistedFrobeniusLift_apply]
  have := hne' q x
  refine rationalFormsSectionsEquiv_twistedChartFrobeniusLiftForms_model (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart cs' haff' hne' q x)
    (cechEtaleChart_logUnit cs' haff' hne' σs hunit q x) (π q x) (hπ q x) p (F q x 0) (hF q x 0)
    (hker q x) (cechEtaleChart_coords_eq cs cs' haff hne haff' hne' hcoords q x) (hΦ0 q x)
    ((cechLift_hg cs cs' hsub g hg) q x) (logTwistExponent (σs (x 0)) rr) a _ ?_
  have h1 := cechRationalValue_logCechRestrict hnorm ξ hinj hξ E hEc cs σs hcs (fun i => (cs' i).U)
    hsub (logUnit_stalk cs cs' σs hunit hcoords) hne hne' M b q Y x
  rw [← ha, ← h1]
  rfl


omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] [IsIntegral X] in
include hcs in
theorem cechEtaleChart_isSNCChart (q : ℕ) (x : Fin (q + 1) → Fin N) :
    IsSNCChart (cechEtaleChart cs haff hne q x) ξ (σs (x 0)) :=
  isSNCChart_etaleChartRestrict (hcs (x 0)) _ _ _ _

omit [Fact p.Prime] [CharP K p] in
include hnorm hinj hξ hEc hcs hg in
/-- The inverse twist weight is an equation of `p • M + Σ_k r_k • E_k` on every Čech intersection. -/
theorem cechTarget_isLocalEquationAt (q : ℕ) (x : Fin (q + 1) → Fin N) :
    ∀ w ∈ (cechEtaleChart cs haff hne q x).U, (p • M + ∑ k, rr k • E k).IsLocalEquationAt w
      (g q x ^ p * logTwistMonomial (cechEtaleChart cs haff hne q x) (logSetOf (σs (x 0))) (logTwistExponent (σs (x 0)) rr)) :=
  fun w hw => isLocalEquationAt_logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) rr hnorm ξ hinj hξ E hEc
    (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x) p M (hg q x) w hw

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] [IsIntegral X]
  [CharP K p] in
include hcs hrr in
theorem cechTwistExponent_lt (q : ℕ) (x : Fin (q + 1) → Fin N) :
    ∀ j ∈ logSetOf (σs (x 0)), (logTwistExponent (σs (x 0)) rr) j < p :=
  fun j _ => logTwistExponent_lt (hcs (x 0)).1 (Fact.out : p.Prime).pos hrr j

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] [Fact p.Prime] in
theorem rationalForms_natCast_zsmul {b : ℕ} (v : RationalForms K X b) : (p : ℤ) • v = 0 := by
  rw [← Int.cast_smul_eq_zsmul X.functionField, Int.cast_natCast,
    natCast_char_eq_zero_of_algebra (K := K) (S := X.functionField) p, zero_smul]

include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg hΦ0 hy0 hftU hrr in
/-- **Cartier condition in degree `0`, surjectivity**, for the logarithmic diagonal component. -/
theorem logCechDIComponent_surj_zero [PerfectRing K p] (q : ℕ)
    (z : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U)).X q)
    (hz : ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 0 (fun i => (cs i).U)).f q).hom z = 0) :
    ∃ y, z = logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr 0 0 q q rfl y := by
  have hstep : ∀ x : Fin (q + 1) → Fin N, ∃ y : Set.powersetCard (Fin n) 0 → Γ(X, (cechEtaleChart cs haff hne q x).U),
      cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U) hne q z x =
        logChartInverseCartierForm (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) y := by
    intro x
    have := hne q x
    have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hftU q x
    obtain ⟨a, ha⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0))
      (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
      (cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U) hne q z x)
      (fun w hw => (z x).2 w hw _ (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff
        hne p g hg rr q x w hw))
    have hcl : rationalFormsDiff (cechEtaleChart cs haff hne q x) 0 (logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a) = 0 := by
      have h1 := cechRationalValue_logFormsCechDiff (fun i => (cs i).U) hne hnorm ξ hinj hξ E hEc hsnc
        p c₀ M rr 0 q z x
      rw [hz, cechRationalValue_zero, ha, rationalFormsDiff_eq_of_chart c₀ (cechEtaleChart cs haff hne q x)] at h1
      exact h1.symm
    obtain ⟨y, hy⟩ := logChart_cartier_exists_zero (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x) (hy0 q x)
      (cechTwistExponent_lt ξ cs σs hcs p rr hrr q x) a hcl
    exact ⟨y, ha.trans hy⟩
  choose y hy using hstep
  refine ⟨logCechOfValues E (fun i => (cs i).U) hne M 0 q
    (fun x => logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (((g q x)⁻¹ : X.functionFieldˣ) : X.functionField) (y x))
    (fun x w hw f hf => logChartModelForm_mem hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0))
      (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x) (hg q x) (y x) w hw f hf), ?_⟩
  refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) 0) (fun i => (cs i).U) hne q
    fun x => ?_
  rw [hy x, cechRationalValue_logCechDIComponent_diag_model hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hΦ0 0 q _ x (y x) (cechRationalValue_logCechOfValues E (fun i => (cs i).U) hne M 0 q _ _ x),
    Nat.factorial_zero, Nat.cast_one, one_smul]


include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg hΦ0 hy0 hftU hrr in
/-- **Cartier condition, surjectivity**, for the logarithmic diagonal component (`p > n`). -/
theorem logCechDIComponent_surj [PerfectRing K p] (hpn : n < p) (c q : ℕ)
    (z : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (c + 1)) (fun i => (cs i).U)).X q)
    (hz : ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (c + 1) (fun i => (cs i).U)).f q).hom z = 0) :
    ∃ y w, z = logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr (c + 1) (c + 1) q q rfl y +
      ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c (fun i => (cs i).U)).f q).hom w := by
  rcases le_or_gt (c + 1) n with hc | hc
  · have hstep : ∀ x : Fin (q + 1) → Fin N,
        ∃ (y : Set.powersetCard (Fin n) (c + 1) → Γ(X, (cechEtaleChart cs haff hne q x).U))
          (a' : Set.powersetCard (Fin n) c → Γ(X, (cechEtaleChart cs haff hne q x).U)),
          cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (c + 1)) (fun i => (cs i).U) hne q z x =
            logChartInverseCartierForm (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) y +
              rationalFormsDiff (cechEtaleChart cs haff hne q x) c (logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a') := by
      intro x
      have := hne q x
      have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hftU q x
      obtain ⟨a, ha⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
        (cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (c + 1)) (fun i => (cs i).U) hne q z x)
        (fun w hw => (z x).2 w hw _ (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff hne p g hg rr q x w hw))
      have hcl : rationalFormsDiff (cechEtaleChart cs haff hne q x) (c + 1) (logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a) = 0 := by
        have h1 := cechRationalValue_logFormsCechDiff (fun i => (cs i).U) hne hnorm ξ hinj hξ E hEc
          hsnc p c₀ M rr (c + 1) q z x
        rw [hz, cechRationalValue_zero, ha, rationalFormsDiff_eq_of_chart c₀ (cechEtaleChart cs haff hne q x)] at h1
        exact h1.symm
      obtain ⟨y, a', hy⟩ := logChart_cartier_exists_succ (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x) (hy0 q x)
        (cechTwistExponent_lt ξ cs σs hcs p rr hrr q x) a hcl
      exact ⟨y, a', ha.trans hy⟩
    choose y a' hy using hstep
    refine ⟨Nat.gcdA (c + 1).factorial p • logCechOfValues E (fun i => (cs i).U) hne M (c + 1) q
      (fun x => logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (((g q x)⁻¹ : X.functionFieldˣ) : X.functionField)
        (y x))
      (fun x w hw f hf => logChartModelForm_mem hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x) (hg q x)
        (y x) w hw f hf),
      logCechOfValues E (fun i => (cs i).U) hne (p • M + ∑ k, rr k • E k) c q
        (fun x => logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) (a' x))
        (fun x w hw f hf => logChartModelForm_mem hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x) (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff hne p g hg rr q x)
          (a' x) w hw f hf), ?_⟩
    refine cechRationalValue_injective (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (c + 1)) (fun i => (cs i).U) hne q
      fun x => ?_
    rw [cechRationalValue_add, map_zsmul, cechRationalValue_zsmul,
      cechRationalValue_logCechDIComponent_diag_model hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hΦ0 (c + 1) q _ x (y x) (cechRationalValue_logCechOfValues E (fun i => (cs i).U) hne M
        (c + 1) q _ _ x),
      cechRationalValue_logFormsCechDiff, cechRationalValue_logCechOfValues, hy x, smul_smul,
      mul_comm, factorial_gcdA_zsmul (Fact.out : p.Prime) (by omega) (rationalForms_natCast_zsmul p),
      rationalFormsDiff_eq_of_chart c₀ (cechEtaleChart cs haff hne q x)]
  · have hsub' : ∀ w : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (c + 1))
        (fun i => (cs i).U)).X q, w = 0 := fun w => funext fun x =>
      @Subsingleton.elim _ (logFormsSheaf_sections_subsingleton_of_lt c₀ E _ hc _) _ _
    exact ⟨0, 0, (hsub' z).trans (hsub' _).symm⟩

include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg hΦ0 hy0 in
/-- **Cartier condition in degree `0`, injectivity**, for the logarithmic diagonal component. -/
theorem logCechDIComponent_inj_zero (q : ℕ)
    (y : (cechComplexLinear K (logFormsSheaf K E M 0) (fun i => (cs i).U)).X q)
    (h : logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr 0 0 q q rfl y = 0) : y = 0 := by
  refine cechRationalValue_injective (logFormsSubmodule K E M 0) (fun i => (cs i).U) hne q
    fun x => ?_
  have := hne q x
  obtain ⟨a, ha⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
    (cechRationalValue K (logFormsSubmodule K E M 0) (fun i => (cs i).U) hne q y x)
    (fun w hw => (y x).2 w hw (g q x) (hg q x w hw))
  have hval := congrArg (fun z => cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) 0)
    (fun i => (cs i).U) hne q z x) h
  rw [cechRationalValue_logCechDIComponent_diag_model hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hΦ0 0 q y x a ha, cechRationalValue_zero, Nat.factorial_zero, Nat.cast_one, one_smul] at hval
  have h0 := logChart_cartier_unique_zero (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x) (hy0 q x) a hval
  rw [cechRationalValue_zero, ha, h0]
  simp only [logChartModelForm, Pi.zero_apply, map_zero, zero_mul, zero_smul, Finset.sum_const_zero]

include hnorm hinj hξ hEc hcs hsub hunit hcoords hΦ hH hg hΦ0 hy0 hftU hrr in
/-- **Cartier condition, injectivity**, for the logarithmic diagonal component (`p > n`). -/
theorem logCechDIComponent_inj [PerfectRing K p] (hpn : n < p) (c q : ℕ)
    (y : (cechComplexLinear K (logFormsSheaf K E M (c + 1)) (fun i => (cs i).U)).X q)
    (w : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) c) (fun i => (cs i).U)).X q)
    (h : logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr (c + 1) (c + 1) q q rfl y =
      ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c (fun i => (cs i).U)).f q).hom w) : y = 0 := by
  rcases le_or_gt (c + 1) n with hc | hc
  · refine cechRationalValue_injective (logFormsSubmodule K E M (c + 1)) (fun i => (cs i).U) hne q
      fun x => ?_
    have := hne q x
    have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hftU q x
    obtain ⟨a, ha⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
      (cechRationalValue K (logFormsSubmodule K E M (c + 1)) (fun i => (cs i).U) hne q y x)
      (fun w hw => (y x).2 w hw (g q x) (hg q x w hw))
    obtain ⟨a', ha'⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
      (cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) c) (fun i => (cs i).U) hne q w x)
      (fun w' hw' => (w x).2 w' hw' _ (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff hne p g hg rr q x w' hw'))
    have hval := congrArg (fun z => cechRationalValue K (logFormsSubmodule K E (p • M + ∑ k, rr k • E k) (c + 1))
      (fun i => (cs i).U) hne q z x) h
    rw [cechRationalValue_logCechDIComponent_diag_model hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hΦ0 (c + 1) q y x a ha, cechRationalValue_logFormsCechDiff, ha',
      rationalFormsDiff_eq_of_chart c₀ (cechEtaleChart cs haff hne q x)] at hval
    obtain ⟨a'', ha''⟩ := exists_logChartModelForm_eq hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x) (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x)
      (Nat.gcdA (c + 1).factorial p • logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a')
      (fun w' hw' => by
        rw [smul_comm]
        exact Submodule.smul_of_tower_mem _ _ (logChartModelForm_mem hnorm ξ hinj hξ E hEc (cechEtaleChart cs haff hne q x)
          (σs (x 0)) (cechEtaleChart_isSNCChart ξ cs σs hcs haff hne q x) (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff hne p g hg rr q x) a' w' hw' _ (cechTarget_isLocalEquationAt hnorm ξ hinj hξ E hEc cs σs hcs haff hne p g hg rr q x w' hw')))
    have hval2 : logChartInverseCartierForm (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a =
        rationalFormsDiff (cechEtaleChart cs haff hne q x) c (logChartModelForm (cechEtaleChart cs haff hne q x) (σs (x 0)) (logTwistWeight (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x)) a'') := by
      rw [← ha'', map_zsmul, ← hval, smul_smul, mul_comm,
        factorial_gcdA_zsmul (Fact.out : p.Prime) (by omega) (rationalForms_natCast_zsmul p)]
    have h0 := logChart_cartier_unique_succ (cechEtaleChart cs haff hne q x) (σs (x 0)) p (logTwistExponent (σs (x 0)) rr) (g q x) (hy0 q x) (cechTwistExponent_lt ξ cs σs hcs p rr hrr q x) a a'' hval2
    rw [cechRationalValue_zero, ha, h0]
    simp only [logChartModelForm, Pi.zero_apply, map_zero, zero_mul, zero_smul, Finset.sum_const_zero]
  · exact funext fun x =>
      @Subsingleton.elim _ (logFormsSheaf_sections_subsingleton_of_lt c₀ E M hc _) _ _


include hcs haff hne cs' haff' hne' hsub hunit hcoords hπ hF hker hΦ hH hg hcover R hR hRF hann hp2 hK hft
  hΦ0 hy0 hftU hrr in
/-- **The logarithmic Deligne–Illusie comparison data from lifts on the Čech intersections**
(`p > n`). -/
theorem logDeligneIllusieStaircaseData_of_cechLifts [PerfectRing K p] (hpn : n < p) :
    LogDeligneIllusieStaircaseData K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (fun i => (cs i).U) :=
  logDeligneIllusieStaircaseData_of_components hnorm ξ hinj hξ E hEc hsnc p c₀ M rr
    (fun i => (cs i).U) (logCechDIComponent hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr)
    (fun b i q q' h hb => logCechDIComponent_of_lt hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr b i q q' h hb)
    (fun b q q' h y => logCechDIComponent_closed hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hann hp2 hK hft c₀ hcover hsnc b q q' h y)
    (fun b q q' h h' y => logCechDIComponent_relation_zero hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr R hR hRF hann hp2 hK hft b q q' h h'
      y)
    (fun b i q q' h h' h'' y => logCechDIComponent_relation_succ hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr R hR hRF hann hp2 hK hft c₀
      hcover hsnc b i q q' h h' h'' y)
    (fun q z hz => logCechDIComponent_surj_zero hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr c₀ hsnc hΦ0 hy0 hftU hrr q z hz)
    (fun c q z hz => logCechDIComponent_surj hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr c₀ hsnc hΦ0 hy0 hftU hrr hpn c q z hz)
    (fun q y h => logCechDIComponent_inj_zero hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr hΦ0 hy0 q y h)
    (fun c q y w h => logCechDIComponent_inj hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff' hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH g hg rr c₀ hsnc hΦ0 hy0 hftU hrr hpn c q y w h)

end Comparison


section Vanishing

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
  (hΦ0 : ∀ q (x : Fin (q + 1) → Fin N) (i : Fin n),
    KaehlerDifferential.map K K Γ(X, (cechEtaleChart cs' haff' hne' q x).U) X.functionField
      (frobeniusLiftOneFormAux (cechEtaleChart cs' haff' hne' q x).coords (cechEtaleChart cs' haff' hne' q x).formallyEtale (π q x) (hπ q x) p (F q x 0)
        (hF q x 0) (hker q x)
        (localLogBasis (σs (x 0)) (cechEtaleChart cs' haff' hne' q x) (cechEtaleChart_logUnit cs' haff' hne' σs hunit q x) i)) =
      logCartierCoeff (cechEtaleChart cs haff hne q x) (σs (x 0)) p i • logChartBasis (cechEtaleChart cs haff hne q x) (σs (x 0)) i)
  (hy0 : ∀ q (x : Fin (q + 1) → Fin N) (j : Fin n),
    etaleCoordFun (cechEtaleChart cs haff hne q x).coords j ≠ 0)
  (hftU : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
/-- The product `Π_k h_k^{D_k}` of local equations is a local equation of `Σ_k D_k • E_k`. -/
theorem isLocalEquationAt_sum_nsmul_prod_pow (D : Fin r → ℕ) {y : X} {h : Fin r → X.functionFieldˣ}
    (hh : ∀ k, (E k).IsLocalEquationAt y (h k)) :
    (∑ k, D k • E k).IsLocalEquationAt y (∏ k, h k ^ D k) := by
  have : ∀ T : Finset (Fin r), (∑ k ∈ T, D k • E k).IsLocalEquationAt y (∏ k ∈ T, h k ^ D k) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.prod_empty]
      exact CartierDivisor.isLocalEquationAt_zero y
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (isLocalEquationAt_nsmul_pow (hh a) (D a)).mul ih
  exact this Finset.univ

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
include hnorm hinj hξ hEc hsnc hcs haff hne cs' haff' hne' hsub hunit hcoords hπ hF hker hΦ hH R hR hRF
  hann hp2 hK hft hΦ0 hy0 hftU in
/-- **Kawamata–Viehweg vanishing in characteristic `p` from logarithmic lift data**: over a finite
field of characteristic `p > n`, let the boundary `E` be simple normal crossing on a cover by
charts `cs`, with lift data on a cover `cs'` away from the boundary as above (the Frobenius lifts
compatible with the logarithmic structure, the coordinate Frobenius at the first vertex). If
`m • A − Σ_k a_k • E_k` is ample with `0 ≤ a_k < m`, then `H^j(O(K_X + A)) = 0` for `j ≥ 1`. -/
theorem canonical_vanishing_of_logCechLifts [Finite K] [PerfectRing K p]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hpn : n < p) (hcov : ⨆ i, (cs i).U = ⊤) (A : CartierDivisor X)
    (gA : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
    (hgA : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x, A.IsLocalEquationAt y (gA q x))
    (gE : Fin r → ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
    (hgE : ∀ k q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
      (E k).IsLocalEquationAt y (gE k q x))
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (a : Fin r → ℕ) (ha : ∀ k, a k < m₀)
    (hamp : CartierIsAmpleProj K (m₀ • A - ∑ k, a k • E k)) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + A).sheaf j) := by
  refine canonical_vanishing_of_logDeligneIllusie hnorm ξ hinj hξ E hEc hsnc c₀ hcover p
    (Fact.out : p.Prime).two_le A m₀ hm₀ a ha hamp (fun e D rr hrr m hm => ?_) hj
  have hgM : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
      (p ^ e • A - ∑ k, D k • E k).IsLocalEquationAt y
        (gA q x ^ p ^ e * (∏ k, gE k q x ^ D k)⁻¹) := by
    intro q x y hy
    rw [sub_eq_add_neg]
    exact (isLocalEquationAt_nsmul_pow (hgA q x y hy) (p ^ e)).mul
      (isLocalEquationAt_sum_nsmul_prod_pow E D (fun k => hgE k q x y hy)).inv
  exact logDeligneIllusieInequality_of_staircaseData hnorm ξ hinj hξ E hEc hsnc p c₀
    (p ^ e • A - ∑ k, D k • E k) rr (fun i => (cs i).U) (fun i => (cs i).isAffine) hcov
    (logDeligneIllusieStaircaseData_of_cechLifts hnorm ξ hinj hξ E hEc cs σs hcs haff hne cs' haff'
      hne' hsub hunit hcoords L π hπ p F hF hker hΦ hH (fun q x => gA q x ^ p ^ e * (∏ k, gE k q x ^ D k)⁻¹)
      hgM rr R hR hRF hann hp2 hK hft c₀ hcover hsnc hΦ0 hy0 hftU hrr hpn) hm

end Vanishing

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogFormsDeRham
public import MixedFujita.LogFormsTensor
public import MixedFujita.DeligneIllusieHomologyInjective

/-!
The logarithmic Deligne–Illusie inequality from the staircase hypotheses (step 10, R2).

These are the logarithmic versions of checks 427, 435, 436 and 440. The sheaves `Ω^b_X(log E)(M)`
are coherent (check 481). So on a finite affine open cover of a proper scheme with affine diagonal,
over a finite field, their `K`-linear Čech cohomology has the dimension of their sheaf cohomology
(`finrank_cechComplexLinear_logForms_homology`).

* The iterated cone of the rows `Č(Ω^b(log E)(p • M + Σ_k r_k • E_k))` along the de Rham
  differential of check 485 is the logarithmic Čech–de Rham complex (`logCechDeRhamCone`). Its
  cohomology in degree `m` has dimension at most
  `Σ_{b ≤ n} h^{m-b}(Ω^b(log E)(p • M + Σ_k r_k • E_k))`.
* The iterated cone of the rows `Č(Ω^b(log E)(M))` with zero vertical maps (`logDISource`) has
  dimension `Σ_{b ≤ n} h^{m-b}(Ω^b(log E)(M))` in degree `m ≥ n`.

An additive chain map between them satisfying the staircase hypotheses of check 439 gives the
logarithmic Deligne–Illusie inequality (`logDeligneIllusieInequality_of_staircase`).
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

/-- **`Ω^b_X(log E)(M)` vanishes above the dimension.** -/
theorem logFormsSheaf_sections_subsingleton_of_lt (c : EtaleChart K X n) {r : ℕ}
    (E : Fin r → CartierDivisor X) (M : CartierDivisor X) {b : ℕ} (hb : n < b) (U : X.Opens) :
    Subsingleton Γ(logFormsSheaf K E M b, U) := by
  have := rationalFormsSheaf_sections_subsingleton_of_lt c hb U
  exact inferInstanceAs (Subsingleton ↥(logFormsSections K E M b U))

section Counts

variable {r : ℕ} (E : Fin r → CartierDivisor X)

variable (K) in
/-- The dimension count `Σ_{i ≤ d} h^{m - i}(Ω^i_X(log E)(M))` of total degree `m`. -/
noncomputable def logHodgeCount (M : CartierDivisor X) (d m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), Module.finrank K
    (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (logFormsSheaf K E M i) (m - i))

variable (K) in
/-- **The logarithmic Deligne–Illusie dimension inequality** for `M` and `R = Σ_k r_k • E_k` in
total degree `m`: `Σ_{i ≤ d} h^{m - i}(Ω^i(log E)(M)) ≤ Σ_{i ≤ d} h^{m - i}(Ω^i(log E)(p • M + R))`. -/
def LogDeligneIllusieInequality (M : CartierDivisor X) (p : ℕ) (rr : Fin r → ℕ) (d m : ℕ) : Prop :=
  logHodgeCount K E M d m ≤ logHodgeCount K E (p • M + ∑ k, rr k • E k) d m

variable (K) in
/-- **The source of the logarithmic Deligne–Illusie map**, `⊕_{b ≤ d} Č(Ω^b(log E)(M))[-b]`. -/
noncomputable def logDISource (M : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens) (d : ℕ) :
    CochainComplex (ModuleCat.{u} K) ℕ :=
  iteratedCone (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) d 0

end Counts

section Cohomology

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hsnc : IsSNCFamily K n ξ)

include hnorm hinj hξ hEc hsnc in
/-- **The Čech cohomology of `Ω^b_X(log E)(M)` is additively its sheaf cohomology** for a finite
affine cover of a scheme with affine diagonal. -/
theorem logFormsSheaf_nonempty_cechHomologyAddEquiv
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) (q : ℕ) :
    Nonempty ((TopCat.Presheaf.cechComplex 𝒰 (logFormsSheaf K E M b).presheaf).homology q ≃+
      TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (logFormsSheaf K E M b) q) := by
  have := (isCoherent_logFormsSheaf hnorm ξ hinj hξ hEc hsnc M b).isQuasicoherent
  obtain ⟨e⟩ := Scheme.Modules.nonempty_cechHomologyIso_H (logFormsSheaf K E M b) 𝒰 h𝒰 hcov q
  exact ⟨e.addCommGroupIsoToAddEquiv.trans
    (sgaCohomologyLinearEquiv (logFormsSheaf K E M b) q).toAddEquiv⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
include hnorm hinj hξ hEc hsnc in
/-- **The cohomology of `Ω^b_X(log E)(M)` is finite-dimensional** on a proper scheme. -/
theorem logFormsSheaf_cohomology_finite [IsProper (X ↘ Spec (CommRingCat.of K))]
    (M : CartierDivisor X) (b i : ℕ) :
    Module.Finite K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (logFormsSheaf K E M b) i) := by
  have := isCoherent_logFormsSheaf hnorm ξ hinj hξ hEc hsnc M b
  exact proper_coherent_cohomology_finite K (logFormsSheaf K E M b) i

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
include hnorm hinj hξ hEc hsnc in
/-- **The `K`-linear Čech cohomology of `Ω^b(log E)(M)` has the dimension of the sheaf
cohomology** over a finite field, for a finite affine open cover of a proper scheme with affine
diagonal. -/
theorem finrank_cechComplexLinear_logForms_homology [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (M : CartierDivisor X) (b : ℕ) {N : ℕ} (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i))
    (hcov : ⨆ i, 𝒰 i = ⊤) (q : ℕ) :
    FiniteDimensional K ((cechComplexLinear K (logFormsSheaf K E M b) 𝒰).homology q) ∧
      Module.finrank K ((cechComplexLinear K (logFormsSheaf K E M b) 𝒰).homology q) =
        Module.finrank K
          (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (logFormsSheaf K E M b) q) := by
  obtain ⟨e⟩ := logFormsSheaf_nonempty_cechHomologyAddEquiv hnorm ξ hinj hξ E hEc hsnc M b 𝒰 h𝒰
    hcov q
  have := logFormsSheaf_cohomology_finite hnorm ξ hinj hξ E hEc hsnc M b q
  exact finite_finrank_eq_of_addEquiv ((cechComplexLinearHomologyAddEquiv K _ 𝒰 q).trans e)

variable (K) in
/-- **The logarithmic Čech–de Rham complex** of `Ω^•(log E)(p • M + Σ_k r_k • E_k)` in de Rham
degrees `≤ n`, as the iterated cone of the rows along the de Rham differential. -/
noncomputable def logCechDeRhamCone (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ} (𝒰 : Fin N → X.Opens) :
    CochainComplex (ModuleCat.{u} K) ℕ :=
  iteratedCone (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n 0

set_option linter.overlappingInstances false in
include hnorm hinj hξ hEc hsnc in
/-- **Hodge-to-de Rham bound:** the cohomology of the logarithmic Čech–de Rham complex in degree
`m` has dimension at most `Σ_{b ≤ n} h^{m-b}(Ω^b(log E)(p • M + Σ_k r_k • E_k))`. -/
theorem finrank_logCechDeRhamCone_homology_le [Finite K] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) (m : ℕ) :
    FiniteDimensional K ((logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).homology m) ∧
      Module.finrank K ((logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).homology m) ≤ logHodgeCount K E (p • M + ∑ k, rr k • E k) n m := by
  obtain ⟨h1, h2⟩ := finrank_iteratedCone_homology_le (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰)
    (fun b q => (finrank_cechComplexLinear_logForms_homology hnorm ξ hinj hξ E hEc hsnc _ b 𝒰 h𝒰
      hcov q).1) n 0 m
  refine ⟨h1, h2.trans ?_⟩
  rw [coneFiltrationBound, logHodgeCount, Nat.sub_zero, zero_add]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : b ≤ m
  · simp only [hb, ↓reduceIte]
    rw [zero_add]
    exact (finrank_cechComplexLinear_logForms_homology hnorm ξ hinj hξ E hEc hsnc _ b 𝒰 h𝒰 hcov
      (m - b)).2.le
  · simp only [hb, ↓reduceIte]
    exact Nat.zero_le _

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
include hnorm hinj hξ hEc hsnc in
/-- **The left-hand side of the logarithmic Deligne–Illusie inequality:** for `m ≥ n`,
`dim H^m(logDISource) = Σ_{b ≤ n} h^{m-b}(Ω^b(log E)(M))`. -/
theorem finrank_logDISource_homology [Finite K] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) {m : ℕ}
    (hm : n ≤ m) :
    FiniteDimensional K ((logDISource K E M 𝒰 n).homology m) ∧
      Module.finrank K ((logDISource K E M 𝒰 n).homology m) = logHodgeCount K E M n m := by
  obtain ⟨h1, h2⟩ := finrank_iteratedCone_zero_homology (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰)
    (fun b q => (finrank_cechComplexLinear_logForms_homology hnorm ξ hinj hξ E hEc hsnc M b 𝒰 h𝒰
      hcov q).1) n 0 m
  refine ⟨h1, h2.trans ?_⟩
  rw [coneFiltrationBound, logHodgeCount, Nat.sub_zero, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbm : b ≤ m := by
    rw [Finset.mem_range] at hb
    omega
  simp only [hbm, ↓reduceIte]
  rw [zero_add]
  exact (finrank_cechComplexLinear_logForms_homology hnorm ξ hinj hξ E hEc hsnc M b 𝒰 h𝒰 hcov
    (m - b)).2

/-- **The vertical map out of the top row vanishes:** `Ω^{n+1}(log E)(p • M + R) = 0`. -/
theorem logFormsCechDiffLinearMap_top_apply (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ} (𝒰 : Fin N → X.Opens) (q : ℕ)
    (z : (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) n) 𝒰).X q) :
    ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr n 𝒰).f q).hom z = 0 := by
  have hs : ∀ U : X.Opens, Subsingleton Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) (n + 1), U) := fun U =>
    logFormsSheaf_sections_subsingleton_of_lt c₀ E _ (Nat.lt_succ_self n) U
  have : Subsingleton (TopCat.Presheaf.CechCochain 𝒰
      (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (n + 1)).presheaf q) :=
    ⟨fun a b => funext fun x => @Subsingleton.elim _ (hs _) _ _⟩
  exact @Subsingleton.elim _ this _ _

set_option linter.overlappingInstances false in
include hnorm hinj hξ hEc hsnc in
/-- **The logarithmic Deligne–Illusie inequality from the staircase hypotheses**: an additive chain
map `⊕_b Č(Ω^b(log E)(M))[-b] → Čech–de Rham(Ω^•(log E)(p • M + R))` which does not raise the de
Rham degree and whose leading components `Φ_c` satisfy the Cartier condition on the Čech cochains
gives the logarithmic Deligne–Illusie inequality for `m > n`, over a finite field. -/
theorem logDeligneIllusieInequality_of_staircase [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤)
    (φ : ∀ m, (logDISource K E M 𝒰 n).X m →+ (logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).X m)
    (hφ : ∀ m x, φ (m + 1) (((logDISource K E M 𝒰 n).d m (m + 1)).hom x) =
      ((logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).d m (m + 1)).hom (φ m x))
    (htri : ∀ m c x, ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n c m x →
      ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n c m (φ m x))
    (Φ : ∀ c q, (cechComplexLinear K (logFormsSheaf K E M c) 𝒰).X q →+
      (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) c) 𝒰).X q)
    (hdiag : ∀ m c q (h : q + c = m) x,
      ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n c m x →
      coneRowComp (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n 0 c c q m (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x))
    (hcsurj0 : ∀ q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 0 𝒰).f q).hom z = 0 → ∃ y, z = Φ 0 q y)
    (hcsurj : ∀ c q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w)
    (hcinj0 : ∀ q y, Φ 0 q y = 0 → y = 0)
    (hcinj : ∀ c q y w, Φ (c + 1) q y = ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w → y = 0)
    {m : ℕ} (hm : n < m) : LogDeligneIllusieInequality K E M p rr n m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hinjS : ∀ x, ((logDISource K E M 𝒰 n).d (m + 1) (m + 1 + 1)).hom x = 0 →
      φ (m + 1) x ∈ LinearMap.range ((logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).d m (m + 1)).hom →
        x ∈ LinearMap.range ((logDISource K E M 𝒰 n).d m (m + 1)).hom := by
    rintro x hx ⟨y, hy⟩
    obtain ⟨s, hs⟩ := deligneIllusie_injective (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n φ hφ htri Φ hdiag hcsurj0
      hcsurj hcinj0 hcinj (fun q z => logFormsCechDiffLinearMap_top_apply hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰 q z)
      m x y hx hy.symm
    exact ⟨s, hs.symm⟩
  obtain ⟨_, hS⟩ := finrank_logDISource_homology hnorm ξ hinj hξ E hEc hsnc M 𝒰 h𝒰 hcov
    (m := m + 1) (by omega)
  obtain ⟨_, hTle⟩ := finrank_logCechDeRhamCone_homology_le hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰
    h𝒰 hcov (m + 1)
  have hST := (finrank_homology_succ_le_of_additive φ hφ m hinjS).2
  unfold LogDeligneIllusieInequality
  omega

variable (K) in
/-- **The data of the logarithmic Deligne–Illusie comparison** for `M` and `R = Σ_k r_k • E_k` on
the cover `𝒰`. -/
def LogDeligneIllusieStaircaseData (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ} (𝒰 : Fin N → X.Opens) : Prop :=
  ∃ (φ : ∀ m, (logDISource K E M 𝒰 n).X m →+ (logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).X m)
    (Φ : ∀ c q, (cechComplexLinear K (logFormsSheaf K E M c) 𝒰).X q →+
      (cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) c) 𝒰).X q),
    (∀ m x, φ (m + 1) (((logDISource K E M 𝒰 n).d m (m + 1)).hom x) = ((logCechDeRhamCone K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰).d m (m + 1)).hom (φ m x)) ∧
    (∀ m c x, ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n c m x →
      ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n c m (φ m x)) ∧
    (∀ m c q (h : q + c = m) x,
      ConeRowsLE (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n c m x →
      coneRowComp (fun b => cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰) (fun b => logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) (fun b => logFormsCechDiffLinearMap_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰) n 0 c c q m (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp (fun b => cechComplexLinear K (logFormsSheaf K E M b) 𝒰) (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h
          x)) ∧
    (∀ q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 0 𝒰).f q).hom z = 0 → ∃ y, z = Φ 0 q y) ∧
    (∀ c q z, ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w) ∧
    (∀ q y, Φ 0 q y = 0 → y = 0) ∧
    (∀ c q y w, Φ (c + 1) q y = ((logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr c 𝒰).f q).hom w → y = 0)

set_option linter.overlappingInstances false in
include hnorm hinj hξ hEc hsnc in
/-- **The logarithmic Deligne–Illusie inequality from the comparison data.** -/
theorem logDeligneIllusieInequality_of_staircaseData [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤)
    (hdata : LogDeligneIllusieStaircaseData K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰) {m : ℕ} (hm : n < m) :
    LogDeligneIllusieInequality K E M p rr n m := by
  obtain ⟨φ, Φ, hφ, htri, hdiag, hsurj0, hsurj, hinj0, hinj'⟩ := hdata
  exact logDeligneIllusieInequality_of_staircase hnorm ξ hinj hξ E hEc hsnc p c₀ M rr 𝒰 h𝒰 hcov φ
    hφ htri Φ hdiag hsurj0 hsurj hinj0 hinj' hm

end Cohomology

end MixedFujita

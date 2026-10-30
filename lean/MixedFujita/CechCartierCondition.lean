/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartCartierDegreeZero
public import MixedFujita.DeligneIllusieHomologyInjective

/-!
The Cartier condition on Čech cochains (step 10).

Let the cover consist of étale charts `cs i`. A Čech intersection `U_x` is an open affine part of
the chart of its first index, hence an étale chart itself (`cechEtaleChart`, check 420). Given on
every `U_x` a mod-`p²` Frobenius lift of `Γ(U_x)` and an equation `g_x` of `D`, the twisted
Deligne–Illusie maps of check 437 act componentwise on the Čech cochains
(`cechTwistedFrobeniusLift`, additive), and the Cartier isomorphism of checks 437 and 441 holds
componentwise: a cochain of closed forms of `Ω^{c+1}(p • D)` is `Φ y + d w`
(`cechTwistedFrobeniusLift_surj`), `Φ y` is exact only for `y = 0`
(`cechTwistedFrobeniusLift_inj`), and in degree `0` a cochain of closed functions is `Φ y` and
`Φ` is injective (`cechTwistedFrobeniusLift_surj_zero`, `cechTwistedFrobeniusLift_inj_zero`).
These are the four Cartier conditions of `DeligneIllusieStaircaseData` (check 440).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower sectionsBaseModule

section Chart

variable {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))

/-- **The étale chart on a Čech intersection**, restricted from the chart of its first index. -/
noncomputable def cechEtaleChart (q : ℕ) (x : Fin (q + 1) → Fin N) : EtaleChart K X n :=
  etaleChartRestrict (cs (x 0)) (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) (haff q x)
    (hne q x) (TopCat.Presheaf.cechOpen_le _ x 0)

omit [IsIntegral X] in
theorem cechEtaleChart_U (q : ℕ) (x : Fin (q + 1) → Fin N) :
    (cechEtaleChart cs haff hne q x).U = TopCat.Presheaf.cechOpen (fun i => (cs i).U) x := rfl

end Chart

section Lift

variable {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (L : ∀ q, (Fin (q + 1) → Fin N) → Type u) [∀ q x, CommRing (L q x)]
  (π : ∀ q x, L q x →+* Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hπ : ∀ q x, Function.Surjective (π q x)) (p : ℕ) [Fact p.Prime] [CharP K p]
  (F : ∀ q x, L q x →+* L q x) (hF : ∀ q x y, π q x (F q x y) = π q x y ^ p)
  (hker : ∀ q x y, π q x y = 0 → ∃ z, y = (p : L q x) * z)
  {D : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
    D.IsLocalEquationAt y (g q x))

theorem twistedChartFrobeniusLiftForms_zero (c : EtaleChart K X n) {L' : Type u} [CommRing L']
    (π' : L' →+* Γ(X, c.U)) (hπ' : Function.Surjective π') (F' : L' →+* L')
    (hF' : ∀ x, π' (F' x) = π' x ^ p) (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z)
    {g' : X.functionFieldˣ} (hg' : ∀ x ∈ c.U, D.IsLocalEquationAt x g') (b : ℕ) :
    twistedChartFrobeniusLiftForms c π' hπ' p F' hF' hker' hg' b 0 = 0 := by
  have h := twistedChartFrobeniusLiftForms_add c π' hπ' p F' hF' hker' hg' b 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- **The twisted Deligne–Illusie maps on the Čech cochains**, componentwise. -/
noncomputable def cechTwistedFrobeniusLift (c q : ℕ) :
    (cechComplexLinear K (twistedFormsSheaf K D c) (fun i => (cs i).U)).X q →+
      (cechComplexLinear K (twistedFormsSheaf K (p • D) c) (fun i => (cs i).U)).X q where
  toFun y := fun x => twistedChartFrobeniusLiftForms (cechEtaleChart cs haff hne q x) (π q x)
    (hπ q x) p (F q x) (hF q x) (hker q x) (hg q x) c (y x)
  map_zero' := funext fun x => twistedChartFrobeniusLiftForms_zero p
    (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) (F q x) (hF q x) (hker q x) (hg q x) c
  map_add' y y' := funext fun x => twistedChartFrobeniusLiftForms_add
    (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p (F q x) (hF q x) (hker q x) (hg q x) c
    (y x) (y' x)

theorem cechTwistedFrobeniusLift_apply (c q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D c) (fun i => (cs i).U)).X q)
    (x : Fin (q + 1) → Fin N) :
    cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg c q y x =
      twistedChartFrobeniusLiftForms (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p (F q x)
        (hF q x) (hker q x) (hg q x) c (y x) := rfl

omit [Fact p.Prime] in
theorem twistedFormsDiffApp_of_nonempty (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) (U : X.Opens) [h : Nonempty U]
    (s : Γ(twistedFormsSheaf K (p • D) b, U)) :
    twistedFormsDiffApp p c₀ hcover D b U s = twistedFormsDiff p c₀ hcover D b U s := by
  unfold twistedFormsDiffApp
  split
  · rfl
  · contradiction

omit [Fact p.Prime] in
theorem twistedFormsCechDiffLinearMap_f_apply (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b q : ℕ) {M : ℕ}
    (𝒰 : Fin M → X.Opens) (w : (cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰).X q)
    (x : Fin (q + 1) → Fin M) :
    ((twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰).f q).hom w x =
      twistedFormsDiffApp p c₀ hcover D b (TopCat.Presheaf.cechOpen 𝒰 x) (w x) := rfl

variable (hann : ∀ q x z, (p : L q x) * z = 0 → π q x z = 0) (hp2 : ∀ q x, (p : L q x) * p = 0)
  (hK : ∀ q x (a : K), ∃ a' : L q x,
    π q x a' = algebraMap K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) a ∧
      F q x a' = a' ^ p)
  (hy0 : ∀ q x (j : Fin n), etaleCoordFun (cechEtaleChart cs haff hne q x).coords j ≠ 0)
  (hft : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)

include hann hp2 hK hy0 hft in
/-- **Cartier condition, surjectivity**: a Čech cochain of closed forms of `Ω^{c+1}(p • D)` is
`Φ y + d w`. -/
theorem cechTwistedFrobeniusLift_surj [PerfectRing K p] (c q : ℕ)
    (z : (cechComplexLinear K (twistedFormsSheaf K (p • D) (c + 1)) (fun i => (cs i).U)).X q)
    (hz : ((twistedFormsCechDiffLinearMap p c₀ hcover D (c + 1) (fun i => (cs i).U)).f q).hom z =
      0) :
    ∃ y w, z = cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg (c + 1) q y +
      ((twistedFormsCechDiffLinearMap p c₀ hcover D c (fun i => (cs i).U)).f q).hom w := by
  have hcomp : ∀ x : Fin (q + 1) → Fin N, ∃ (yx : twistedFormsSections K D (c + 1)
      (cechEtaleChart cs haff hne q x).U) (wx : twistedFormsSections K (p • D) c
      (cechEtaleChart cs haff hne q x).U),
      z x = twistedChartFrobeniusLiftForms (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p
        (F q x) (hF q x) (hker q x) (hg q x) (c + 1) yx +
        twistedFormsDiff p c₀ hcover D c (cechEtaleChart cs haff hne q x).U wx := by
    intro x
    have : Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) := hne q x
    have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hft q x
    have hzx : twistedFormsDiff p c₀ hcover D (c + 1)
        (cechEtaleChart cs haff hne q x).U (z x) = 0 := by
      have h := congrFun hz x
      rw [twistedFormsCechDiffLinearMap_f_apply, twistedFormsDiffApp_of_nonempty] at h
      exact h
    exact twisted_chart_cartier_sections (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p
      (F q x) (hF q x) (hker q x) (hann q x) (hp2 q x) (hK q x) (hy0 q x) (hg q x) c₀ hcover c
      (z x) hzx
  choose y w hyw using hcomp
  refine ⟨y, w, funext fun x => ?_⟩
  have : Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) := hne q x
  rw [hyw x]
  change _ = cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg (c + 1) q y x +
    ((twistedFormsCechDiffLinearMap p c₀ hcover D c (fun i => (cs i).U)).f q).hom w x
  rw [twistedFormsCechDiffLinearMap_f_apply, twistedFormsDiffApp_of_nonempty]
  rfl

include hann hp2 hK hy0 hft in
/-- **Cartier condition, injectivity**: `Φ y` is exact only for `y = 0`. -/
theorem cechTwistedFrobeniusLift_inj [PerfectRing K p] (c q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D (c + 1)) (fun i => (cs i).U)).X q)
    (w : (cechComplexLinear K (twistedFormsSheaf K (p • D) c) (fun i => (cs i).U)).X q)
    (h : cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg (c + 1) q y =
      ((twistedFormsCechDiffLinearMap p c₀ hcover D c (fun i => (cs i).U)).f q).hom w) :
    y = 0 := by
  funext x
  have : Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) := hne q x
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hft q x
  have hx := congrFun h x
  rw [cechTwistedFrobeniusLift_apply, twistedFormsCechDiffLinearMap_f_apply,
    twistedFormsDiffApp_of_nonempty] at hx
  exact twistedChartFrobeniusLiftForms_eq_zero_of_exact (cechEtaleChart cs haff hne q x) (π q x)
    (hπ q x) p (F q x) (hF q x) (hker q x) (hann q x) (hp2 q x) (hK q x) (hy0 q x) (hg q x) c₀
    hcover c (y x) (w x) hx

include hann hp2 hK hy0 hft in
/-- **Cartier condition in degree `0`, surjectivity**: a Čech cochain of closed functions of
`Ω^0(p • D)` is `Φ y`. -/
theorem cechTwistedFrobeniusLift_surj_zero [PerfectRing K p] (q : ℕ)
    (z : (cechComplexLinear K (twistedFormsSheaf K (p • D) 0) (fun i => (cs i).U)).X q)
    (hz : ((twistedFormsCechDiffLinearMap p c₀ hcover D 0 (fun i => (cs i).U)).f q).hom z = 0) :
    ∃ y, z = cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg 0 q y := by
  have hcomp : ∀ x : Fin (q + 1) → Fin N, ∃ yx : twistedFormsSections K D 0
      (cechEtaleChart cs haff hne q x).U,
      z x = twistedChartFrobeniusLiftForms (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p
        (F q x) (hF q x) (hker q x) (hg q x) 0 yx := by
    intro x
    have : Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) := hne q x
    have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hft q x
    have hzx : twistedFormsDiff p c₀ hcover D 0
        (cechEtaleChart cs haff hne q x).U (z x) = 0 := by
      have h := congrFun hz x
      rw [twistedFormsCechDiffLinearMap_f_apply, twistedFormsDiffApp_of_nonempty] at h
      exact h
    exact twisted_chart_cartier_sections_zero (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p
      (F q x) (hF q x) (hker q x) (hann q x) (hp2 q x) (hK q x) (hy0 q x) (hg q x) c₀ hcover
      (z x) hzx
  choose y hy using hcomp
  exact ⟨y, funext hy⟩

include hann hp2 hK hy0 hft in
/-- **Cartier condition in degree `0`, injectivity.** -/
theorem cechTwistedFrobeniusLift_inj_zero [PerfectRing K p] (q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D 0) (fun i => (cs i).U)).X q)
    (h : cechTwistedFrobeniusLift cs haff hne L π hπ p F hF hker g hg 0 q y = 0) : y = 0 := by
  funext x
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hft q x
  have hx := congrFun h x
  rw [cechTwistedFrobeniusLift_apply] at hx
  exact twistedChartFrobeniusLiftForms_eq_zero (cechEtaleChart cs haff hne q x) (π q x) (hπ q x) p
    (F q x) (hF q x) (hker q x) (hann q x) (hp2 q x) (hK q x) (hy0 q x) (hg q x) 0 (y x) hx

end Lift

end MixedFujita

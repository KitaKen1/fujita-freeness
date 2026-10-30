/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechDeligneIllusieRelations
public import MixedFujita.IteratedConeAssembly
public import MixedFujita.CechCartierCondition

/-!
The Deligne–Illusie comparison data from lifts on the Čech intersections (step 10).

From the Deligne–Illusie map `Ψ'^{b,a}` on Čech cochains (checks 464 and 465), the components
`Ψ_{b → i} = Ψ'^{b, b - i}` for `i ≤ b` and `0` for `i > b` (`cechDIComponent`) satisfy the
relations of check 445: they do not raise the row, the diagonal values are closed
(`cechDIComponent_closed`), and the relations (H3) and (H2) hold
(`cechDIComponent_relation_zero`, `cechDIComponent_relation_succ`). In Čech degree `0` the diagonal
is `b! · Φ`, with `Φ` the twisted Frobenius lift of check 442 at the first vertex
(`cechDIComponent_diag`). For `b ≤ n < p`, `b!` is a unit modulo `p`
(`factorial_mul_gcdA_add_mul_gcdB`) and the Čech cochains are `p`-torsion, so the Cartier
conditions of check 442 transfer to the diagonal; for `b > n` the cochains vanish (check 429).
Hence the comparison data of check 440 exist (`deligneIllusieStaircaseData_of_cechLifts`), and
over a finite field of characteristic `p > n`, Kodaira-type vanishing `H^j(O(K_X + D)) = 0`
(`j ≥ 1`, `D` ample) follows from lifting data on the Čech intersections
(`canonical_vanishing_of_cechLifts`; the equations of `p^k • D` are the `p^k`-th powers).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

section Unit

/-- **`c!` is a unit modulo `p` for `c < p`**: its Bézout coefficients with `p`. -/
theorem factorial_mul_gcdA_add_mul_gcdB {p c : ℕ} (hp : p.Prime) (hc : c < p) :
    (c.factorial : ℤ) * Nat.gcdA c.factorial p + (p : ℤ) * Nat.gcdB c.factorial p = 1 := by
  have hcop : Nat.Coprime c.factorial p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => by
      rw [hp.dvd_factorial] at h
      omega).symm
  rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]

variable {T : Type*} [AddCommGroup T]

theorem factorial_gcdA_zsmul {p c : ℕ} (hp : p.Prime) (hc : c < p)
    (hT : ∀ v : T, (p : ℤ) • v = 0) (v : T) :
    ((c.factorial : ℤ) * Nat.gcdA c.factorial p) • v = v := by
  have h := factorial_mul_gcdA_add_mul_gcdB hp hc
  rw [show (c.factorial : ℤ) * Nat.gcdA c.factorial p = 1 + (-Nat.gcdB c.factorial p) * p by
      linear_combination h,
    add_smul, one_smul, mul_smul, hT, smul_zero, add_zero]

theorem eq_zero_of_factorial_zsmul_eq_zero {p c : ℕ} (hp : p.Prime) (hc : c < p)
    (hT : ∀ v : T, (p : ℤ) • v = 0) {v : T} (h : (c.factorial : ℤ) • v = 0) : v = 0 := by
  rw [← factorial_gcdA_zsmul hp hc hT v, mul_comm, mul_smul, h, smul_zero]

end Unit

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The `K`-linear Čech cochains are `p`-torsion in characteristic `p`. -/
theorem cechComplexLinear_natCast_zsmul (p : ℕ) [CharP K p] (M : X.Modules) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (q : ℕ) (w : (cechComplexLinear K M 𝒰).X q) : (p : ℤ) • w = 0 := by
  rw [← Int.cast_smul_eq_zsmul K, Int.cast_natCast, CharP.cast_eq_zero, zero_smul]

theorem cechComplexLinear_d_apply (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) (m : ℕ)
    (z : (cechComplexLinear K M 𝒰).X m) :
    ((cechComplexLinear K M 𝒰).d m (m + 1)).hom z = TopCat.Presheaf.cechD 𝒰 M.presheaf m z := by
  rw [cechComplexLinear_d]
  rfl

variable [IsIntegral X]

section Cech

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
  {D : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
    D.IsLocalEquationAt y (g q x))

/-- **The components of the Deligne–Illusie comparison** (check 445):
`Ψ_{b → i} = Ψ'^{b, b - i}` for `i ≤ b`, and `0` for `i > b`. -/
noncomputable def cechDIComponent (b i q q' : ℕ) (h : q + b = q' + i) :
    (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q →+
      (cechComplexLinear K (twistedFormsSheaf K (p • D) i) (fun i => (cs i).U)).X q' :=
  if hi : i ≤ b then
    cechDIMap cs haff hne L π hπ p F hF hker g hg b i (b - i) (by omega) q q' (by omega)
  else 0

theorem cechDIMap_congr_degree (b i a a' : ℕ) (ha : a = a') (h : i + a = b) (h' : i + a' = b)
    (q q' : ℕ) (hq : q + a = q') (hq' : q + a' = q') :
    cechDIMap cs haff hne L π hπ p F hF hker g hg b i a h q q' hq =
      cechDIMap cs haff hne L π hπ p F hF hker g hg b i a' h' q q' hq' := by
  subst ha
  rfl

theorem cechDIComponent_eq (b i a q q' : ℕ) (h : q + b = q' + i) (hi : i + a = b)
    (hq : q + a = q') :
    cechDIComponent cs haff hne L π hπ p F hF hker g hg b i q q' h =
      cechDIMap cs haff hne L π hπ p F hF hker g hg b i a hi q q' hq := by
  rw [cechDIComponent, dite_eq_left (by omega)]
  exact cechDIMap_congr_degree cs haff hne L π hπ p F hF hker g hg b i _ a (by omega) _ hi q q' _ hq

/-- **The components do not raise the row.** -/
theorem cechDIComponent_of_lt (b i q q' : ℕ) (h : q + b = q' + i) (hb : b < i) :
    cechDIComponent cs haff hne L π hπ p F hF hker g hg b i q q' h = 0 := by
  rw [cechDIComponent, dite_eq_right (by omega)]

theorem cechDIComponent_apply_diag (b q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q)
    (x : Fin (q + 1) → Fin N) :
    cechDIComponent cs haff hne L π hπ p F hF hker g hg b b q q rfl y x =
      (b.factorial : ℤ) • twistedChartFrobeniusLiftForms (cechEtaleChart cs haff hne q x) (π q x)
        (hπ q x) p (F q x 0) (hF q x 0) (hker q x) (hg q x) b (y x) := by
  rw [cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg b b 0 q q rfl (add_zero b)
    (add_zero q)]
  refine (cechDIMap_apply cs haff hne L π hπ p F hF hker g hg b b 0 (add_zero b) q q (add_zero q) y
    x).trans ?_
  have hx : x ∘ cechBack 0 q q (add_zero q) = x := funext fun t =>
    congrArg x (Fin.ext (by simp [cechBack_val]))
  have hres : (twistedFormsSheaf K D b).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp
      (fun i => (cs i).U) x (cechBack 0 q q (add_zero q)))).op (y (x ∘ cechBack 0 q q (add_zero q))) =
      y x := by
    rw [cech_restrict_congr y hx _ le_rfl]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  rw [zero_mul, pow_zero, one_smul, twistedChartDIComponent_zero, hres,
    show cechFront q 0 = 0 from Fin.ext (by simp [cechFront_val])]

/-- **In Čech degree `0` the diagonal component is `b! · Φ`**, with `Φ` the twisted Frobenius
lift of check 442 at the first vertex. -/
theorem cechDIComponent_diag (b q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q) :
    cechDIComponent cs haff hne L π hπ p F hF hker g hg b b q q rfl y =
      (b.factorial : ℤ) • cechTwistedFrobeniusLift cs haff hne L π hπ p (fun q x => F q x 0)
        (fun q x => hF q x 0) hker g hg b q y :=
  funext fun x => cechDIComponent_apply_diag cs haff hne L π hπ p F hF hker g hg b q y x

variable (R : ∀ q (x : Fin (q + 2) → Fin N) (k : Fin (q + 2)),
    L q (x ∘ Fin.succAbove k) →+* L (q + 1) x)
  (hR : ∀ q x k z, π (q + 1) x (R q x k z) =
    (X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs i).U) x
      (Fin.succAbove k))).op).hom (π q (x ∘ Fin.succAbove k) z))
  (hRF : ∀ q x k j z, R q x k (F q (x ∘ Fin.succAbove k) j z) =
    F (q + 1) x (Fin.succAbove k j) (R q x k z))
  (hann : ∀ q x z, (p : L q x) * z = 0 → π q x z = 0) (hp2 : ∀ q x, (p : L q x) * p = 0)
  (hK : ∀ q x (k : K), ∃ k' : L q x,
    π q x k' = algebraMap K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) k ∧
      ∀ j, F q x j k' = k' ^ p)
  (hft : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)

include hann hp2 hK hft in
/-- **The diagonal values are closed.** -/
theorem cechDIComponent_closed (b q q' : ℕ) (h : q + b = q' + b)
    (y : (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q) :
    ((twistedFormsCechDiffLinearMap p c₀ hcover D b (fun i => (cs i).U)).f q').hom
      (cechDIComponent cs haff hne L π hπ p F hF hker g hg b b q q' h y) = 0 := by
  obtain rfl : q = q' := by omega
  rw [cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg b b 0 q q h (add_zero b) (add_zero q)]
  funext x
  have := hne q x
  rw [twistedFormsCechDiffLinearMap_f_apply, twistedFormsDiffApp_of_nonempty]
  exact twistedFormsDiff_cechDIMap_zero cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀
    hcover b q y x

include hR hRF hann hp2 hK hft in
/-- **The relation (H3) for the components**: `δ Ψ_{b → 0} = Ψ_{b → 0} δ`. -/
theorem cechDIComponent_relation_zero (b q q' : ℕ) (h : q + b = q' + 0)
    (h' : q + 1 + b = q' + 1 + 0)
    (y : (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q) :
    ((cechComplexLinear K (twistedFormsSheaf K (p • D) 0) (fun i => (cs i).U)).d q' (q' + 1)).hom
        (cechDIComponent cs haff hne L π hπ p F hF hker g hg b 0 q q' h y) =
      cechDIComponent cs haff hne L π hπ p F hF hker g hg b 0 (q + 1) (q' + 1) h'
        (((cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).d q (q + 1)).hom y) := by
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply,
    cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg b 0 b q q' h (zero_add b) (by omega),
    cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg b 0 b (q + 1) (q' + 1) h' (zero_add b)
      (by omega)]
  funext x
  exact cechDIMap_relation_top cs haff hne L π hπ p F hF hker g hg R hR hRF hann hp2 hK hft b q q'
    (by omega) y x

include hR hRF hann hp2 hK hft in
/-- **The relation (H2) for the components**:
`δ Ψ_{b → i+1} + (-1)^{q'+1} d Ψ_{b → i} = Ψ_{b → i+1} δ`. -/
theorem cechDIComponent_relation_succ (b i q q' : ℕ) (h : q + b = q' + (i + 1))
    (h' : q + b = q' + 1 + i) (h'' : q + 1 + b = q' + 1 + (i + 1))
    (y : (cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).X q) :
    ((cechComplexLinear K (twistedFormsSheaf K (p • D) (i + 1)) (fun i => (cs i).U)).d q'
          (q' + 1)).hom (cechDIComponent cs haff hne L π hπ p F hF hker g hg b (i + 1) q q' h y) +
        ((-1 : ℤ) ^ (q' + 1)) • ((twistedFormsCechDiffLinearMap p c₀ hcover D i
          (fun i => (cs i).U)).f (q' + 1)).hom
          (cechDIComponent cs haff hne L π hπ p F hF hker g hg b i q (q' + 1) h' y) =
      cechDIComponent cs haff hne L π hπ p F hF hker g hg b (i + 1) (q + 1) (q' + 1) h''
        (((cechComplexLinear K (twistedFormsSheaf K D b) (fun i => (cs i).U)).d q (q + 1)).hom y) := by
  rw [cechComplexLinear_d_apply, cechComplexLinear_d_apply]
  rcases lt_trichotomy i b with hib | hib | hib
  · obtain ⟨a, rfl⟩ : ∃ a, b = i + 1 + a := ⟨b - (i + 1), by omega⟩
    rw [cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg (i + 1 + a) (i + 1) a q q' h rfl
        (by omega),
      cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg (i + 1 + a) i (a + 1) q (q' + 1) h'
        (by omega) (by omega),
      cechDIComponent_eq cs haff hne L π hπ p F hF hker g hg (i + 1 + a) (i + 1) a (q + 1) (q' + 1)
        h'' rfl (by omega)]
    funext x
    exact cechDIMap_relation cs haff hne L π hπ p F hF hker g hg R hR hRF hann hp2 hK hft c₀ hcover
      (i + 1 + a) i a rfl (by omega) q q' (by omega) y x
  · subst hib
    rw [cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg _ _ q q' h (by omega),
      cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg _ _ (q + 1) (q' + 1) h'' (by omega),
      cechDIComponent_closed cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀ hcover _ q
        (q' + 1) h' y]
    simp
  · rw [cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg b (i + 1) q q' h (by omega),
      cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg b i q (q' + 1) h' hib,
      cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg b (i + 1) (q + 1) (q' + 1) h''
        (by omega)]
    simp

variable (hy0 : ∀ q x (j : Fin n), etaleCoordFun (cechEtaleChart cs haff hne q x).coords j ≠ 0)

include hann hp2 hK hy0 hft in
/-- **Cartier condition in degree `0`, surjectivity**, for the diagonal component. -/
theorem cechDIComponent_surj_zero [PerfectRing K p] (q : ℕ)
    (z : (cechComplexLinear K (twistedFormsSheaf K (p • D) 0) (fun i => (cs i).U)).X q)
    (hz : ((twistedFormsCechDiffLinearMap p c₀ hcover D 0 (fun i => (cs i).U)).f q).hom z = 0) :
    ∃ y, z = cechDIComponent cs haff hne L π hπ p F hF hker g hg 0 0 q q rfl y := by
  obtain ⟨y, rfl⟩ := cechTwistedFrobeniusLift_surj_zero cs haff hne L π hπ p (fun q x => F q x 0)
    (fun q x => hF q x 0) hker g hg hann hp2 (fun q x k => (hK q x k).imp fun _ hk => ⟨hk.1, hk.2 0⟩)
    hy0 hft c₀ hcover q z hz
  exact ⟨y, by rw [cechDIComponent_diag, Nat.factorial_zero, Nat.cast_one, one_smul]⟩

include hann hp2 hK hy0 hft in
/-- **Cartier condition in degree `0`, injectivity**, for the diagonal component. -/
theorem cechDIComponent_inj_zero [PerfectRing K p] (q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D 0) (fun i => (cs i).U)).X q)
    (h : cechDIComponent cs haff hne L π hπ p F hF hker g hg 0 0 q q rfl y = 0) : y = 0 := by
  rw [cechDIComponent_diag, Nat.factorial_zero, Nat.cast_one, one_smul] at h
  exact cechTwistedFrobeniusLift_inj_zero cs haff hne L π hπ p (fun q x => F q x 0)
    (fun q x => hF q x 0) hker g hg hann hp2 (fun q x k => (hK q x k).imp fun _ hk => ⟨hk.1, hk.2 0⟩)
    hy0 hft q y h

include hann hp2 hK hy0 hft in
/-- **Cartier condition, surjectivity**, for the diagonal component (`p > n`): `(c + 1)!` is a
unit modulo `p` in the degrees `c + 1 ≤ n`, and the cochains vanish above `n`. -/
theorem cechDIComponent_surj [PerfectRing K p] (hpn : n < p) (c q : ℕ)
    (z : (cechComplexLinear K (twistedFormsSheaf K (p • D) (c + 1)) (fun i => (cs i).U)).X q)
    (hz : ((twistedFormsCechDiffLinearMap p c₀ hcover D (c + 1) (fun i => (cs i).U)).f q).hom z =
      0) :
    ∃ y w, z = cechDIComponent cs haff hne L π hπ p F hF hker g hg (c + 1) (c + 1) q q rfl y +
      ((twistedFormsCechDiffLinearMap p c₀ hcover D c (fun i => (cs i).U)).f q).hom w := by
  rcases le_or_gt (c + 1) n with hc | hc
  · obtain ⟨y, w, rfl⟩ := cechTwistedFrobeniusLift_surj cs haff hne L π hπ p (fun q x => F q x 0)
      (fun q x => hF q x 0) hker g hg hann hp2
      (fun q x k => (hK q x k).imp fun _ hk => ⟨hk.1, hk.2 0⟩) hy0 hft c₀ hcover c q z hz
    refine ⟨Nat.gcdA (c + 1).factorial p • y, w, ?_⟩
    rw [cechDIComponent_diag, map_zsmul, smul_smul,
      factorial_gcdA_zsmul (Fact.out : p.Prime) (by omega)
        (cechComplexLinear_natCast_zsmul p _ _ q)]
  · have hsub : ∀ w : (cechComplexLinear K (twistedFormsSheaf K (p • D) (c + 1))
        (fun i => (cs i).U)).X q, w = 0 := fun w => funext fun x =>
      @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton_of_lt c₀ (p • D) hc _) _ _
    exact ⟨0, 0, (hsub z).trans (hsub _).symm⟩

include hann hp2 hK hy0 hft in
/-- **Cartier condition, injectivity**, for the diagonal component (`p > n`). -/
theorem cechDIComponent_inj [PerfectRing K p] (hpn : n < p) (c q : ℕ)
    (y : (cechComplexLinear K (twistedFormsSheaf K D (c + 1)) (fun i => (cs i).U)).X q)
    (w : (cechComplexLinear K (twistedFormsSheaf K (p • D) c) (fun i => (cs i).U)).X q)
    (h : cechDIComponent cs haff hne L π hπ p F hF hker g hg (c + 1) (c + 1) q q rfl y =
      ((twistedFormsCechDiffLinearMap p c₀ hcover D c (fun i => (cs i).U)).f q).hom w) :
    y = 0 := by
  rcases le_or_gt (c + 1) n with hc | hc
  · rw [cechDIComponent_diag, ← map_zsmul] at h
    exact eq_zero_of_factorial_zsmul_eq_zero (Fact.out : p.Prime) (by omega)
      (cechComplexLinear_natCast_zsmul p _ _ q)
      (cechTwistedFrobeniusLift_inj cs haff hne L π hπ p (fun q x => F q x 0) (fun q x => hF q x 0)
        hker g hg hann hp2 (fun q x k => (hK q x k).imp fun _ hk => ⟨hk.1, hk.2 0⟩) hy0 hft c₀
        hcover c q _ w h)
  · exact funext fun x =>
      @Subsingleton.elim _ (twistedFormsSheaf_sections_subsingleton_of_lt c₀ D hc _) _ _

include hπ hF hker g hg hR hRF hann hp2 hK hy0 hft in
/-- **The Deligne–Illusie comparison data from lifts on the Čech intersections** (`p > n`). -/
theorem deligneIllusieStaircaseData_of_cechLifts [PerfectRing K p] (hpn : n < p) :
    DeligneIllusieStaircaseData K p c₀ hcover D (fun i => (cs i).U) :=
  deligneIllusieStaircaseData_of_components p c₀ hcover D (fun i => (cs i).U)
    (cechDIComponent cs haff hne L π hπ p F hF hker g hg)
    (fun b i q q' h hb => cechDIComponent_of_lt cs haff hne L π hπ p F hF hker g hg b i q q' h hb)
    (fun b q q' h y => cechDIComponent_closed cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀
      hcover b q q' h y)
    (fun b q q' h h' y => cechDIComponent_relation_zero cs haff hne L π hπ p F hF hker g hg R hR hRF
      hann hp2 hK hft b q q' h h' y)
    (fun b i q q' h h' h'' y => cechDIComponent_relation_succ cs haff hne L π hπ p F hF hker g hg R
      hR hRF hann hp2 hK hft c₀ hcover b i q q' h h' h'' y)
    (fun q z hz => cechDIComponent_surj_zero cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀
      hcover hy0 q z hz)
    (fun c q z hz => cechDIComponent_surj cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀
      hcover hy0 hpn c q z hz)
    (fun q y h => cechDIComponent_inj_zero cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft hy0 q
      y h)
    (fun c q y w h => cechDIComponent_inj cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀
      hcover hy0 hpn c q y w h)

include hπ hF hker hg hR hRF hann hp2 hK hy0 hft in
/-- **Kodaira-type vanishing from lifts on the Čech intersections**: over a finite field of
characteristic `p > n`, lifting data modulo `p²` on the Čech intersections of a cover by étale
charts give `H^j(O(K_X + D)) = 0` for `j ≥ 1` and ample `D` (the data for `p^k • D` use the
equations `g^{p^k}`). -/
theorem canonical_vanishing_of_cechLifts [Finite K] [PerfectRing K p]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hpn : n < p) (hD : CartierIsAmpleProj K D) (hcov : ⨆ i, (cs i).U = ⊤) {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + D).sheaf j) :=
  canonical_vanishing_of_staircaseData p (Fact.out : p.Prime).two_le c₀ hcover D hD
    (fun i => (cs i).U) (fun i => (cs i).isAffine) hcov
    (fun k => deligneIllusieStaircaseData_of_cechLifts cs haff hne L π hπ p F hF hker
      (fun q x => g q x ^ p ^ k) (fun q x y hy => isLocalEquationAt_nsmul_pow (hg q x y hy) (p ^ k))
      R hR hRF hann hp2 hK hft c₀ hcover hy0 hpn) hj

end Cech

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedFormsRestrictedBound
public import MixedFujita.ProjectiveDegreeCoprime
public import MixedFujita.ProjectiveFormHilbertLimit
public import MixedFujita.PointClosureHyperplaneEquivalence

/-!
The numerical bound for sums of ample divisors with two coprime very ample multiples (step 4).
Call A coprime-ample if k A and k' A are very ample in the projective sense for coprime
k, k' ≥ 1. On a projective variety this is ampleness, since all large multiples of an ample
divisor are very ample; that classical bridge is the only input not proved here.

Let L_1, …, L_s be coprime-ample on an integral scheme X locally of finite type over an
algebraically closed field, and W the closure of a point, of dimension d ≥ 1. Then for every
ε > 0 and large j the sections of j Σ L_i restrict to W with dimension at least
(s^d - ε) j^d / d!: this is (Σ L_i)^d · W ≥ s^d, in the form used by S-NF.

For each i the embeddings by k_i L_i and k'_i L_i restrict to W, and the linear equivalence
k'_i J_i ∼ k_i J'_i of their hyperplane divisors restricts too. The two Hilbert asymptotics on W
then give r_i k'_i^d = r'_i k_i^d for the degrees, so k_i^d divides r_i and r_i ≥ k_i^d: this is
L_i^d · W ≥ 1, the integrality of the intersection number, obtained without Snapper polynomials,
Serre vanishing or intersection theory. The restricted forms of degree q of the i-th embedding
therefore number at least (k_i^d - ε') q^d / d!, the mixed Brunn–Minkowski bound adds the d-th
roots, and a representation j = a k_i + b k'_i with b < k_i pads the multidegree to j L_i with
chart sections of both embeddings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

section Numerics

/-- For coprime k, k' with k ≥ 1 and j ≥ k k': j = a k + b k' with b < k. -/
theorem exists_coprime_representation {k k' : ℕ} (hk : 1 ≤ k) (hcop : Nat.Coprime k k') {j : ℕ}
    (hj : k * k' ≤ j) : ∃ a b : ℕ, a * k + b * k' = j ∧ b < k := by
  obtain ⟨a, b, h⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le k k' j
    (by rw [Nat.Coprime.gcd_eq_one hcop]; exact one_dvd j)
    (le_trans (Nat.mul_le_mul (Nat.pred_le k) (Nat.pred_le k')) hj)
  refine ⟨a + b / k * k', b % k, ?_, Nat.mod_lt b (by omega)⟩
  have hb := Nat.div_add_mod b k
  calc (a + b / k * k') * k + b % k * k' = a * k + (k * (b / k) + b % k) * k' := by ring
    _ = a * k + b * k' := by rw [hb]
    _ = j := h

/-- A factor 1 - δ is absorbed by ε. -/
theorem exists_delta_pow_sub_lt (s : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ s ^ d - ε < (s * (1 - δ)) ^ d := by
  have hcont : Continuous fun δ : ℝ => (s * (1 - δ)) ^ d := by fun_prop
  have h0 : s ^ d - ε < (fun δ : ℝ => (s * (1 - δ)) ^ d) 0 := by
    simp only [sub_zero, mul_one]
    linarith
  have hev := hcont.continuousAt.eventually (lt_mem_nhds h0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min (r / 2) (1 / 2), lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), hball ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by positivity) (by norm_num))]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- For k ≥ 1 and 0 ≤ δ ≤ 1: (k (1 - δ))^n ≤ k^n - (1 - (1 - δ)^n). -/
theorem mul_one_sub_pow_le {k δ : ℝ} (hk : 1 ≤ k) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    (k * (1 - δ)) ^ n ≤ k ^ n - (1 - (1 - δ) ^ n) := by
  have h1 : (1 : ℝ) ≤ k ^ n := one_le_pow₀ hk
  have h2 : (1 - δ) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  rw [mul_pow]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

end Numerics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Definition

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Ampleness through two coprime very ample multiples: k A and k' A are very ample in the
projective sense for coprime k, k' ≥ 1. -/
def CartierIsAmpleCoprime (A : CartierDivisor Y) : Prop :=
  ∃ k k' : ℕ, 1 ≤ k ∧ 1 ≤ k' ∧ Nat.Coprime k k' ∧
    CartierIsVeryAmpleProj K (k • A) ∧ CartierIsVeryAmpleProj K (k' • A)

variable {K}

/-- A coprime-ample divisor is ample in the projective sense. -/
theorem cartierIsAmpleProj_of_ampleCoprime {A : CartierDivisor Y}
    (hA : CartierIsAmpleCoprime K A) : CartierIsAmpleProj K A := by
  obtain ⟨k, k', hk, -, -, ⟨n, e, he, hbase, g, hg, hggen, f, hAf⟩, -⟩ := hA
  exact ⟨k, hk, n, e, he, hbase, g, hg, hggen, f, hAf⟩

/-- A very ample divisor is coprime-ample. -/
theorem cartierIsAmpleCoprime_of_veryAmple {A : CartierDivisor Y}
    (hA : CartierIsVeryAmpleProj K A) : CartierIsAmpleCoprime K A :=
  ⟨1, 1, le_rfl, le_rfl, Nat.coprime_one_left 1, by rwa [one_smul], by rwa [one_smul]⟩

end Definition

section Degree

variable {K : Type u} [Field K] [Infinite K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] {n n' : ℕ}
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
  (e' : Y ⟶ polynomialProjectiveScheme n' K) [IsClosedImmersion e']
  (g' : MvPolynomial (Fin n') K) (hg' : g'.IsHomogeneous 1)
  (hggen' : g' ∉ (e' (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Two actual closed immersions of an integral scheme of dimension d ≥ 1 with k' J ∼ k J' and
k, k' coprime: the restricted forms of degree D of the first number at least
(k^d - ε) D^d / d! for large D. -/
theorem projectiveFormSectionSpace_coprime_eventually_lower
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (he' : e' ≫ polynomialProjectiveToBase n' K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {k k' : ℕ} (hk : 1 ≤ k)
    (hk' : 1 ≤ k') (hcop : Nat.Coprime k k') (f : Y.functionFieldˣ)
    (hrel : k' • projectiveHyperplaneCartier e g hg hggen =
      k • projectiveHyperplaneCartier e' g' hg' hggen' + principalCartierDivisor Y f)
    (j₀ : {l : Fin n // Nonempty (projectivePullbackCoordinateOpen e l)}) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ D : ℕ in atTop, ((k : ℝ) ^ d - ε) * (D : ℝ) ^ d / d.factorial ≤
      Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) := by
  obtain ⟨r, -, -, hkr, hlim⟩ := projectiveHyperplane_degree_pow_dvd_of_coprime e g hg hggen e' g'
    hg' hggen' he he' hn hd hk hk' hcop f hrel
  have hforms := projectiveFormSectionSpace_tendsto e g hg hggen he hn hd j₀ hlim
  have hfact : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hkr' : (k : ℝ) ^ d ≤ r := by exact_mod_cast hkr
  have hlt : ((k : ℝ) ^ d - ε) / d.factorial < (r : ℝ) / d.factorial :=
    (div_lt_div_iff_of_pos_right hfact).mpr (by linarith)
  filter_upwards [hforms.eventually (lt_mem_nhds hlt), eventually_ge_atTop 1] with D hD hD1
  have hDpos : (0 : ℝ) < (D : ℝ) ^ d := by
    have : (0 : ℝ) < D := by exact_mod_cast hD1
    positivity
  rw [lt_div_iff₀ hDpos] at hD
  have hre : ((k : ℝ) ^ d - ε) * (D : ℝ) ^ d / d.factorial =
      ((k : ℝ) ^ d - ε) / d.factorial * (D : ℝ) ^ d := by ring
  rw [hre]
  exact hD.le

end Degree

section Bound

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The numerical bound for a sum of s coprime-ample divisors: for every ε > 0 and large j, some
finite-dimensional space of sections of j Σ L_i restricts to the closure of η, of dimension
d ≥ 1, with dimension at least (s^d - ε) j^d / d!. -/
theorem coprimeAmpleSum_restrictedSubspaceDim_eventually {s : ℕ} (hs : 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsAmpleCoprime K (L i)) (η : X) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set X)) = d) (hd1 : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • ∑ i, L i).sheaf, ⊤), FiniteDimensional K V ∧
      ((s : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K (j • ∑ i, L i) η V := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  choose k k' hk hk' hcop hv hv' using hL
  -- the 2 s very ample presentations: (i, false) for k_i L_i and (i, true) for k'_i L_i
  let κ : Fin s × Bool → ℕ := fun p => cond p.2 (k' p.1) (k p.1)
  have hvp : ∀ p : Fin s × Bool, CartierIsVeryAmpleProj K (κ p • L p.1) := by
    rintro ⟨i, _ | _⟩
    · exact hv i
    · exact hv' i
  choose N e hci hbase g hg hggen f hLf using hvp
  choose c hc using fun p => polynomialProjective_exists_coordinate_chart (N p) K (e p η)
  have hXgen : ∀ p, MvPolynomial.X (c p) ∉ (e p (genericPoint X)).asHomogeneousIdeal := fun p =>
    (Proj.mem_basicOpen _ _ _).mp (((genericPoint_specializes η).map (e p).continuous).mem_open
      (Proj.basicOpen _ _).isOpen (hc p))
  have hgW : ∀ p, MvPolynomial.X (c p) ∉
      ((pointClosureι η ≫ e p) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal := by
    intro p
    rw [Scheme.Hom.comp_apply, pointClosureι_genericPoint]
    exact (Proj.mem_basicOpen _ _ _).mp (hc p)
  have hbW : ∀ p, (pointClosureι η ≫ e p) ≫ polynomialProjectiveToBase (N p) K =
      pointClosureScheme η ↘ Spec (CommRingCat.of K) := by
    intro p
    rw [Category.assoc, hbase p]
    rfl
  have hW : topologicalKrullDim (pointClosureScheme η) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [pointClosureScheme_topologicalKrullDim, hd]
  -- a closed point y of W in all charts, with coordinates
  let O : Set (pointClosureScheme η) := ⋂ p : Fin s × Bool,
    (projectivePullbackCoordinateOpen (pointClosureι η ≫ e p) (c p) : Set (pointClosureScheme η))
  have hO : IsOpen O :=
    isOpen_iInter_of_finite fun p => (projectivePullbackCoordinateOpen _ _).isOpen
  have hgenO : genericPoint (pointClosureScheme η) ∈ O := by
    refine Set.mem_iInter.mpr fun p => ?_
    change genericPoint _ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e p) (c p)
    rw [projectivePullbackCoordinateOpen, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply,
      pointClosureι_genericPoint]
    exact hc p
  obtain ⟨y, hyc, hyO, ch, hyU⟩ := exists_closedPoint_etaleChart_dim (K := K) hW O hO ⟨_, hgenO⟩
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) ch.isAffine y hyU hyc
  obtain ⟨coords, -, -⟩ := etaleChart_exists_taylorCoordinates ch y hyU β
  have : IsLocallyNoetherian (pointClosureScheme η) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureScheme η ↘ Spec (CommRingCat.of K))
  have hyk : ∀ p, y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e p) (c p) :=
    fun p => Set.mem_iInter.mp hyO p
  -- the hyperplane divisors of the coordinate forms and the presentations κ_p L = H_p + div ρ_p
  let H : Fin s × Bool → CartierDivisor X := fun p =>
    projectiveHyperplaneCartier (e p) (MvPolynomial.X (c p)) (MvPolynomial.isHomogeneous_X K _)
      (hXgen p)
  let ρ : Fin s × Bool → X.functionFieldˣ := fun p =>
    projectivePullbackHomogeneousRatio (e p) ⟨c p, ⟨⟨η, hc p⟩⟩⟩ 1 (g p) (hg p)
      (MvPolynomial.X (c p)) (MvPolynomial.isHomogeneous_X K _) Nat.one_pos (hggen p) (hXgen p) *
        f p
  have hLH : ∀ p, κ p • L p.1 = H p + principalCartierDivisor X (ρ p) := by
    intro p
    rw [hLf p, principalCartierDivisor_mul, ← add_assoc]
    congr 1
    exact projectivePullbackHomogeneousCartier_eq_principalShift (e p) ⟨c p, ⟨⟨η, hc p⟩⟩⟩ 1
      (g p) (hg p) (MvPolynomial.X (c p)) (MvPolynomial.isHomogeneous_X K _) Nat.one_pos
      (hggen p) (hXgen p)
  -- integrality on W: the restricted forms of the embedding by k_i L_i
  have hforms : ∀ p : Fin s × Bool, p.2 = false → ∀ ε₁ : ℝ, 0 < ε₁ → ∀ᶠ D : ℕ in atTop,
      ((κ p : ℝ) ^ (d + 1) - ε₁) * (D : ℝ) ^ (d + 1) / (d + 1).factorial ≤
        Module.finrank K (projectiveFormSectionSpace (pointClosureι η ≫ e p)
          (MvPolynomial.X (c p)) (MvPolynomial.isHomogeneous_X K _) (hgW p)
          ⟨c p, ⟨⟨y, hyk p⟩⟩⟩ (hbW p) D) := by
    rintro ⟨i, _ | _⟩ hp ε₁ hε₁
    swap
    · exact absurd hp (by simp)
    have h1 : k i • L i = H (i, false) + principalCartierDivisor X (ρ (i, false)) :=
      hLH (i, false)
    have h2 : k' i • L i = H (i, true) + principalCartierDivisor X (ρ (i, true)) := hLH (i, true)
    have hrelX : k' i • H (i, false) = k i • H (i, true) +
        principalCartierDivisor X (ρ (i, true) ^ k i * (ρ (i, false) ^ k' i)⁻¹) := by
      have h3 : k' i • (k i • L i) = k i • (k' i • L i) := smul_comm _ _ _
      rw [h1, h2, nsmul_add, nsmul_add] at h3
      rw [principalCartierDivisor_mul, principalCartierDivisor_inv, principalCartierDivisor_power,
        principalCartierDivisor_power]
      calc k' i • H (i, false)
          = (k' i • H (i, false) + k' i • principalCartierDivisor X (ρ (i, false))) -
              k' i • principalCartierDivisor X (ρ (i, false)) := by abel
        _ = (k i • H (i, true) + k i • principalCartierDivisor X (ρ (i, true))) -
              k' i • principalCartierDivisor X (ρ (i, false)) := by rw [h3]
        _ = _ := by abel
    obtain ⟨fW, hrelW⟩ := pointClosure_hyperplane_nsmul_eq_add_principal (η := η)
      (e (i, false)) (MvPolynomial.X (c (i, false))) (MvPolynomial.isHomogeneous_X K _)
      (hXgen (i, false)) (hgW (i, false))
      (e (i, true)) (MvPolynomial.X (c (i, true))) (MvPolynomial.isHomogeneous_X K _)
      (hXgen (i, true)) (hgW (i, true)) _ hrelX
    exact projectiveFormSectionSpace_coprime_eventually_lower
      (pointClosureι η ≫ e (i, false)) (MvPolynomial.X (c (i, false)))
      (MvPolynomial.isHomogeneous_X K _) (hgW (i, false))
      (pointClosureι η ≫ e (i, true)) (MvPolynomial.X (c (i, true)))
      (MvPolynomial.isHomogeneous_X K _) (hgW (i, true))
      (hbW (i, false)) (hbW (i, true)) hW (by omega) (hk i) (hk' i) (hcop i) fW hrelW _ hε₁
  -- the family indexed by ℕ: first the embeddings by k_i L_i, then those by k'_i L_i
  let idx : ℕ → Fin s × Bool := fun l => (finExtend hs (l % s), decide (s ≤ l))
  have hidx0 : ∀ l, l < s → idx l = (finExtend hs l, false) := fun l hl => by
    change (finExtend hs (l % s), decide (s ≤ l)) = (finExtend hs l, false)
    rw [Nat.mod_eq_of_lt hl, decide_eq_false (by omega)]
  have hidx1 : ∀ l, l < s → idx (s + l) = (finExtend hs l, true) := fun l hl => by
    change (finExtend hs ((s + l) % s), decide (s ≤ s + l)) = (finExtend hs l, true)
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hl, decide_eq_true (by omega)]
  have hEci : ∀ l : ℕ, IsClosedImmersion (e (idx l)) := fun l => hci (idx l)
  let jW : ∀ l : ℕ, {t : Fin (N (idx l)) //
      Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e (idx l)) t)} :=
    fun l => ⟨c (idx l), ⟨⟨y, hyk (idx l)⟩⟩⟩
  -- the constants
  set pad := (s - 1) * (d + 1) with hpad
  obtain ⟨δ, hδ0, hδ1, hδ⟩ := exists_delta_pow_sub_lt (s : ℝ) (d + 1) hε
  set ε₁ : ℝ := 1 - (1 - δ) ^ (d + 1) with hε₁def
  have hε₁ : 0 < ε₁ := by
    have : (1 - δ) ^ (d + 1) < 1 := pow_lt_one₀ (by linarith) (by linarith) (Nat.succ_ne_zero d)
    linarith
  have hD : ∀ p : Fin s × Bool, p.2 = false → ∃ D₀ : ℕ, ∀ D ≥ D₀,
      ((κ p : ℝ) ^ (d + 1) - ε₁) * (D : ℝ) ^ (d + 1) / (d + 1).factorial ≤
        Module.finrank K (projectiveFormSectionSpace (pointClosureι η ≫ e p)
          (MvPolynomial.X (c p)) (MvPolynomial.isHomogeneous_X K _) (hgW p)
          ⟨c p, ⟨⟨y, hyk p⟩⟩⟩ (hbW p) D) :=
    fun p hp => eventually_atTop.mp (hforms p hp ε₁ hε₁)
  choose! D₀ hD₀ using hD
  set Cn : ℕ := ∑ i : Fin s, (k i * k' i + k i * (D₀ (i, false) + pad)) with hCn
  have hCi : ∀ i : Fin s, k i * k' i + k i * (D₀ (i, false) + pad) ≤ Cn := fun i =>
    Finset.single_le_sum (f := fun i : Fin s => k i * k' i + k i * (D₀ (i, false) + pad))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hfinal := eventually_sub_pow_le ((s : ℝ) * (1 - δ)) (Cn : ℝ) (d + 1)
    (ε := ((s : ℝ) * (1 - δ)) ^ (d + 1) - ((s : ℝ) ^ (d + 1) - ε)) (by linarith)
  filter_upwards [hfinal, eventually_ge_atTop (Cn + 1)] with j hj hjC
  -- j = a_i k_i + b_i k'_i with b_i < k_i
  have hrep : ∀ i : Fin s, ∃ a bb : ℕ, a * k i + bb * k' i = j ∧ bb < k i := fun i =>
    exists_coprime_representation (hk i) (hcop i) (by have := hCi i; omega)
  choose a bb hab hbb using hrep
  have ha : ∀ i : Fin s, D₀ (i, false) + pad ≤ a i := by
    intro i
    have h1 : bb i * k' i ≤ k i * k' i := Nat.mul_le_mul_right _ (hbb i).le
    have h2 := hCi i
    have h3 := hab i
    have h4 : k i * (D₀ (i, false) + pad) ≤ k i * a i := by
      rw [mul_comm (k i) (a i)]
      omega
    exact Nat.le_of_mul_le_mul_left h4 (hk i)
  have hkq : ∀ i : Fin s, (j : ℝ) - Cn ≤ (k i : ℝ) * ((a i - pad : ℕ) : ℝ) := by
    intro i
    have h1 : bb i * k' i ≤ k i * k' i := Nat.mul_le_mul_right _ (hbb i).le
    have h2 := hCi i
    have h3 : k i * a i + bb i * k' i = j := by rw [mul_comm]; exact hab i
    have hpa : pad ≤ a i := le_trans (Nat.le_add_left _ _) (ha i)
    have h5 : k i * pad ≤ k i * a i := Nat.mul_le_mul_left _ hpa
    have h6 : k i * pad ≤ k i * (D₀ (i, false) + pad) :=
      Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
    have h7 : j ≤ k i * (a i - pad) + Cn := by
      rw [Nat.mul_sub]
      omega
    have h8 : (j : ℝ) ≤ (k i : ℝ) * ((a i - pad : ℕ) : ℝ) + Cn := by exact_mod_cast h7
    linarith
  -- the multidegree and the degrees of the forms
  let B : Fin s × Bool → ℕ := fun p => cond p.2 (bb p.1) (a p.1)
  let b : ℕ → ℕ := fun l => B (idx l)
  let q : ℕ → ℕ := fun l => b l - pad
  have hbl : ∀ l, l < s → b l = a (finExtend hs l) := fun l hl => by
    change B (idx l) = _
    rw [hidx0 l hl]
    rfl
  set lam : ℝ := (1 - δ) * ((j : ℝ) - Cn) with hlamdef
  have hjCn : (1 : ℝ) ≤ (j : ℝ) - Cn := by
    have : ((Cn + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hjC
    push_cast at this
    linarith
  have hlampos : 0 < lam := mul_pos (by linarith) (by linarith)
  have hboth : ∀ l, l < s → lam ^ (d + 1) ≤ (((d + 1).factorial * Module.finrank K
      (projectiveFormSectionSpace (pointClosureι η ≫ e (idx l)) (MvPolynomial.X (c (idx l)))
        (MvPolynomial.isHomogeneous_X K _) (hgW (idx l)) (jW l) (hbW (idx l)) (q l)) : ℕ) : ℝ) := by
    intro l hl
    have hp : (idx l).2 = false := by rw [hidx0 l hl]
    have hκl : κ (idx l) = k (finExtend hs l) := by
      rw [hidx0 l hl]
      rfl
    have hql : q l = a (finExtend hs l) - pad := by
      change b l - pad = _
      rw [hbl l hl]
    have hDl : D₀ (idx l) ≤ q l := by
      rw [hql, hidx0 l hl]
      have := ha (finExtend hs l)
      omega
    have hbound := hD₀ (idx l) hp (q l) hDl
    have hk1 : (1 : ℝ) ≤ (κ (idx l) : ℝ) := by
      rw [hκl]
      exact_mod_cast hk (finExtend hs l)
    have hμ : lam ≤ (κ (idx l) : ℝ) * (1 - δ) * (q l : ℝ) := by
      have h := hkq (finExtend hs l)
      rw [hκl, hql]
      have h1δ : (0 : ℝ) ≤ 1 - δ := by linarith
      calc lam = (1 - δ) * ((j : ℝ) - Cn) := rfl
        _ ≤ (1 - δ) * ((k (finExtend hs l) : ℝ) * ((a (finExtend hs l) - pad : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h h1δ
        _ = _ := by ring
    have hfact : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d + 1)
    have hq0 : (0 : ℝ) ≤ (q l : ℝ) ^ (d + 1) := by positivity
    calc lam ^ (d + 1) ≤ ((κ (idx l) : ℝ) * (1 - δ) * (q l : ℝ)) ^ (d + 1) :=
          pow_le_pow_left₀ hlampos.le hμ _
      _ = ((κ (idx l) : ℝ) * (1 - δ)) ^ (d + 1) * (q l : ℝ) ^ (d + 1) := by rw [mul_pow]
      _ ≤ ((κ (idx l) : ℝ) ^ (d + 1) - ε₁) * (q l : ℝ) ^ (d + 1) :=
          mul_le_mul_of_nonneg_right (mul_one_sub_pow_le hk1 hδ0.le hδ1.le (d + 1)) hq0
      _ ≤ _ := by
          rw [div_le_iff₀ hfact] at hbound
          push_cast
          linarith
  -- the divisor identity Σ_l b_l H_l + div P = j Σ L_i
  set P : X.functionFieldˣ := ∏ l ∈ Finset.range (2 * s), ρ (idx l) ^ b l with hP
  have hA : pointClosureMultiDivisor (fun l => H (idx l)) (2 * s) b +
      principalCartierDivisor X P = j • ∑ i, L i := by
    rw [hP, principalCartierDivisor_weighted_prod (X := X) (Finset.range (2 * s))
      (fun l => ρ (idx l)) b]
    unfold pointClosureMultiDivisor
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ l, b l • H (idx l) + b l • principalCartierDivisor X (ρ (idx l)) =
        (b l * κ (idx l)) • L (idx l).1 := by
      intro l
      rw [mul_nsmul', hLH (idx l), nsmul_add]
    rw [Finset.sum_congr rfl fun l _ => hterm l, two_mul, Finset.sum_range_add,
      ← Finset.sum_add_distrib]
    have hpair : ∀ l ∈ Finset.range s, (b l * κ (idx l)) • L (idx l).1 +
        (b (s + l) * κ (idx (s + l))) • L (idx (s + l)).1 = j • L (finExtend hs l) := by
      intro l hl
      have hl' := Finset.mem_range.mp hl
      have e0 : b l * κ (idx l) = a (finExtend hs l) * k (finExtend hs l) := by
        change B (idx l) * κ (idx l) = _
        rw [hidx0 l hl']
        rfl
      have e1 : b (s + l) * κ (idx (s + l)) = bb (finExtend hs l) * k' (finExtend hs l) := by
        change B (idx (s + l)) * κ (idx (s + l)) = _
        rw [hidx1 l hl']
        rfl
      have e2 : L (idx l).1 = L (finExtend hs l) := by rw [hidx0 l hl']
      have e3 : L (idx (s + l)).1 = L (finExtend hs l) := by rw [hidx1 l hl']
      rw [e0, e1, e2, e3, ← add_nsmul, hab]
    rw [Finset.sum_congr rfl hpair, Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun l => j • L (finExtend hs l)) s]
    exact Finset.sum_congr rfl fun i _ => by rw [finExtend_val hs i]
  obtain ⟨V, hV, hVdim⟩ := mixedForms_restrictedSubspaceDim_lower y (fun l => e (idx l))
    (fun l => MvPolynomial.X (c (idx l))) (fun l => MvPolynomial.isHomogeneous_X K _)
    (fun l => hXgen (idx l)) (fun l => hgW (idx l)) (fun l => hbase (idx l)) jW
    (fun l => hyk (idx l)) coords hyc q b (2 * s) s hs (by omega)
    (fun l hl => by
      change b l - pad + pad ≤ b l
      rw [Nat.sub_add_cancel]
      rw [hbl l hl]
      exact le_trans (Nat.le_add_left _ _) (ha (finExtend hs l)))
    hlampos.le
    (fun l hl => by
      by_contra h0
      have h1 := hboth l hl
      rw [Nat.eq_zero_of_not_pos h0, mul_zero, Nat.cast_zero] at h1
      have h2 : 0 < lam ^ (d + 1) := by positivity
      linarith)
    (fun l hl => hboth l hl) P hA
  refine ⟨V, hV, le_trans ?_ hVdim⟩
  have hcoef : ((s : ℝ) * (1 - δ)) ^ (d + 1) -
      (((s : ℝ) * (1 - δ)) ^ (d + 1) - ((s : ℝ) ^ (d + 1) - ε)) = (s : ℝ) ^ (d + 1) - ε := by ring
  have hprod : (s : ℝ) * (1 - δ) * ((j : ℝ) - Cn) = (s : ℝ) * lam := by rw [hlamdef]; ring
  rw [hcoef, hprod] at hj
  exact div_le_div_of_nonneg_right hj (by positivity)

/-- The numerical input for F1 (step 4) for coprime-ample divisors: for s ≥ n + 1 of them the sum
A = Σ L_i satisfies the bound of `MixedAmpleNumericalBound` on every positive-dimensional closure
of a point. -/
theorem mixedCoprimeAmpleNumericalBound {n s : ℕ} (hs : n + 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsAmpleCoprime K (L i)) (η : X) (d : ℕ)
    (hd : topologicalKrullDim (closure ({η} : Set X)) = d) (hd1 : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • ∑ i, L i).sheaf, ⊤), FiniteDimensional K V ∧
      ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K (j • ∑ i, L i) η V := by
  filter_upwards [coprimeAmpleSum_restrictedSubspaceDim_eventually (by omega) L hL η hd hd1 hε]
    with j ⟨V, hV, hle⟩
  refine ⟨V, hV, le_trans ?_ hle⟩
  have hns : (n + 1 : ℝ) ^ d ≤ (s : ℝ) ^ d :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) d
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Bound

section Statements

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra

/-- F1 for coprime-ample divisors: as `MixedFujitaFreeness`, with each L_i having two coprime very
ample multiples. -/
def MixedFujitaFreenessCoprime : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (s : ℕ), n + 1 ≤ s → ∀ (L : Fin s → CartierDivisor X),
        (∀ i, CartierIsAmpleCoprime K (L i)) →
      ∀ N : CartierDivisor X, CartierIsNef K N →
        CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N)

/-- F1 for coprime-ample divisors follows from S-NF for ample sums alone: the numerical hypothesis
is proved by the bound for sums of coprime-ample divisors. -/
theorem mixedFujitaFreenessCoprime_of_strongNumericalFreenessSum
    (h : StrongNumericalFreenessSum.{u}) : MixedFujitaFreenessCoprime.{u} := by
  intro K _ _ _ _ X _ _ n hn hn1 _ c₀ s hs L hL N hN
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact h K X n hn hn1 c₀ (∑ i, L i) N
    (cartierIsAmpleSum_sum (by omega) L fun i => cartierIsAmpleProj_of_ampleCoprime (hL i)) hN
    (fun η d hd hd1 ε hε => mixedCoprimeAmpleNumericalBound hs L hL η d hd hd1 ε hε)

/-- The classical bridge that remains for the numerical input of F1: on a smooth projective
variety an ample divisor (one very ample multiple) has two coprime very ample multiples. -/
def AmpleCoprimeBridge : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (A : CartierDivisor X),
      CartierIsAmpleProj K A → CartierIsAmpleCoprime K A

/-- The numerical input for F1 follows from the bridge. -/
theorem mixedAmpleNumericalBound_of_ampleCoprimeBridge (hbridge : AmpleCoprimeBridge.{u}) :
    MixedAmpleNumericalBound.{u} := by
  intro K _ _ _ _ X _ _ n hn hn1 _ s hs L hL η d hd hd1 ε hε
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact mixedCoprimeAmpleNumericalBound hs L (fun i => hbridge K X n hn hn1 (L i) (hL i)) η d hd
    hd1 ε hε

/-- F1 from S-NF for ample sums and the bridge. -/
theorem mixedFujitaFreeness_of_strongNumericalFreenessSum_of_ampleCoprimeBridge
    (h : StrongNumericalFreenessSum.{u}) (hbridge : AmpleCoprimeBridge.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_strongNumericalFreenessSum h
    (mixedAmpleNumericalBound_of_ampleCoprimeBridge hbridge)

end Statements

end MixedFujita

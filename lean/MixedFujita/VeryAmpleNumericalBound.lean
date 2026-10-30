/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureForms
public import MixedFujita.MixedFormCubeBound
public import MixedFujita.EtaleChartDimension
public import MixedFujita.ClosedRationalPoints
public import MixedFujita.ProjectivePullbackFixedClass

/-!
The numerical bound for sums of very ample divisors (step 4). Let L_1, …, L_s be very ample on an
integral scheme X locally of finite type over an algebraically closed field K: each L_i is
linearly equivalent to the hyperplane divisor of a closed immersion e_i into a projective space.
Let η be a point whose closure W has dimension d ≥ 1. For each i some coordinate X_{k_i} does not
vanish at e_i(η), and the hyperplane divisor of X_{k_i} is linearly equivalent to the given one.
W is an integral variety, so it has a closed point y in all the charts {X_{k_i} ≠ 0} with an étale
chart of d coordinates; its stalk has a K-point and completion coordinates. The mixed bound (13)
with forms only on W gives (d! dim U)^(1/d) ≥ s q for the span U of Taylor expansions at y of
products of restricted forms, and U lies in the image of the sections of (q + (s-1) d) Σ J_i on X;
the principal shift to Σ L_i keeps the image. Hence some finite-dimensional space of sections of
j Σ L_i restricts to W with dimension at least (s (j - (s-1) d))^d / d!, and for every ε > 0 and
large j at least (s^d - ε) j^d / d!. With s ≥ n + 1 this is the numerical hypothesis of S-NF for
A = Σ L_i, without intersection numbers; so F1 for very ample L_i follows from S-NF for ample sums
alone.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Definition

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Very ampleness in the projective sense: linearly equivalent to the hyperplane divisor of an
actual closed immersion over the base field. -/
def CartierIsVeryAmpleProj (A : CartierDivisor Y) : Prop :=
  ∃ (n : ℕ) (e : Y ⟶ polynomialProjectiveScheme n K) (_ : IsClosedImmersion e)
    (_ : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal) (f : Y.functionFieldˣ),
    A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y f

variable {K}

/-- A very ample divisor is ample. -/
theorem cartierIsAmpleProj_of_veryAmple {A : CartierDivisor Y}
    (hA : CartierIsVeryAmpleProj K A) : CartierIsAmpleProj K A := by
  obtain ⟨n, e, he, hbase, g, hg, hggen, f, hAf⟩ := hA
  exact ⟨1, le_rfl, n, e, he, hbase, g, hg, hggen, f, by rw [one_smul, hAf]⟩

end Definition

section Points

variable {K : Type u} [Field K] [IsAlgClosed K] {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- A closed point of an affine open of a scheme locally of finite type over an algebraically
closed field has a K-valued evaluation of its stalk. -/
theorem affineOpen_closedPoint_has_localEvaluation {U : W.Opens} (hU : IsAffineOpen U) (x : W)
    (hx : x ∈ U) (hClosed : IsClosed {x}) : Nonempty (W.presheaf.stalk x →ₐ[K] K) := by
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : U)
  have := cartierBaseOpenLocalScalarTower (K := K) x hx
  have : Algebra.FiniteType K Γ(W, U) := sectionsBaseOpen_finiteType hU
  have : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hx⟩ hClosed
  have := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  exact ⟨closedPointLocalEvaluation (K := K) (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (W.presheaf.stalk x)⟩

end Points

section Numerics

/-- Indices of Fin s extended to ℕ, constant beyond s - 1. -/
def finExtend {s : ℕ} (hs : 1 ≤ s) (i : ℕ) : Fin s := ⟨min i (s - 1), by omega⟩

theorem finExtend_val {s : ℕ} (hs : 1 ≤ s) (i : Fin s) : finExtend hs i = i :=
  Fin.ext (min_eq_left (by have := i.isLt; omega))

/-- From (d! u)^(1/d) ≥ a ≥ 0: a^d / d! ≤ u. -/
theorem pow_div_factorial_le_of_le_rpow_inv {d u : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : a ≤ (((d + 1).factorial * u : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹) :
    a ^ (d + 1) / (d + 1).factorial ≤ u := by
  have hz : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [Real.le_rpow_inv_iff_of_pos ha (by positivity) hz] at h
  have hcast : ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast, Nat.cast_mul] at h
  rw [div_le_iff₀ (by positivity), mul_comm]
  exact h

/-- For every ε > 0, eventually (s^d - ε) j^d ≤ (s (j - c))^d. -/
theorem eventually_sub_pow_le (s c : ℝ) (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, (s ^ d - ε) * (j : ℝ) ^ d ≤ (s * ((j : ℝ) - c)) ^ d := by
  have h1 : Tendsto (fun j : ℕ => s * (1 - c / (j : ℝ))) atTop (𝓝 (s * (1 - 0))) :=
    (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat c)).const_mul s
  rw [sub_zero, mul_one] at h1
  have h2 := (h1.pow d).eventually (lt_mem_nhds (show s ^ d - ε < s ^ d by linarith))
  filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj0
  have hid : (s * ((j : ℝ) - c)) ^ d = (s * (1 - c / j)) ^ d * (j : ℝ) ^ d := by
    rw [← mul_pow]
    congr 1
    rw [mul_assoc, sub_mul, one_mul, div_mul_cancel₀ c hj'.ne']
  rw [hid]
  exact mul_le_mul_of_nonneg_right hj.le (by positivity)

end Numerics

section Bound

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

omit [IsAlgClosed K] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- The restriction bound transported along an equality of divisors. -/
theorem exists_le_cartierRestrictedSubspaceDim_of_le_range_of_eq {η : X}
    {D D' : CartierDivisor X} (hD : D = D') (y : pointClosureScheme η) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (pointClosureι η y) f) {m : ℕ}
    (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
      ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (U : Submodule K (MvPowerSeries (Fin m) K)) [FiniteDimensional K U]
    (hU : U ≤ LinearMap.range (pointClosureSectionTaylor D y f hf coords)) :
    ∃ V : Submodule K Γ(D'.sheaf, ⊤), FiniteDimensional K V ∧
      Module.finrank K U ≤ cartierRestrictedSubspaceDim K D' η V := by
  subst hD
  exact exists_le_cartierRestrictedSubspaceDim_of_le_range D y f hf coords U hU

/-- The bound for a sum of s very ample divisors at fixed q ≥ 1: some finite-dimensional space of
sections of (q + (s-1) d) Σ L_i restricts to the closure of η, of dimension d ≥ 1, with dimension
at least (s q)^d / d!. -/
theorem veryAmpleSum_restrictedSubspaceDim_lower {s : ℕ} (hs : 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsVeryAmpleProj K (L i)) (η : X) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set X)) = d) (hd1 : 1 ≤ d) (q : ℕ) (hq : 1 ≤ q) :
    ∃ V : Submodule K Γ(((q + (s - 1) * d) • ∑ i, L i).sheaf, ⊤), FiniteDimensional K V ∧
      ((s * q : ℕ) : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K ((q + (s - 1) * d) • ∑ i, L i) η V := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  choose N e hci hbase g hg hggen f hLf using hL
  choose k hk using fun i => polynomialProjective_exists_coordinate_chart (N i) K (e i η)
  -- the coordinate forms avoid e_i(η), hence the image of the generic point
  have hXgen : ∀ i, MvPolynomial.X (k i) ∉ (e i (genericPoint X)).asHomogeneousIdeal := fun i =>
    (Proj.mem_basicOpen _ _ _).mp (((genericPoint_specializes η).map (e i).continuous).mem_open
      (Proj.basicOpen _ _).isOpen (hk i))
  have hgW : ∀ i, MvPolynomial.X (k i) ∉
      ((pointClosureι η ≫ e i) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal := by
    intro i
    rw [Scheme.Hom.comp_apply, pointClosureι_genericPoint]
    exact (Proj.mem_basicOpen _ _ _).mp (hk i)
  -- the closure W of η and a closed point y in all charts with an étale chart
  have hW : topologicalKrullDim (pointClosureScheme η) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [pointClosureScheme_topologicalKrullDim, hd]
  let O : Set (pointClosureScheme η) := ⋂ i : Fin s,
    (projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) (k i) : Set (pointClosureScheme η))
  have hO : IsOpen O := isOpen_iInter_of_finite fun i => (projectivePullbackCoordinateOpen _ _).isOpen
  have hgenO : genericPoint (pointClosureScheme η) ∈ O := by
    refine Set.mem_iInter.mpr fun i => ?_
    change genericPoint _ ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) (k i)
    rw [projectivePullbackCoordinateOpen, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply,
      pointClosureι_genericPoint]
    exact hk i
  obtain ⟨y, hyc, hyO, c, hyU⟩ := exists_closedPoint_etaleChart_dim (K := K) hW O hO ⟨_, hgenO⟩
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) c.isAffine y hyU hyc
  obtain ⟨coords, -, -⟩ := etaleChart_exists_taylorCoordinates c y hyU β
  have : IsLocallyNoetherian (pointClosureScheme η) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureScheme η ↘ Spec (CommRingCat.of K))
  have hyk : ∀ i : Fin s, y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) (k i) :=
    fun i => Set.mem_iInter.mp hyO i
  let jW : ∀ i : ℕ, {l : Fin (N (finExtend hs i)) //
      Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e (finExtend hs i)) l)} :=
    fun i => ⟨k (finExtend hs i), ⟨⟨y, hyk (finExtend hs i)⟩⟩⟩
  -- (13) with forms only on W, and the inclusion of U in the sections of X
  have hbound := projective_mixed_formsOnly_lower (Y := pointClosureScheme η)
    (fun i => pointClosureι η ≫ e (finExtend hs i)) (fun i => MvPolynomial.X (k (finExtend hs i)))
    (fun i => MvPolynomial.isHomogeneous_X K _) (fun i => hgW (finExtend hs i))
    (pointClosureι_comp_toBase (fun i => e (finExtend hs i)) (fun i => hbase (finExtend hs i)))
    y coords jW (fun i => hyk (finExtend hs i)) hW hyc q hq (s - 1)
  have hU := mixedProductSpace_le_pointClosureHyperplaneRange_const y
    (fun i => e (finExtend hs i)) (fun i => MvPolynomial.X (k (finExtend hs i)))
    (fun i => MvPolynomial.isHomogeneous_X K _) (fun i => hXgen (finExtend hs i))
    (fun i => hgW (finExtend hs i)) (fun i => hbase (finExtend hs i)) jW
    (fun i => hyk (finExtend hs i)) coords q s hs
  -- the divisor identity: (q + (s-1)(d+1)) Σ J_i + div G = (q + (s-1)(d+1)) Σ L_i
  let H : Fin s → CartierDivisor X := fun a =>
    projectiveHyperplaneCartier (e a) (MvPolynomial.X (k a)) (MvPolynomial.isHomogeneous_X K _)
      (hXgen a)
  let r : Fin s → X.functionFieldˣ := fun a =>
    projectivePullbackHomogeneousRatio (e a) ⟨k a, ⟨⟨η, hk a⟩⟩⟩ 1 (g a) (hg a)
      (MvPolynomial.X (k a)) (MvPolynomial.isHomogeneous_X K _) Nat.one_pos (hggen a) (hXgen a)
  have hLH : ∀ a, L a = H a + principalCartierDivisor X (r a * f a) := by
    intro a
    rw [hLf a, principalCartierDivisor_mul, ← add_assoc]
    congr 1
    exact projectivePullbackHomogeneousCartier_eq_principalShift (e a) ⟨k a, ⟨⟨η, hk a⟩⟩⟩ 1
      (g a) (hg a) (MvPolynomial.X (k a)) (MvPolynomial.isHomogeneous_X K _) Nat.one_pos
      (hggen a) (hXgen a)
  have hsumL : ∑ a, L a = ∑ a, H a + principalCartierDivisor X (∏ a, (r a * f a)) := by
    rw [Finset.sum_congr rfl fun a _ => hLH a, Finset.sum_add_distrib]
    congr 1
    have h := principalCartierDivisor_weighted_prod (X := X) Finset.univ
      (fun a => r a * f a) (fun _ => 1)
    simp only [pow_one, one_smul] at h
    exact h.symm
  have hsumJ : ∑ i ∈ Finset.range s, H (finExtend hs i) = ∑ a, H a := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => H (finExtend hs i)) s]
    exact Finset.sum_congr rfl fun a _ => congrArg H (finExtend_val hs a)
  set j := q + (s - 1) * (d + 1) with hj
  set P := ∏ a, (r a * f a) with hP
  have hD : pointClosureMultiDivisor (fun i => H (finExtend hs i)) s (fun _ => j) +
      principalCartierDivisor X (P ^ j) = j • ∑ a, L a := by
    rw [pointClosureMultiDivisor_const, hsumJ, hsumL, smul_add, principalCartierDivisor_power]
  have hF := pointClosureMulti_isLocalEquationAt y (fun i => H (finExtend hs i))
    (fun i => projectiveHyperplaneUnit (e (finExtend hs i)) (MvPolynomial.X (k (finExtend hs i)))
      (MvPolynomial.isHomogeneous_X K _) (hXgen (finExtend hs i))
      (pointClosureChart y (fun i => e (finExtend hs i)) jW (fun i => hyk (finExtend hs i)) i))
    (pointClosureChart_isLocalEquationAt y (fun i => e (finExtend hs i))
      (fun i => MvPolynomial.X (k (finExtend hs i))) (fun i => MvPolynomial.isHomogeneous_X K _)
      (fun i => hXgen (finExtend hs i)) jW (fun i => hyk (finExtend hs i))) s (fun _ => j)
  have hle := hU.trans (pointClosureSectionTaylor_range_le_principal _ y _ (P ^ j) hF coords)
  have : FiniteDimensional K (mixedProductSpace
      (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e (finExtend hs i))
        (fun i => MvPolynomial.X (k (finExtend hs i))) (fun i => MvPolynomial.isHomogeneous_X K _)
        (fun i => hgW (finExtend hs i))
        (pointClosureι_comp_toBase (fun i => e (finExtend hs i)) (fun i => hbase (finExtend hs i)))
        y coords jW (fun i => hyk (finExtend hs i)) q)
      (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e (finExtend hs i))
        (fun i => MvPolynomial.X (k (finExtend hs i))) (fun i => MvPolynomial.isHomogeneous_X K _)
        (fun i => hgW (finExtend hs i))
        (pointClosureι_comp_toBase (fun i => e (finExtend hs i)) (fun i => hbase (finExtend hs i)))
        y coords jW (fun i => hyk (finExtend hs i)) (d + 1) 0) (s - 1)) :=
    finiteDimensional_mixedProductSpace _ _ _
  obtain ⟨V, hV, hVdim⟩ := exists_le_cartierRestrictedSubspaceDim_of_le_range_of_eq hD y _ _
    coords _ hle
  refine ⟨V, hV, ?_⟩
  rw [Nat.sub_add_cancel hs] at hbound
  have h2 := pow_div_factorial_le_of_le_rpow_inv (by positivity) hbound
  calc ((s * q : ℕ) : ℝ) ^ (d + 1) / (d + 1).factorial
      = ((s : ℝ) * q) ^ (d + 1) / (d + 1).factorial := by push_cast; ring
    _ ≤ _ := h2
    _ ≤ _ := by exact_mod_cast hVdim

/-- The numerical bound for a sum of s very ample divisors: for every ε > 0 and large j, some
finite-dimensional space of sections of j Σ L_i restricts to the closure of η, of dimension
d ≥ 1, with dimension at least (s^d - ε) j^d / d!. -/
theorem veryAmpleSum_restrictedSubspaceDim_eventually {s : ℕ} (hs : 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsVeryAmpleProj K (L i)) (η : X) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set X)) = d) (hd1 : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • ∑ i, L i).sheaf, ⊤), FiniteDimensional K V ∧
      ((s : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K (j • ∑ i, L i) η V := by
  filter_upwards [eventually_sub_pow_le (s : ℝ) (((s - 1) * d : ℕ) : ℝ) d hε,
    eventually_ge_atTop ((s - 1) * d + 1)] with j hj hjc
  obtain ⟨q, rfl⟩ : ∃ q, j = q + (s - 1) * d := ⟨j - (s - 1) * d, by omega⟩
  obtain ⟨V, hV, hdim⟩ := veryAmpleSum_restrictedSubspaceDim_lower hs L hL η hd hd1 q (by omega)
  refine ⟨V, hV, le_trans ?_ hdim⟩
  have hq : ((q + (s - 1) * d : ℕ) : ℝ) - (((s - 1) * d : ℕ) : ℝ) = q := by push_cast; ring
  rw [hq] at hj
  rw [div_le_div_iff_of_pos_right (by positivity), Nat.cast_mul]
  exact hj

/-- The numerical input for F1 (step 4) for very ample divisors: for s ≥ n + 1 very ample L_i, the
sum A = Σ L_i satisfies the bound of `MixedAmpleNumericalBound` on every positive-dimensional
closure of a point. -/
theorem mixedVeryAmpleNumericalBound {n s : ℕ} (hs : n + 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsVeryAmpleProj K (L i)) (η : X) (d : ℕ)
    (hd : topologicalKrullDim (closure ({η} : Set X)) = d) (hd1 : 1 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • ∑ i, L i).sheaf, ⊤), FiniteDimensional K V ∧
      ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K (j • ∑ i, L i) η V := by
  filter_upwards [veryAmpleSum_restrictedSubspaceDim_eventually (by omega) L hL η hd hd1 hε]
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

/-- F1 for very ample divisors: as `MixedFujitaFreeness`, with very ample L_1, …, L_s. -/
def MixedFujitaFreenessVeryAmple : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (s : ℕ), n + 1 ≤ s → ∀ (L : Fin s → CartierDivisor X),
        (∀ i, CartierIsVeryAmpleProj K (L i)) →
      ∀ N : CartierDivisor X, CartierIsNef K N →
        CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N)

/-- F1 for very ample divisors follows from S-NF for ample sums alone: the numerical hypothesis
is proved by the bound for sums of very ample divisors. -/
theorem mixedFujitaFreenessVeryAmple_of_strongNumericalFreenessSum
    (h : StrongNumericalFreenessSum.{u}) : MixedFujitaFreenessVeryAmple.{u} := by
  intro K _ _ _ _ X _ _ n hn hn1 _ c₀ s hs L hL N hN
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact h K X n hn hn1 c₀ (∑ i, L i) N
    (cartierIsAmpleSum_sum (by omega) L fun i => cartierIsAmpleProj_of_veryAmple (hL i)) hN
    (fun η d hd hd1 ε hε => mixedVeryAmpleNumericalBound hs L hL η d hd hd1 ε hε)

end Statements

end MixedFujita

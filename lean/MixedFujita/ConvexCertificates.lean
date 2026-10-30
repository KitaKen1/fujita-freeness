/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InteriorLatticeBoxes
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Tactic.FunProp

/-!
An augmented vertex matrix supplies an exact barycentric certificate.
Strictly positive coordinates certify an interior point of the actual
Mathlib convex hull. The certificate survives a small change of vertices.
The later rational slice and geometric degeneration are separate steps.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

def simplexVertexMatrix {n : ℕ} {K : Type*} [One K]
    (v : Fin (n + 1) → Fin n → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  fun i j => Fin.cases 1 (fun k => v j k) i

noncomputable def simplexWeights {n : ℕ} {K : Type*} [Field K]
    (v : Fin (n + 1) → Fin n → K) (x : Fin n → K) : Fin (n + 1) → K :=
  (simplexVertexMatrix v)⁻¹.mulVec (Fin.cons 1 x)

theorem simplexVertexMatrix_mulVec_head {n : ℕ} {K : Type*} [Semiring K]
    (v : Fin (n + 1) → Fin n → K) (w : Fin (n + 1) → K) :
    (simplexVertexMatrix v).mulVec w 0 = ∑ j, w j := by
  simp [Matrix.mulVec, dotProduct, simplexVertexMatrix]

theorem simplexVertexMatrix_mulVec_tail {n : ℕ} {K : Type*} [CommSemiring K]
    (v : Fin (n + 1) → Fin n → K) (w : Fin (n + 1) → K) (i : Fin n) :
    (simplexVertexMatrix v).mulVec w i.succ = ∑ j, w j * v j i := by
  simp [Matrix.mulVec, dotProduct, simplexVertexMatrix, mul_comm]

theorem simplexWeights_equation {n : ℕ} {K : Type*} [Field K]
    (v : Fin (n + 1) → Fin n → K) (x : Fin n → K)
    (hv : IsUnit (simplexVertexMatrix v).det) :
    (simplexVertexMatrix v).mulVec (simplexWeights v x) = Fin.cons 1 x := by
  rw [simplexWeights, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hv, Matrix.one_mulVec]

theorem simplexWeights_sum {n : ℕ} {K : Type*} [Field K]
    (v : Fin (n + 1) → Fin n → K) (x : Fin n → K)
    (hv : IsUnit (simplexVertexMatrix v).det) : ∑ j, simplexWeights v x j = 1 := by
  have h := congrFun (simplexWeights_equation v x hv) 0
  simpa only [simplexVertexMatrix_mulVec_head, Fin.cons_zero] using h

theorem simplexWeights_combination {n : ℕ} {K : Type*} [Field K]
    (v : Fin (n + 1) → Fin n → K) (x : Fin n → K)
    (hv : IsUnit (simplexVertexMatrix v).det) :
    ∑ j, simplexWeights v x j • v j = x := by
  funext i
  have h := congrFun (simplexWeights_equation v x hv) i.succ
  simpa only [simplexVertexMatrix_mulVec_tail, Fin.cons_succ, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using h

theorem simplexWeights_eq_of_certificate {n : ℕ} {K : Type*} [Field K]
    (v : Fin (n + 1) → Fin n → K) (x : Fin n → K)
    (hv : IsUnit (simplexVertexMatrix v).det) (w : Fin (n + 1) → K)
    (hw : (simplexVertexMatrix v).mulVec w = Fin.cons 1 x) :
    simplexWeights v x = w := by
  apply Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hv)
  rw [simplexWeights_equation v x hv, hw]

theorem simplexWeights_mem_convexHull {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ)
    (hv : IsUnit (simplexVertexMatrix v).det)
    (hw : ∀ j, 0 ≤ simplexWeights v x j) : x ∈ convexHull ℝ (Set.range v) := by
  exact mem_convexHull_of_exists_fintype (simplexWeights v x) v hw
    (simplexWeights_sum v x hv) (fun j => Set.mem_range_self j)
    (simplexWeights_combination v x hv)

theorem continuous_simplexVertexMatrix {n : ℕ} :
    Continuous (simplexVertexMatrix :
      (Fin (n + 1) → Fin n → ℝ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · change Continuous (fun _ : Fin (n + 1) → Fin n → ℝ => fun _ : Fin (n + 1) => (1 : ℝ))
    exact continuous_const
  · change Continuous (fun v : Fin (n + 1) → Fin n → ℝ => fun j => v j k)
    fun_prop

theorem continuous_simplexWeights_point {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℝ) : Continuous (simplexWeights v) := by
  unfold simplexWeights
  apply Continuous.matrix_mulVec continuous_const
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · exact continuous_const
  · fun_prop

theorem simplexWeights_pos_mem_interior {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ)
    (hv : IsUnit (simplexVertexMatrix v).det)
    (hw : ∀ j, 0 < simplexWeights v x j) :
    x ∈ interior (convexHull ℝ (Set.range v)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hpos : ∀ᶠ y in 𝓝 x, ∀ j, 0 < simplexWeights v y j := by
    apply Filter.eventually_all.mpr
    intro j
    have hj : ContinuousAt (fun y => simplexWeights v y j) x :=
      ((continuous_apply j).comp (continuous_simplexWeights_point v)).continuousAt
    exact hj.eventually (lt_mem_nhds (hw j))
  exact Filter.mem_of_superset hpos fun y hy =>
    simplexWeights_mem_convexHull v y hv (fun j => (hy j).le)

theorem continuousAt_simplexWeights_vertices {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ)
    (hv : (simplexVertexMatrix v).det ≠ 0) :
    ContinuousAt (fun u => simplexWeights u x) v := by
  have hi : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (simplexVertexMatrix v) :=
    continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hv)
  have hmat := hi.comp continuous_simplexVertexMatrix.continuousAt
  unfold simplexWeights
  have hmvec : Continuous (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      A.mulVec (Fin.cons 1 x)) := Continuous.matrix_mulVec continuous_id continuous_const
  exact hmvec.continuousAt.comp hmat

theorem eventually_simplex_positive_certificate {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℝ) (x : Fin n → ℝ)
    (hv : (simplexVertexMatrix v).det ≠ 0)
    (hw : ∀ j, 0 < simplexWeights v x j) :
    ∀ᶠ u in 𝓝 v, (simplexVertexMatrix u).det ≠ 0 ∧
      ∀ j, 0 < simplexWeights u x j := by
  have hdet : ∀ᶠ u in 𝓝 v, (simplexVertexMatrix u).det ≠ 0 :=
    continuous_simplexVertexMatrix.matrix_det.continuousAt.eventually
      (isOpen_ne.mem_nhds hv)
  have hpos : ∀ᶠ u in 𝓝 v, ∀ j, 0 < simplexWeights u x j := by
    apply Filter.eventually_all.mpr
    intro j
    exact ((continuous_apply j).continuousAt.comp
      (continuousAt_simplexWeights_vertices v x hv)).eventually (lt_mem_nhds (hw j))
  exact hdet.and hpos

def surroundingSimplex {n : ℕ} (c : Fin n → ℝ) (δ : ℝ) :
    Fin (n + 1) → Fin n → ℝ :=
  Fin.cons (fun i => c i - δ) (fun j i => c i + if j = i then δ else 0)

theorem surroundingSimplex_combination {n : ℕ} (c : Fin n → ℝ) (δ : ℝ)
    (w : Fin (n + 1) → ℝ) (i : Fin n) :
    (∑ j, w j * surroundingSimplex c δ j i) =
      c i * (∑ j, w j) + δ * (w i.succ - w 0) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [surroundingSimplex, Fin.cons_zero, Fin.cons_succ, mul_add,
    Finset.sum_add_distrib]
  have heq : (∑ j : Fin n, w j.succ * (if j = i then δ else 0)) = w i.succ * δ := by
    simp
  rw [heq, ← Finset.sum_mul]
  ring

theorem surroundingSimplex_det_ne_zero {n : ℕ} (c : Fin n → ℝ) {δ : ℝ}
    (hδ : 0 < δ) : (simplexVertexMatrix (surroundingSimplex c δ)).det ≠ 0 := by
  have hker : ∀ w, (simplexVertexMatrix (surroundingSimplex c δ)).mulVec w = 0 → w = 0 := by
    intro w hw
    have hsum : (∑ j, w j) = 0 := by
      simpa only [simplexVertexMatrix_mulVec_head, Pi.zero_apply] using congrFun hw 0
    have htail (i : Fin n) : w i.succ = w 0 := by
      have h := congrFun hw i.succ
      rw [simplexVertexMatrix_mulVec_tail, surroundingSimplex_combination, hsum] at h
      simp only [Pi.zero_apply, mul_zero, zero_add] at h
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hδ.ne')
    have hc : w = fun _ => w 0 := by
      funext j
      exact Fin.cases rfl htail j
    have hzero : w 0 = 0 := by
      rw [hc] at hsum
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      exact (mul_eq_zero.mp hsum).resolve_left (by positivity)
    rw [hc, hzero]
    rfl
  have hinj : Function.Injective (simplexVertexMatrix (surroundingSimplex c δ)).mulVec := by
    intro w z hwz
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hwz, sub_self]
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

theorem surroundingSimplex_weights {n : ℕ} (c : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    simplexWeights (surroundingSimplex c δ) c = fun _ => 1 / (n + 1 : ℝ) := by
  have hv := isUnit_iff_ne_zero.mpr (surroundingSimplex_det_ne_zero c hδ)
  apply simplexWeights_eq_of_certificate _ _ hv
  have hsum : (∑ _j : Fin (n + 1), 1 / (n + 1 : ℝ)) = 1 := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    simp [div_eq_mul_inv, hn]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [simplexVertexMatrix_mulVec_head, hsum]
    simp
  · rw [simplexVertexMatrix_mulVec_tail, surroundingSimplex_combination, hsum]
    simp

theorem surroundingSimplex_center_mem_interior {n : ℕ} (c : Fin n → ℝ) {δ : ℝ}
    (hδ : 0 < δ) : c ∈ interior (convexHull ℝ (Set.range (surroundingSimplex c δ))) := by
  apply simplexWeights_pos_mem_interior _ _
    (isUnit_iff_ne_zero.mpr (surroundingSimplex_det_ne_zero c hδ))
  intro j
  rw [surroundingSimplex_weights c hδ]
  positivity

def positiveSimplexInterior {n : ℕ} (C : ℝ) : Set (Fin n → ℝ) :=
  {u | (∀ i, 0 < u i) ∧ (∑ i, u i) < C}

theorem isOpen_positiveSimplexInterior {n : ℕ} (C : ℝ) :
    IsOpen (positiveSimplexInterior (n := n) C) := by
  change IsOpen ({u : Fin n → ℝ | ∀ i, 0 < u i} ∩ {u | (∑ i, u i) < C})
  apply IsOpen.inter
  · rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_lt (by fun_prop) continuous_const

theorem exists_surroundingSimplex_inside {n : ℕ} (c : Fin n → ℝ) {C : ℝ}
    (hc : c ∈ positiveSimplexInterior C) :
    ∃ δ > 0, ∀ j, surroundingSimplex c δ j ∈ positiveSimplexInterior C := by
  have hevent : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ j,
      surroundingSimplex c δ j ∈ positiveSimplexInterior C := by
    apply Filter.eventually_all.mpr
    intro j
    have hj : Continuous (fun δ : ℝ => surroundingSimplex c δ j) := by
      apply continuous_pi
      intro i
      refine Fin.cases ?_ (fun k => ?_) j
      · change Continuous (fun δ : ℝ => c i - δ)
        fun_prop
      · change Continuous (fun δ : ℝ => c i + if k = i then δ else 0)
        by_cases hki : k = i <;> simp only [hki, ite_true, ite_false] <;> fun_prop
    exact hj.continuousAt.eventually ((isOpen_positiveSimplexInterior C).mem_nhds
      (by
        have heq : surroundingSimplex c 0 j = c := by
          refine Fin.cases ?_ (fun k => ?_) j <;> simp [surroundingSimplex]
        change surroundingSimplex c 0 j ∈ positiveSimplexInterior C
        rwa [heq]))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r / 2, half_pos hr, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
  linarith

/-- A positive barycentric certificate transfers interior approximation to
an actual finite simplex of exponents, all chosen in the same degree. -/
theorem equality_mean_eventually_surrounds_point {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (c : Fin n → ℝ)
    {C : ℝ} (hm : Tendsto m atTop atTop) (hC : 0 < C)
    (hc : c ∈ positiveSimplexInterior C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, ∃ g : Fin (n + 1) → Fin n → ℕ,
      (∀ j, g j ∈ E k) ∧
      (simplexVertexMatrix (fun j i => (g j i : ℝ) / m k)).det ≠ 0 ∧
      (∀ j, 0 < simplexWeights (fun j i => (g j i : ℝ) / m k) c j) ∧
      c ∈ interior (convexHull ℝ (Set.range (fun j i => (g j i : ℝ) / m k))) := by
  classical
  obtain ⟨δ, hδ, hinside⟩ := exists_surroundingSimplex_inside c hc
  let v := surroundingSimplex c δ
  have hdet := surroundingSimplex_det_ne_zero c hδ
  have hweights : ∀ j, 0 < simplexWeights v c j := by
    intro j
    dsimp only [v]
    rw [surroundingSimplex_weights c hδ]
    positivity
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_simplex_positive_certificate v c hdet hweights)
  let U : Finset (Fin n → ℝ) := Finset.univ.image v
  have hU : ∀ u ∈ U, u ∈ positiveSimplexInterior C := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact hinside j
  have happ := equality_mean_eventually_approximates_finite_family E m U hm hC hr
    (fun u hu => (hU u hu).1) (fun u hu => (hU u hu).2) hcard hmean
  filter_upwards [happ] with k hk
  have hj : ∀ j, ∃ γ ∈ E k, ∀ i, |(γ i : ℝ) / m k - v j i| < r := by
    intro j
    exact hk (v j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  choose g hg hclose using hj
  have hdist : (fun j i => (g j i : ℝ) / m k) ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr]
    intro j
    rw [pi_norm_lt_iff hr]
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hclose j i
  obtain ⟨hd, hp⟩ := hball hdist
  exact ⟨g, hg, hd, hp,
    simplexWeights_pos_mem_interior _ c (isUnit_iff_ne_zero.mpr hd) hp⟩

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureTaylor
public import MixedFujita.MixedRestrictedForms

/-!
Restricted forms on the closure of a point come from sections on the ambient scheme (step 4). Let
W be the closure of a point η of an integral scheme X over K, ι its closed immersion, y a point of
W with completion coordinates, and J_i divisors on X with local equations v_i at ι(y). For a
multidegree a, the divisor Σ_{i<s} a_i J_i has the local equation ∏ v_i^{a_i}, and the images Ψ_a
at y of its sections multiply: Ψ_a · Ψ_b ≤ Ψ_{a+b}. If every N J_i has a section with Ψ = 1, the
images grow with a. For the hyperplane divisors J_i of morphisms e_i to projective spaces, the
chart forms X_k^N give such sections, and a form F of degree D gives a section of D J_i on X and one
on W for the composite ι ≫ e_i, both with the germ of F/X_k^D as local coefficient, so Ψ of the
first is the Taylor expansion at y of the second. Hence the restricted forms of degree D for
ι ≫ e_i lie in Ψ_{D δ_i}, and for k < s the partial product spaces U_k of the mixed bound (13) on W
lie in the image of the sections of the divisor of multidegree (q + k (d+1), q, …, q, 0, …): the
products of restricted forms on W are restrictions of sections on X.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

variable {η : X} (y : pointClosureScheme η)

section MultiDegree

variable {m : ℕ}
  (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
    ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin m) K)

/-- Equal divisors with equal local equations have the same image. -/
theorem pointClosureSectionTaylor_range_congr {D D' : CartierDivisor X} (hD : D = D')
    {f f' : X.functionFieldˣ} (hff : f = f') (hf : D.IsLocalEquationAt (pointClosureι η y) f)
    (hf' : D'.IsLocalEquationAt (pointClosureι η y) f') :
    LinearMap.range (pointClosureSectionTaylor D y f hf coords) =
      LinearMap.range (pointClosureSectionTaylor D' y f' hf' coords) := by
  subst hD hff
  rfl

variable (J : ℕ → CartierDivisor X) (v : ℕ → X.functionFieldˣ)

/-- The divisor Σ_{i<s} a_i J_i of a multidegree a. -/
noncomputable def pointClosureMultiDivisor (s : ℕ) (a : ℕ → ℕ) : CartierDivisor X :=
  ∑ i ∈ Finset.range s, a i • J i

/-- The local equation ∏_{i<s} v_i^{a_i} of the divisor of a multidegree. -/
noncomputable def pointClosureMultiUnit (s : ℕ) (a : ℕ → ℕ) : X.functionFieldˣ :=
  ∏ i ∈ Finset.range s, v i ^ a i

theorem pointClosureMultiDivisor_add (s : ℕ) (a b : ℕ → ℕ) :
    pointClosureMultiDivisor J s a + pointClosureMultiDivisor J s b =
      pointClosureMultiDivisor J s (a + b) := by
  simp only [pointClosureMultiDivisor, ← Finset.sum_add_distrib, Pi.add_apply, add_smul]

theorem pointClosureMultiUnit_mul (s : ℕ) (a b : ℕ → ℕ) :
    pointClosureMultiUnit v s a * pointClosureMultiUnit v s b =
      pointClosureMultiUnit v s (a + b) := by
  simp only [pointClosureMultiUnit, ← Finset.prod_mul_distrib, Pi.add_apply, pow_add]

theorem pointClosureMultiDivisor_const (s j : ℕ) :
    pointClosureMultiDivisor J s (fun _ => j) = j • ∑ i ∈ Finset.range s, J i := by
  rw [pointClosureMultiDivisor, Finset.smul_sum]

theorem pointClosureMultiUnit_const (s j : ℕ) :
    pointClosureMultiUnit v s (fun _ => j) = (∏ i ∈ Finset.range s, v i) ^ j := by
  rw [pointClosureMultiUnit, Finset.prod_pow]

variable (hJ : ∀ i, (J i).IsLocalEquationAt (pointClosureι η y) (v i))

include hJ in
theorem pointClosureMulti_isLocalEquationAt (s : ℕ) (a : ℕ → ℕ) :
    (pointClosureMultiDivisor J s a).IsLocalEquationAt (pointClosureι η y)
      (pointClosureMultiUnit v s a) := by
  induction s with
  | zero =>
    rw [pointClosureMultiDivisor, pointClosureMultiUnit, Finset.sum_range_zero,
      Finset.prod_range_zero]
    exact CartierDivisor.isLocalEquationAt_zero _
  | succ s ih =>
    rw [pointClosureMultiDivisor, pointClosureMultiUnit, Finset.sum_range_succ,
      Finset.prod_range_succ]
    exact ih.mul (cartierLocalEquation_pow _ _ _ (hJ s) (a s))

/-- The image at y of the sections of the divisor of a multidegree. -/
noncomputable def pointClosureMultiRange (s : ℕ) (a : ℕ → ℕ) :
    Submodule K (MvPowerSeries (Fin m) K) :=
  LinearMap.range (pointClosureSectionTaylor (pointClosureMultiDivisor J s a) y
    (pointClosureMultiUnit v s a) (pointClosureMulti_isLocalEquationAt y J v hJ s a) coords)

/-- Products of images: Ψ_a · Ψ_b ≤ Ψ_{a+b}. -/
theorem pointClosureMultiRange_mul (s : ℕ) (a b : ℕ → ℕ) :
    pointClosureMultiRange y coords J v hJ s a * pointClosureMultiRange y coords J v hJ s b ≤
      pointClosureMultiRange y coords J v hJ s (a + b) :=
  (pointClosureSectionTaylor_range_mul _ _ y _ _ _ _ coords).trans
    (pointClosureSectionTaylor_range_congr y coords (pointClosureMultiDivisor_add J s a b)
      (pointClosureMultiUnit_mul v s a b) _ _).le

/-- The image of the sections of N J_i lies in the image of the multidegree N δ_i. -/
theorem pointClosureSectionTaylor_range_le_multiRange (s i : ℕ) (hi : i < s) (N : ℕ) :
    LinearMap.range (pointClosureSectionTaylor (N • J i) y (v i ^ N)
        (cartierLocalEquation_pow _ _ _ (hJ i) N) coords) ≤
      pointClosureMultiRange y coords J v hJ s (Pi.single i N) := by
  refine (pointClosureSectionTaylor_range_congr y coords ?_ ?_ _ _).le
  · rw [pointClosureMultiDivisor, Finset.sum_eq_single i, Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h
      exact absurd (Finset.mem_range.mpr hi) h
  · rw [pointClosureMultiUnit, Finset.prod_eq_single i, Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, pow_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr hi) h

variable (h1 : ∀ i N, (1 : MvPowerSeries (Fin m) K) ∈ LinearMap.range
  (pointClosureSectionTaylor (N • J i) y (v i ^ N) (cartierLocalEquation_pow _ _ _ (hJ i) N) coords))

include h1 in
/-- If every N J_i has a section restricting to 1, so does every multidegree. -/
theorem one_mem_pointClosureMultiRange (s : ℕ) (a : ℕ → ℕ) :
    (1 : MvPowerSeries (Fin m) K) ∈ pointClosureMultiRange y coords J v hJ s a := by
  induction s with
  | zero =>
    have hc := pointClosureSectionTaylor_range_congr y coords (D := 0 • J 0)
      (D' := pointClosureMultiDivisor J 0 a) (f := v 0 ^ 0) (f' := pointClosureMultiUnit v 0 a)
      (by rw [zero_smul, pointClosureMultiDivisor, Finset.sum_range_zero])
      (by rw [pow_zero, pointClosureMultiUnit, Finset.prod_range_zero])
      (cartierLocalEquation_pow _ _ _ (hJ 0) 0) (pointClosureMulti_isLocalEquationAt y J v hJ 0 a)
    unfold pointClosureMultiRange
    rw [← hc]
    exact h1 0 0
  | succ s ih =>
    have h := Submodule.mul_mem_mul ih (h1 s (a s))
    rw [mul_one] at h
    have hle : pointClosureMultiRange y coords J v hJ s a *
        LinearMap.range (pointClosureSectionTaylor (a s • J s) y (v s ^ a s)
          (cartierLocalEquation_pow _ _ _ (hJ s) (a s)) coords) ≤
        pointClosureMultiRange y coords J v hJ (s + 1) a :=
      (pointClosureSectionTaylor_range_mul _ _ y _ _ _ _ coords).trans
        (pointClosureSectionTaylor_range_congr y coords
          (by simp only [pointClosureMultiDivisor, Finset.sum_range_succ])
          (by simp only [pointClosureMultiUnit, Finset.prod_range_succ]) _ _).le
    exact hle h

include h1 in
/-- The images grow with the multidegree. -/
theorem pointClosureMultiRange_mono (s : ℕ) {a b : ℕ → ℕ} (hab : ∀ i < s, a i ≤ b i) :
    pointClosureMultiRange y coords J v hJ s a ≤ pointClosureMultiRange y coords J v hJ s b := by
  have hc : pointClosureMultiRange y coords J v hJ s (a + (b - a)) =
      pointClosureMultiRange y coords J v hJ s b := by
    unfold pointClosureMultiRange
    apply pointClosureSectionTaylor_range_congr
    · unfold pointClosureMultiDivisor
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Pi.add_apply, Pi.sub_apply, Nat.add_sub_cancel' (hab i (Finset.mem_range.mp hi))]
    · unfold pointClosureMultiUnit
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Pi.add_apply, Pi.sub_apply, Nat.add_sub_cancel' (hab i (Finset.mem_range.mp hi))]
  calc pointClosureMultiRange y coords J v hJ s a
      = pointClosureMultiRange y coords J v hJ s a * 1 := (mul_one _).symm
    _ ≤ pointClosureMultiRange y coords J v hJ s a *
        pointClosureMultiRange y coords J v hJ s (b - a) :=
      mul_le_mul' le_rfl
        (Submodule.one_le.mpr (one_mem_pointClosureMultiRange y coords J v hJ h1 s _))
    _ ≤ pointClosureMultiRange y coords J v hJ s (a + (b - a)) :=
      pointClosureMultiRange_mul y coords J v hJ s a (b - a)
    _ = pointClosureMultiRange y coords J v hJ s b := hc

end MultiDegree

section Forms

variable {n : ℕ → ℕ} (e : ∀ i, X ⟶ polynomialProjectiveScheme (n i) K)
  (g : ∀ i, MvPolynomial (Fin (n i)) K) (hg : ∀ i, (g i).IsHomogeneous 1)
  (hggen : ∀ i, g i ∉ ((e i) (genericPoint X)).asHomogeneousIdeal)
  (hgW : ∀ i, g i ∉
    ((pointClosureι η ≫ e i) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
  (he : ∀ i, e i ≫ polynomialProjectiveToBase (n i) K = X ↘ Spec (CommRingCat.of K))
  (jW : ∀ i,
    {k : Fin (n i) // Nonempty (projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) k)})
  (hyj : ∀ i, y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) (jW i).val)
  {d : ℕ}
  (coords : AdicCompletion (IsLocalRing.maximalIdeal ((pointClosureScheme η).presheaf.stalk y))
    ((pointClosureScheme η).presheaf.stalk y) ≃ₐ[K] MvPowerSeries (Fin (d + 1)) K)

omit [IsIntegral X] in
include he in
/-- The composites ι ≫ e_i are over K. -/
theorem pointClosureι_comp_toBase (i : ℕ) :
    (pointClosureι η ≫ e i) ≫ polynomialProjectiveToBase (n i) K =
      pointClosureScheme η ↘ Spec (CommRingCat.of K) := by
  rw [Category.assoc, he i]
  rfl

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] in
theorem pointClosureι_mem_coordinateOpen {i : ℕ} {k : Fin (n i)}
    (h : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e i) k) :
    pointClosureι η y ∈ projectivePullbackCoordinateOpen (e i) k := by
  rw [projectivePullbackCoordinateOpen, Scheme.Hom.comp_preimage] at h
  rw [projectivePullbackCoordinateOpen]
  exact (Scheme.Hom.mem_preimage _).mp h

/-- The chart of e_i at ι(y) given by the chart of ι ≫ e_i at y. -/
def pointClosureChart (i : ℕ) :
    {k : Fin (n i) // Nonempty (projectivePullbackCoordinateOpen (e i) k)} :=
  ⟨(jW i).val, ⟨⟨pointClosureι η y, pointClosureι_mem_coordinateOpen y e (hyj i)⟩⟩⟩

omit [X.Over (Spec (CommRingCat.of K))] in
theorem pointClosureChart_isLocalEquationAt (i : ℕ) :
    (projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)).IsLocalEquationAt
      (pointClosureι η y)
      (projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i)) :=
  projectiveHyperplane_isLocalEquationAt (e i) (g i) (hg i) (hggen i) _ (pointClosureι η y)
    (pointClosureι_mem_coordinateOpen y e (hyj i))

/-- The chart forms X_k^N give sections of N J_i restricting to 1. -/
theorem one_mem_range_pointClosureSectionTaylor_chart (i N : ℕ) :
    (1 : MvPowerSeries (Fin (d + 1)) K) ∈ LinearMap.range (pointClosureSectionTaylor
      (N • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)) y
      (projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) ^ N)
      (cartierLocalEquation_pow _ _ _
        (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj i) N) coords) := by
  refine ⟨projectiveFormSection (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) N
    (MvPolynomial.X (pointClosureChart y e jW hyj i).val ^ N)
    (MvPolynomial.isHomogeneous_X_pow _ N), ?_⟩
  rw [pointClosureSectionTaylor_apply, projectiveFormSection_localCoefficient (e i) (g i) (hg i)
    (hggen i) (pointClosureChart y e jW hyj i) (pointClosureChart y e jW hyj i) (pointClosureι η y)
    (pointClosureι_mem_coordinateOpen y e (hyj i)), projectivePullbackHomogeneousEquation_eq_affine,
    map_pow, projectiveDehomogenize_X_self, one_pow, map_one, map_one, map_one]

/-- A form of degree D: Ψ of its section on X is the Taylor expansion at y of its section on W. -/
theorem pointClosureSectionTaylor_projectiveFormSection (i D : ℕ)
    (F : MvPolynomial (Fin (n i)) K) (hF : F.IsHomogeneous D) :
    pointClosureSectionTaylor (D • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)) y
        (projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) ^ D)
        (cartierLocalEquation_pow _ _ _
          (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj i) D) coords
        (projectiveFormSection (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) D F
          hF) =
      mixedHyperplaneTaylor (fun i => pointClosureι η ≫ e i) g hg hgW y coords jW hyj i D
        (projectiveFormSection (pointClosureι η ≫ e i) (g i) (hg i) (hgW i) (jW i) D F hF) := by
  rw [pointClosureSectionTaylor_apply, projectiveFormSection_localCoefficient (e i) (g i) (hg i)
    (hggen i) (pointClosureChart y e jW hyj i) (pointClosureChart y e jW hyj i) (pointClosureι η y)
    (pointClosureι_mem_coordinateOpen y e (hyj i)), mixedHyperplaneTaylor,
    cartierTaylorCoordinates_apply, projectiveFormSection_localCoefficient (pointClosureι η ≫ e i)
    (g i) (hg i) (hgW i) (jW i) (jW i) y (hyj i),
    pointClosureTaylor_apply, Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- The restricted forms of degree D for ι ≫ e_i lie in the image of the sections of D J_i. -/
theorem mixedFormTaylorSpace_le_pointClosureSectionTaylor_range (D i : ℕ) :
    mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
        (pointClosureι_comp_toBase e he) y coords jW hyj D i ≤
      LinearMap.range (pointClosureSectionTaylor
        (D • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)) y
        (projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) ^ D)
        (cartierLocalEquation_pow _ _ _
          (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj i) D) coords) := by
  rintro _ ⟨⟨_, F, rfl⟩, rfl⟩
  exact ⟨projectiveFormSection (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i) D
    F.1 ((MvPolynomial.mem_homogeneousSubmodule D F.1).mp F.2),
    pointClosureSectionTaylor_projectiveFormSection y e g hg hggen hgW jW hyj coords i D F.1 _⟩

/-- The multidegree images for the hyperplane divisors J_i. -/
noncomputable abbrev pointClosureHyperplaneRange (s : ℕ) (a : ℕ → ℕ) :
    Submodule K (MvPowerSeries (Fin (d + 1)) K) :=
  pointClosureMultiRange y coords
    (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
    (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (pointClosureChart y e jW hyj i))
    (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) s a

/-- For k < s, the partial product space U_k of the mixed bound on W lies in the image of the
sections of the divisor of multidegree (q + k (d+1), q, …, q, 0, …). -/
theorem mixedProductSpace_le_pointClosureHyperplaneRange (q s k : ℕ) (hk : k < s) :
    mixedProductSpace
        (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj q)
        (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) k ≤
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s
        (fun l => if l ≤ k then q + k * (d + 1) else 0) := by
  have h1 := one_mem_range_pointClosureSectionTaylor_chart y e g hg hggen jW hyj coords
  have hform : ∀ D i, i < s → mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
      (pointClosureι_comp_toBase e he) y coords jW hyj D i ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s (Pi.single i D) :=
    fun D i hi =>
      (mixedFormTaylorSpace_le_pointClosureSectionTaylor_range y e g hg hggen hgW he jW hyj coords
        D i).trans (pointClosureSectionTaylor_range_le_multiRange y coords
          (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
          (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
            (pointClosureChart y e jW hyj i))
          (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) s i hi D)
  have hmono : ∀ {a b : ℕ → ℕ}, (∀ l < s, a l ≤ b l) →
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s a ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s b := fun hab =>
    pointClosureMultiRange_mono y coords
      (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
      (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
        (pointClosureChart y e jW hyj i))
      (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) h1 s hab
  have hmul : ∀ a b : ℕ → ℕ,
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s a *
          pointClosureHyperplaneRange y e g hg hggen jW hyj coords s b ≤
        pointClosureHyperplaneRange y e g hg hggen jW hyj coords s (a + b) := fun a b =>
    pointClosureMultiRange_mul y coords
      (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
      (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
        (pointClosureChart y e jW hyj i))
      (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) s a b
  induction k with
  | zero =>
    refine (hform q 0 hk).trans (hmono fun l _ => ?_)
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · rw [Pi.single_eq_of_ne (by omega)]
      exact Nat.zero_le _
  | succ k ih =>
    have hU := mul_le_mul' (mul_le_mul' (ih (by omega)) (hform q (k + 1) hk))
      (hform (d + 1) 0 (by omega))
    refine hU.trans ((mul_le_mul' (hmul _ _) le_rfl).trans ((hmul _ _).trans (hmono fun l _ => ?_)))
    simp only [Pi.add_apply, Pi.single_apply]
    rw [add_one_mul]
    split_ifs <;> omega


/-- With k = s - 1: U_{s-1} lies in the image of the sections of (q + (s-1)(d+1)) Σ_{i<s} J_i. -/
theorem mixedProductSpace_le_pointClosureHyperplaneRange_const (q s : ℕ) (hs : 1 ≤ s) :
    mixedProductSpace
        (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj q)
        (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
          (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) (s - 1) ≤
      pointClosureHyperplaneRange y e g hg hggen jW hyj coords s
        (fun _ => q + (s - 1) * (d + 1)) :=
  (mixedProductSpace_le_pointClosureHyperplaneRange y e g hg hggen hgW he jW hyj coords q s (s - 1)
    (by omega)).trans
    (pointClosureMultiRange_mono y coords
      (fun i => projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i))
      (fun i => projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i)
        (pointClosureChart y e jW hyj i))
      (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj)
      (one_mem_range_pointClosureSectionTaylor_chart y e g hg hggen jW hyj coords) s fun l _ => by
        split_ifs <;> omega)

end Forms

end MixedFujita

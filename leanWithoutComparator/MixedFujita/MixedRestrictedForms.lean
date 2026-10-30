/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveCubeCondition
public import MixedFujita.ProjectiveUniformGrowth

/-!
The mixed bound (13) for a sum of hyperplane classes, without mixed intersection numbers. Let Y be
an actual integral closed subscheme of dimension d + 1, with several embeddings e_i into
polynomial projective spaces and hyperplane classes J_i, and x a closed point with completion
coordinates. Let S_i(q) be the Taylor image at x of the restricted forms of degree q for e_i, and
C the Taylor image of Γ((d+1) J_0), whose initial exponents contain the cube by the cube condition.
The partial product spaces U_0 = S_0, U_{k+1} = U_k · S_{k+1} · C are spans of Taylor expansions
of products of actual sections; multiplying each factor from C by the chart sections X^(d+1) of
(d+1) J_i for 1 ≤ i ≤ k, whose Taylor expansions are 1, these are sections of
(q + k (d+1)) (J_0 + ... + J_k), so U_k lies in the Taylor image of that space (this
interpretation is not used in the proof). Lemma 4 for each e_i with λ = 1
gives ((d+1)! dim S_i(q))^(1/(d+1)) ≥ q, and the mixed Brunn–Minkowski bound gives
((d+1)! dim U_k)^(1/(d+1)) ≥ (k+1) q: the bound (13) for the sum of k + 1 hyperplane classes with
λ = k + 1, uniform in Y and x.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

section Abstract

variable {K : Type*} [Field K] {σ : Type*}

/-- The partial product spaces U_0 = S_0 and U_{k+1} = U_k · S_{k+1} · C. -/
noncomputable def mixedProductSpace (S : ℕ → Submodule K (MvPowerSeries σ K))
    (C : Submodule K (MvPowerSeries σ K)) : ℕ → Submodule K (MvPowerSeries σ K)
  | 0 => S 0
  | k + 1 => mixedProductSpace S C k * S (k + 1) * C

theorem finiteDimensional_mixedProductSpace (S : ℕ → Submodule K (MvPowerSeries σ K))
    (C : Submodule K (MvPowerSeries σ K)) [∀ i, FiniteDimensional K (S i)]
    [FiniteDimensional K C] (k : ℕ) : FiniteDimensional K (mixedProductSpace S C k) := by
  induction k with
  | zero => change FiniteDimensional K (S 0); infer_instance
  | succ k ih =>
    change FiniteDimensional K (mixedProductSpace S C k * S (k + 1) * C)
    rw [← Submodule.fg_iff_finiteDimensional] at ih ⊢
    exact (ih.mul ((Submodule.fg_iff_finiteDimensional _).mpr inferInstance)).mul
      ((Submodule.fg_iff_finiteDimensional _).mpr inferInstance)

variable {D : ℕ}

/-- The mixed bound for the partial product spaces. -/
theorem mixedProductSpace_root_lower (m : MonomialOrder (Fin (D + 1)))
    (S : ℕ → Submodule K (MvPowerSeries (Fin (D + 1)) K))
    (C : Submodule K (MvPowerSeries (Fin (D + 1)) K)) [∀ i, FiniteDimensional K (S i)]
    [FiniteDimensional K C]
    (hcube : binaryVectors (D + 1) ⊆ initialExponentSet m C)
    (hpos : ∀ i, 0 < Module.finrank K (S i)) {q : ℝ}
    (hlow : ∀ i, q ≤ (((D + 1).factorial * Module.finrank K (S i) : ℕ) : ℝ) ^ ((D : ℝ) + 1)⁻¹)
    (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * q ≤
      (((D + 1).factorial * Module.finrank K (mixedProductSpace S C k) : ℕ) : ℝ) ^
        ((D : ℝ) + 1)⁻¹ := by
  have := finiteDimensional_mixedProductSpace S C
  exact mixed_root_sum_lower m S (mixedProductSpace S C) C le_rfl
    (fun k φ hφ ψ hψ χ hχ => Submodule.mul_mem_mul (Submodule.mul_mem_mul hφ hψ) hχ) hcube hpos
    hlow k

end Abstract

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

section Geometric

variable {n : ℕ → ℕ} (e : ∀ i, Y ⟶ polynomialProjectiveScheme (n i) K)
  [∀ i, IsClosedImmersion (e i)] (g : ∀ i, MvPolynomial (Fin (n i)) K)
  (hg : ∀ i, (g i).IsHomogeneous 1) (hggen : ∀ i, g i ∉ ((e i) (genericPoint Y)).asHomogeneousIdeal)
  (he : ∀ i, e i ≫ polynomialProjectiveToBase (n i) K = Y ↘ Spec (CommRingCat.of K))
  {d : ℕ} (x : Y) [IsNoetherianRing (Y.presheaf.stalk x)]
  (coords : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin (d + 1)) K)
  (j : ∀ i, {k : Fin (n i) // Nonempty (projectivePullbackCoordinateOpen (e i) k)})
  (hxj : ∀ i, x ∈ projectivePullbackCoordinateOpen (e i) (j i).val)

/-- The Taylor maps at x of the multiples of the i-th hyperplane class. -/
noncomputable def mixedHyperplaneTaylor (i D : ℕ) :
    Γ((D • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)).sheaf, ⊤) →ₗ[K]
      MvPowerSeries (Fin (d + 1)) K :=
  cartierTaylorCoordinates (D • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)) x
    (projectiveHyperplaneUnit (e i) (g i) (hg i) (hggen i) (j i) ^ D)
    (cartierLocalEquation_pow _ x _
      (projectiveHyperplane_isLocalEquationAt (e i) (g i) (hg i) (hggen i) (j i) x (hxj i)) D)
    coords

/-- The Taylor image at x of the restricted forms of degree q for the i-th embedding. -/
noncomputable def mixedFormTaylorSpace (q i : ℕ) : Submodule K (MvPowerSeries (Fin (d + 1)) K) :=
  LinearMap.range ((mixedHyperplaneTaylor e g hg hggen x coords j hxj i q).comp
    (projectiveFormSectionSpace (e i) (g i) (hg i) (hggen i) (j i) (he i) q).subtype)

/-- The Taylor image at x of Γ((d+1) J_0), which contains the cube. -/
noncomputable def mixedCubeSpace : Submodule K (MvPowerSeries (Fin (d + 1)) K) :=
  LinearMap.range (mixedHyperplaneTaylor e g hg hggen x coords j hxj 0 (d + 1))

instance mixedFormTaylorSpace_finiteDimensional (q i : ℕ) :
    FiniteDimensional K (mixedFormTaylorSpace e g hg hggen he x coords j hxj q i) :=
  LinearMap.finiteDimensional_range _

/-- (13) for a sum of hyperplane classes of several embeddings, with λ the number of summands:
((d+1)! dim U_k)^(1/(d+1)) ≥ (k+1) q for the span U_k of Taylor expansions of products of
restricted forms of degree q for e_0, ..., e_k and k sections of (d+1) J_0. -/
theorem projective_mixed_restrictedForms_lower
    (hn : topologicalKrullDim Y = ((d + 1 : ℕ) : WithBot ℕ∞)) (hx : IsClosed {x})
    [∀ i (D : ℕ), FiniteDimensional K
      Γ((D • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)).sheaf, ⊤)]
    (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * q ≤
      (((d + 1).factorial * Module.finrank K (mixedProductSpace
        (mixedFormTaylorSpace e g hg hggen he x coords j hxj q)
        (mixedCubeSpace e g hg hggen x coords j hxj) k) : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹ := by
  set m := weightedMonomialOrder (finiteLexMonomialOrder (Fin (d + 1))) (fun _ => (1 : ℝ))
    (fun _ => 0) (fun _ => zero_le_one) with hm
  have : FiniteDimensional K (mixedCubeSpace e g hg hggen x coords j hxj) :=
    LinearMap.finiteDimensional_range _
  have hdeg : ∀ a b, m.toSyn a < m.toSyn b → a.degree ≤ b.degree := fun a b h =>
    weightedMonomialOrder_one_degree_le _ _ _ h
  have hcube : binaryVectors (d + 1) ⊆ initialExponentSet m
      (mixedCubeSpace e g hg hggen x coords j hxj) :=
    projectiveHyperplane_binaryVectors_subset (e 0) (g 0) (hg 0) (hggen 0) (j 0) x (hxj 0) hx
      coords m hdeg le_rfl
  have hTinj : ∀ i D,
      Function.Injective (mixedHyperplaneTaylor e g hg hggen x coords j hxj i D) :=
    fun i D => cartierTaylorCoordinates_injective _ x _ _ coords
  have hrank : ∀ i, Module.finrank K (mixedFormTaylorSpace e g hg hggen he x coords j hxj q i) =
      Module.finrank K (projectiveFormSectionSpace (e i) (g i) (hg i) (hggen i) (j i) (he i) q) := by
    intro i
    exact LinearMap.finrank_range_of_inj ((hTinj i q).comp Subtype.val_injective)
  have hlow : ∀ i, (q : ℝ) ≤ (((d + 1).factorial *
      Module.finrank K (mixedFormTaylorSpace e g hg hggen he x coords j hxj q i) : ℕ) : ℝ) ^
        ((d : ℝ) + 1)⁻¹ := by
    intro i
    obtain ⟨r, hr, -, -, hroot⟩ := projective_restrictedForms_root_lower (e i) (g i) (hg i)
      (hggen i) (he i) hn (by omega)
    have h := (hroot (j i) 1 q (by simpa using hr) (by simp)).2
    rw [hrank i]
    have hexp : ((1 : ℝ) / ((d + 1 : ℕ) : ℝ)) = ((d : ℝ) + 1)⁻¹ := by
      push_cast
      rw [one_div]
    simp only [Nat.cast_one, one_pow, one_mul, add_sub_cancel_right, hexp] at h
    exact h
  have hpos : ∀ i,
      0 < Module.finrank K (mixedFormTaylorSpace e g hg hggen he x coords j hxj q i) := by
    intro i
    by_contra h0
    push Not at h0
    have h1 : Module.finrank K (mixedFormTaylorSpace e g hg hggen he x coords j hxj q i) = 0 := by
      omega
    have h2 := hlow i
    rw [h1, mul_zero, Nat.cast_zero, Real.zero_rpow (by positivity)] at h2
    have h3 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact mixedProductSpace_root_lower m _ _ hcube hpos hlow k

end Geometric

end MixedFujita

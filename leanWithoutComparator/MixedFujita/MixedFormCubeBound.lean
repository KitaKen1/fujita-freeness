/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedRestrictedForms

/-!
The mixed bound (13) with forms only (step 4). The cube condition is supplied by forms: for every
S some form section of degree D ≥ d + 1 has initial exponent 1_S
(`projectiveFormSection_initial_cube`), so the initial exponents of the Taylor image of the
restricted forms of degree d + 1 already contain the cube {0,1}^(d+1). With this space in place of
the Taylor image of all of Γ((d+1) J_0), the partial product spaces U_k are spans of Taylor
expansions of products of restricted forms only, and the mixed Brunn–Minkowski bound still gives
((d+1)! dim U_k)^(1/(d+1)) ≥ (k+1) q. Products of restricted forms are restrictions of products
of forms on any variety containing Y in the same projective spaces, so the bound passes to the
sections of an ambient variety restricted to Y.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

variable {n : ℕ → ℕ} (e : ∀ i, Y ⟶ polynomialProjectiveScheme (n i) K)
  [∀ i, IsClosedImmersion (e i)] (g : ∀ i, MvPolynomial (Fin (n i)) K)
  (hg : ∀ i, (g i).IsHomogeneous 1) (hggen : ∀ i, g i ∉ ((e i) (genericPoint Y)).asHomogeneousIdeal)
  (he : ∀ i, e i ≫ polynomialProjectiveToBase (n i) K = Y ↘ Spec (CommRingCat.of K))
  {d : ℕ} (x : Y) [IsNoetherianRing (Y.presheaf.stalk x)]
  (coords : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (Y.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin (d + 1)) K)
  (j : ∀ i, {k : Fin (n i) // Nonempty (projectivePullbackCoordinateOpen (e i) k)})
  (hxj : ∀ i, x ∈ projectivePullbackCoordinateOpen (e i) (j i).val)

/-- The cube condition for the Taylor image of the restricted forms of degree D ≥ d + 1. -/
theorem mixedFormTaylorSpace_binaryVectors_subset (hx : IsClosed {x})
    (m : MonomialOrder (Fin (d + 1))) (hdeg : ∀ q p, m.toSyn q < m.toSyn p → q.degree ≤ p.degree)
    {D : ℕ} (hD : d + 1 ≤ D) (i : ℕ) :
    binaryVectors (d + 1) ⊆
      initialExponentSet m (mixedFormTaylorSpace e g hg hggen he x coords j hxj D i) := by
  classical
  intro γ hγ
  have hγ01 : ∀ l, γ l = 0 ∨ γ l = 1 := by
    intro l
    have h := Fintype.mem_piFinset.mp hγ l
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  obtain ⟨F, hF, hinit⟩ := projectiveFormSection_initial_cube (e i) (g i) (hg i) (hggen i) (j i) x
    (hxj i) hx coords m hdeg hD (Finset.univ.filter fun l => γ l = 1)
  rw [mem_initialExponentSet]
  refine ⟨∑ l ∈ Finset.univ.filter (fun l => γ l = 1), Finsupp.single l 1,
    (mem_initialMonomialFinset m _ _).mpr ⟨_,
      ⟨⟨projectiveFormSection (e i) (g i) (hg i) (hggen i) (j i) D F hF,
        ⟨⟨F, (MvPolynomial.mem_homogeneousSubmodule D F).mpr hF⟩, rfl⟩⟩, rfl⟩, hinit⟩, ?_⟩
  funext l
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rcases hγ01 l with h | h <;> simp [h]

/-- (13) with forms only: ((d+1)! dim U_k)^(1/(d+1)) ≥ (k+1) q for the span U_k of Taylor
expansions of products of restricted forms of degree q for e_0, ..., e_k and k restricted forms of
degree d + 1 for e_0. -/
theorem projective_mixed_formsOnly_lower
    (hn : topologicalKrullDim Y = ((d + 1 : ℕ) : WithBot ℕ∞)) (hx : IsClosed {x})
    (q : ℕ) (hq : 1 ≤ q) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * q ≤
      (((d + 1).factorial * Module.finrank K (mixedProductSpace
        (mixedFormTaylorSpace e g hg hggen he x coords j hxj q)
        (mixedFormTaylorSpace e g hg hggen he x coords j hxj (d + 1) 0) k) : ℕ) : ℝ) ^
          ((d : ℝ) + 1)⁻¹ := by
  set m := weightedMonomialOrder (finiteLexMonomialOrder (Fin (d + 1))) (fun _ => (1 : ℝ))
    (fun _ => 0) (fun _ => zero_le_one) with hm
  have hdeg : ∀ a b, m.toSyn a < m.toSyn b → a.degree ≤ b.degree := fun a b h =>
    weightedMonomialOrder_one_degree_le _ _ _ h
  have hcube := mixedFormTaylorSpace_binaryVectors_subset e g hg hggen he x coords j hxj hx m hdeg
    le_rfl 0
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

end MixedFujita

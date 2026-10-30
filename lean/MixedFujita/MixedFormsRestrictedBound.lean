/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.VeryAmpleNumericalBound
public import MixedFujita.MixedFormsVaryingDegree

/-!
The mixed bound (13) for restricted sections with a given growth of each family of forms
(step 4). Let W be the closure of a point η of an integral scheme X, of dimension d + 1, with a
closed point y and completion coordinates, and let e_l be closed immersions of X into projective
spaces with degree-one forms g_l not vanishing at the generic point of W and hyperplane divisors
J_l. Suppose that for l < s the restricted forms of degree q_l of the l-th embedding span a space
of dimension n_l with λ^(d+1) ≤ (d+1)! n_l. Then for every multidegree b with
b_l ≥ q_l + (s-1)(d+1) for l < s, and every divisor A = Σ_{l<tot} b_l J_l + div P, some
finite-dimensional space of sections of A restricts to W with dimension at least
(s λ)^(d+1) / (d+1)!. The embeddings with index l ≥ s only pad the multidegree with their chart
sections. With λ = q this contains the bound for sums of very ample divisors; with the degree
of W in the l-th embedding it gives the bound for divisors with a very ample multiple.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

section Numerics

/-- From a^(d+1) ≤ N with a ≥ 0: a ≤ N^(1/(d+1)). -/
theorem le_rpow_inv_of_pow_le {d N : ℕ} {a : ℝ} (ha : 0 ≤ a) (h : a ^ (d + 1) ≤ (N : ℝ)) :
    a ≤ (N : ℝ) ^ ((d : ℝ) + 1)⁻¹ := by
  have hz : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [Real.le_rpow_inv_iff_of_pos ha (by positivity) hz]
  have hcast : ((d : ℝ) + 1) = ((d + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast]
  exact h

end Numerics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

variable {η : X} (y : pointClosureScheme η)
  [IsNoetherianRing ((pointClosureScheme η).presheaf.stalk y)]
  {n : ℕ → ℕ} (e : ∀ i, X ⟶ polynomialProjectiveScheme (n i) K) [∀ i, IsClosedImmersion (e i)]
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

include hyj coords in
/-- The mixed bound for restricted sections from the growth of the restricted forms. -/
theorem mixedForms_restrictedSubspaceDim_lower (hyc : IsClosed {y}) (q b : ℕ → ℕ) (tot s : ℕ)
    (hs : 1 ≤ s) (hst : s ≤ tot) (hb : ∀ l < s, q l + (s - 1) * (d + 1) ≤ b l) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hpos : ∀ l < s, 0 < Module.finrank K (projectiveFormSectionSpace (pointClosureι η ≫ e l)
      (g l) (hg l) (hgW l) (jW l) (pointClosureι_comp_toBase e he l) (q l)))
    (hlow : ∀ l < s, lam ^ (d + 1) ≤ (((d + 1).factorial * Module.finrank K
      (projectiveFormSectionSpace (pointClosureι η ≫ e l) (g l) (hg l) (hgW l) (jW l)
        (pointClosureι_comp_toBase e he l) (q l)) : ℕ) : ℝ))
    {A : CartierDivisor X} (P : X.functionFieldˣ)
    (hA : pointClosureMultiDivisor
        (fun l => projectiveHyperplaneCartier (e l) (g l) (hg l) (hggen l)) tot b +
      principalCartierDivisor X P = A) :
    ∃ V : Submodule K Γ(A.sheaf, ⊤), FiniteDimensional K V ∧
      ((s : ℝ) * lam) ^ (d + 1) / (d + 1).factorial ≤ cartierRestrictedSubspaceDim K A η V := by
  set m := weightedMonomialOrder (finiteLexMonomialOrder (Fin (d + 1))) (fun _ => (1 : ℝ))
    (fun _ => 0) (fun _ => zero_le_one) with hm
  have hdeg : ∀ a b, m.toSyn a < m.toSyn b → a.degree ≤ b.degree := fun a b h =>
    weightedMonomialOrder_one_degree_le _ _ _ h
  have hcube := mixedFormTaylorSpace_binaryVectors_subset (fun i => pointClosureι η ≫ e i) g hg hgW
    (pointClosureι_comp_toBase e he) y coords jW hyj hyc m hdeg le_rfl 0
  have hrank : ∀ l D, Module.finrank K (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg
      hgW (pointClosureι_comp_toBase e he) y coords jW hyj D l) =
      Module.finrank K (projectiveFormSectionSpace (pointClosureι η ≫ e l) (g l) (hg l) (hgW l)
        (jW l) (pointClosureι_comp_toBase e he l) D) := fun l D =>
    LinearMap.finrank_range_of_inj
      ((cartierTaylorCoordinates_injective _ y _ _ coords).comp Subtype.val_injective)
  have hroot := mixedProductSpace_root_sum_lower m
    (fun l => mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
      (pointClosureι_comp_toBase e he) y coords jW hyj (q l) l)
    (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
      (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) hcube (s - 1)
    (fun l hl => by
      rw [hrank]
      exact hpos l (by omega))
    (fun _ => lam)
    (fun l hl => by
      rw [hrank]
      exact le_rpow_inv_of_pow_le hlam (hlow l (by omega)))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.sub_add_cancel hs] at hroot
  have hU := mixedProductSpace_le_pointClosureHyperplaneRange_varying y e g hg hggen hgW he jW hyj
    coords q tot (s - 1) (by omega) b (fun l hl => hb l (by omega))
  have hF := pointClosureMulti_isLocalEquationAt y
    (fun l => projectiveHyperplaneCartier (e l) (g l) (hg l) (hggen l))
    (fun l => projectiveHyperplaneUnit (e l) (g l) (hg l) (hggen l)
      (pointClosureChart y e jW hyj l))
    (pointClosureChart_isLocalEquationAt y e g hg hggen jW hyj) tot b
  have hle := hU.trans (pointClosureSectionTaylor_range_le_principal _ y _ P hF coords)
  have : FiniteDimensional K (mixedProductSpace
      (fun l => mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
        (pointClosureι_comp_toBase e he) y coords jW hyj (q l) l)
      (mixedFormTaylorSpace (fun i => pointClosureι η ≫ e i) g hg hgW
        (pointClosureι_comp_toBase e he) y coords jW hyj (d + 1) 0) (s - 1)) :=
    finiteDimensional_mixedProductSpace _ _ _
  obtain ⟨V, hV, hVdim⟩ := exists_le_cartierRestrictedSubspaceDim_of_le_range_of_eq hA y _ _
    coords _ hle
  refine ⟨V, hV, ?_⟩
  have h2 := pow_div_factorial_le_of_le_rpow_inv (by positivity) hroot
  exact h2.trans (by exact_mod_cast hVdim)

end MixedFujita

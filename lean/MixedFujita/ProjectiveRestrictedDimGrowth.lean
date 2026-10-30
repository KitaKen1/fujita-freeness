/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedFormsRestrictedBound
public import MixedFujita.ProjectiveUniformGrowth
public import MixedFujita.StrongNumericalFreenessStatement

/-!
Lemma 4 of the manuscript for the dimensions of the sections restricted to the closure of a
point (the form of the bound (13) used by (20)).

Let X be a closed subscheme of projective space with hyperplane divisor J, η a point of X whose
closure W has dimension d + 1 and such that the degree-one form g does not vanish at η. Lemma 4
for the forms restricted to W (`projective_restrictedForms_root_lower`) gives the degree r of W,
the leading coefficient of h^0(W, D J) = r D^(d+1)/(d+1)! + o(D^(d+1)), and, for s^(d+1) ≤ r, a
lower bound for the dimension of the forms of degree q restricted to W. The restricted forms are
restrictions of sections of q J on X (`mixedForms_restrictedSubspaceDim_lower` with one
embedding), so the same bound holds for the dimension of the sections of q J restricted to W:

  (s (q + 1 - s^(d+1)))^(d+1) ≤ (d+1)! dim (image of Γ(X, q J) on W)   for s^(d+1) ≤ r, q + 1.

The bound depends on W only through the condition s^(d+1) ≤ r.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

section Subspace

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- The restriction of a subspace of sections has at most the dimension of the restriction of all
sections. -/
theorem cartierRestrictedSubspaceDim_le (D : CartierDivisor X) (η : X)
    [FiniteDimensional K Γ(D.sheaf, ⊤)] (V : Submodule K Γ(D.sheaf, ⊤)) :
    cartierRestrictedSubspaceDim K D η V ≤ cartierRestrictedDim K D η :=
  Submodule.finrank_le _

end Subspace

variable {K : Type u} [Field K] [IsAlgClosed K] {N : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  (e : X ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)

/-- Lemma 4 for the sections of q J restricted to the closure W of η: with r the degree of W, for
s^(d+1) ≤ r and s^(d+1) ≤ q + 1 the dimension I of the restricted sections satisfies
(s (q + 1 - s^(d+1)))^(d+1) ≤ (d+1)! I. -/
theorem projectiveHyperplane_cartierRestrictedDim_pow_lower
    (he : e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K)) (η : X) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set X)) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    [∀ q : ℕ, FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)] :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι η ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ (d + 1)) atTop (nhds ((r : ℝ) / (d + 1).factorial)) ∧
      ∀ s q : ℕ, s ^ (d + 1) ≤ r → s ^ (d + 1) ≤ q + 1 →
        (s * (q + 1 - s ^ (d + 1))) ^ (d + 1) ≤ (d + 1).factorial *
          cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) η := by
  have hW : topologicalKrullDim (pointClosureScheme η) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    rw [pointClosureScheme_topologicalKrullDim, hd]
  have heW : (pointClosureι η ≫ e) ≫ polynomialProjectiveToBase N K =
      pointClosureScheme η ↘ Spec (CommRingCat.of K) :=
    pointClosureι_comp_toBase (fun _ : ℕ => e) (fun _ => he) 0
  obtain ⟨r, hr, hfinW, hlim, hunif⟩ := projective_restrictedForms_root_lower
    (pointClosureι η ≫ e) g hg hgW heW hW (Nat.succ_le_succ (Nat.zero_le d))
  refine ⟨r, hr, hfinW, hlim, fun s q hsr hsq => ?_⟩
  by_cases hzero : s * (q + 1 - s ^ (d + 1)) = 0
  · rw [hzero, zero_pow (Nat.succ_ne_zero d)]
    exact Nat.zero_le _
  -- a closed point of W in a coordinate chart, with completion coordinates
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart N K (e η)
  have hgenO : genericPoint (pointClosureScheme η) ∈
      projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k := by
    rw [projectivePullbackCoordinateOpen, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply,
      pointClosureι_genericPoint]
    exact hk
  obtain ⟨y, hyc, hyO, c, hyU⟩ := exists_closedPoint_etaleChart_dim (K := K) hW
    (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k : Set (pointClosureScheme η))
    (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) k).isOpen ⟨_, hgenO⟩
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) c.isAffine y hyU hyc
  obtain ⟨coords, -, -⟩ := etaleChart_exists_taylorCoordinates c y hyU β
  have : IsLocallyNoetherian (pointClosureScheme η) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointClosureScheme η ↘ Spec (CommRingCat.of K))
  obtain ⟨jW, hjW⟩ : ∃ jW : {l : Fin N // Nonempty
      (projectivePullbackCoordinateOpen (pointClosureι η ≫ e) l)}, jW.val = k :=
    ⟨⟨k, ⟨⟨y, hyO⟩⟩⟩, rfl⟩
  have hyj : y ∈ projectivePullbackCoordinateOpen (pointClosureι η ≫ e) jW.val := by
    rw [hjW]
    exact hyO
  obtain ⟨hpow, -⟩ := hunif jW s q hsr hsq
  have hlampos : 0 < s * (q + 1 - s ^ (d + 1)) := Nat.pos_of_ne_zero hzero
  have hpow' : (s * (q + 1 - s ^ (d + 1))) ^ (d + 1) ≤ (d + 1).factorial * Module.finrank K
      (projectiveFormSectionSpace (pointClosureι η ≫ e) g hg hgW jW heW q) := by
    rw [mul_pow]
    exact hpow
  have hfpos : 0 < Module.finrank K
      (projectiveFormSectionSpace (pointClosureι η ≫ e) g hg hgW jW heW q) := by
    by_contra h0
    have h1 : Module.finrank K
        (projectiveFormSectionSpace (pointClosureι η ≫ e) g hg hgW jW heW q) = 0 := by omega
    rw [h1, mul_zero] at hpow'
    have h2 : 0 < (s * (q + 1 - s ^ (d + 1))) ^ (d + 1) := Nat.pow_pos hlampos
    omega
  obtain ⟨V, hV, hVdim⟩ := mixedForms_restrictedSubspaceDim_lower (η := η) y (fun _ : ℕ => e)
    (fun _ => g) (fun _ => hg) (fun _ => hggen) (fun _ => hgW) (fun _ => he) (fun _ => jW)
    (fun _ => hyj) coords hyc (fun _ => q) (fun _ => q) 1 1 le_rfl le_rfl
    (fun l _ => by simp) (lam := ((s * (q + 1 - s ^ (d + 1)) : ℕ) : ℝ)) (Nat.cast_nonneg _)
    (fun _ _ => hfpos) (fun _ _ => by exact_mod_cast hpow')
    (A := q • projectiveHyperplaneCartier e g hg hggen) (1 : X.functionFieldˣ) (by
      rw [pointClosureMultiDivisor_const, Finset.sum_range_one, principalCartierDivisor_one,
        add_zero])
  have hle := cartierRestrictedSubspaceDim_le K (q • projectiveHyperplaneCartier e g hg hggen) η V
  rw [Nat.cast_one, one_mul, div_le_iff₀ (by positivity)] at hVdim
  have h5 : (s * (q + 1 - s ^ (d + 1))) ^ (d + 1) ≤
      cartierRestrictedSubspaceDim K (q • projectiveHyperplaneCartier e g hg hggen) η V *
        (d + 1).factorial := by exact_mod_cast hVdim
  calc (s * (q + 1 - s ^ (d + 1))) ^ (d + 1)
      ≤ cartierRestrictedSubspaceDim K (q • projectiveHyperplaneCartier e g hg hggen) η V *
        (d + 1).factorial := h5
    _ = (d + 1).factorial *
        cartierRestrictedSubspaceDim K (q • projectiveHyperplaneCartier e g hg hggen) η V :=
        mul_comm _ _
    _ ≤ _ := Nat.mul_le_mul_left _ hle

end MixedFujita

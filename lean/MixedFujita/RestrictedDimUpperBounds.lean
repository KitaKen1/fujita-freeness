/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveRestrictedDimGrowth
public import MixedFujita.PointClosureHyperplaneRestriction
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.CartierBigOperations

/-!
Upper bounds for sections and restricted sections (pieces of Kodaira's lemma; step 17).

Kodaira's lemma (a big T and an ample H give a nonzero section of m T − H) is proved by counting:
for an effective divisor E = Σ η_j in |J| whose components avoid the zeros of a section of
a J − T, the sections of m T vanishing at every η_j have codimension at most Σ_j of the dimensions
of the sections restricted at η_j (`finrank_le_finrank_iInf_add_sum_cartierRestrictedDim`), each
of these is at most the one for m a J (`cartierRestrictedDim_le_add_of_not_mem`, multiplication
by a section not vanishing at η_j), and that one grows at most like m^(dim W_j)
(`projectiveHyperplane_exists_cartierRestrictedDim_le_mul_pow`, from Lemma 4's Hilbert limit on
the closure W_j). This file proves these three bounds, together with the linear algebra
(`finrank_le_finrank_iInf_add_sum`) and the bound h⁰(q J) ≤ C (q + 1)^d
(`projectiveHyperplane_exists_finrank_le_mul_pow`, from the Hilbert limit by
`exists_le_mul_succ_pow_of_tendsto`). The division by E (Hartogs), the choice of E (Bertini on a
smooth model) and the assembly are not done here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

section LinearAlgebra

/-- The intersection of finitely many subspaces has codimension at most the sum of their
codimensions. -/
theorem finrank_le_finrank_iInf_add_sum (K : Type*) [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {ι : Type*} [Fintype ι] (U : ι → Submodule K V) :
    Module.finrank K V ≤
      Module.finrank K (⨅ i, U i : Submodule K V) + ∑ i, Module.finrank K (V ⧸ U i) := by
  classical
  let φ : V →ₗ[K] (∀ i, V ⧸ U i) := LinearMap.pi fun i => (U i).mkQ
  have hker : LinearMap.ker φ = ⨅ i, U i := by
    simp only [φ, LinearMap.ker_pi, Submodule.ker_mkQ]
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have hr : Module.finrank K (LinearMap.range φ) ≤ ∑ i, Module.finrank K (V ⧸ U i) :=
    (Submodule.finrank_le _).trans (Module.finrank_pi_fintype K).le
  rw [hker] at h
  omega

end LinearAlgebra

section Sequences

/-- A nonnegative sequence with a finite limit of a_q / q^d is at most C (q + 1)^d. -/
theorem exists_le_mul_succ_pow_of_tendsto {a : ℕ → ℝ} (ha : ∀ q, 0 ≤ a q) {d : ℕ} {L : ℝ}
    (h : Tendsto (fun q : ℕ => a q / (q : ℝ) ^ d) atTop (nhds L)) :
    ∃ C : ℝ, ∀ q : ℕ, a q ≤ C * ((q : ℝ) + 1) ^ d := by
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp (h.eventually (gt_mem_nhds (lt_add_one L)))
  have hsum : 0 ≤ ∑ i ∈ Finset.range (Q + 1), a i := Finset.sum_nonneg fun i _ => ha i
  refine ⟨max (L + 1) 0 + ∑ i ∈ Finset.range (Q + 1), a i, fun q => ?_⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have hpow : (1 : ℝ) ≤ ((q : ℝ) + 1) ^ d := one_le_pow₀ hq1
  have hC : 0 ≤ max (L + 1) 0 + ∑ i ∈ Finset.range (Q + 1), a i :=
    add_nonneg (le_max_right _ _) hsum
  by_cases hq : q ≤ Q ∨ q = 0
  · have hle : a q ≤ ∑ i ∈ Finset.range (Q + 1), a i :=
      Finset.single_le_sum (fun i _ => ha i) (Finset.mem_range.mpr (by omega))
    calc a q ≤ ∑ i ∈ Finset.range (Q + 1), a i := hle
      _ ≤ (max (L + 1) 0 + ∑ i ∈ Finset.range (Q + 1), a i) * 1 := by
        rw [mul_one]; linarith [le_max_right (L + 1) 0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hC
  · have hqQ : Q ≤ q := by omega
    have hq0 : q ≠ 0 := by omega
    have hqpos : (0 : ℝ) < (q : ℝ) ^ d := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq0) d
    have h1 := hQ q hqQ
    rw [div_lt_iff₀ hqpos] at h1
    have hqq : (q : ℝ) ^ d ≤ ((q : ℝ) + 1) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg q) (by linarith) d
    calc a q ≤ (L + 1) * (q : ℝ) ^ d := h1.le
      _ ≤ max (L + 1) 0 * (q : ℝ) ^ d := mul_le_mul_of_nonneg_right (le_max_left _ _) hqpos.le
      _ ≤ max (L + 1) 0 * ((q : ℝ) + 1) ^ d := mul_le_mul_of_nonneg_left hqq (le_max_right _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hsum) (by positivity)

end Sequences

section Hilbert

variable {K : Type u} [Field K] [Infinite K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The sections of q J, for the hyperplane class J of an integral closed subscheme of dimension
d ≥ 1 of projective space, have dimension at most C (q + 1)^d. -/
theorem projectiveHyperplane_exists_finrank_le_mul_pow
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ q : ℕ, (Module.finrank K
      Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤ C * ((q : ℝ) + 1) ^ d := by
  obtain ⟨r, -, -, hlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hn hd
  exact exists_le_mul_succ_pow_of_tendsto (fun q => Nat.cast_nonneg _) hlim

end Hilbert

section Restricted

variable {K : Type u} [Field K] [IsAlgClosed K] {N : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  (e : X ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)

/-- The sections of q J restricted to a point η whose closure W has dimension d + 1 and is not
contained in the hyperplane have dimension at most C (q + 1)^(d + 1). -/
theorem projectiveHyperplane_exists_cartierRestrictedDim_le_mul_pow
    (he : e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K)) (η : X) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set X)) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hgW : g ∉ ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal)
    [∀ q : ℕ, FiniteDimensional K Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)] :
    ∃ C : ℝ, ∀ q : ℕ, (cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) η :
      ℝ) ≤ C * ((q : ℝ) + 1) ^ (d + 1) := by
  obtain ⟨r, -, hfinW, hlim, -⟩ :=
    projectiveHyperplane_cartierRestrictedDim_pow_lower e g hg hggen he η hd hgW
  obtain ⟨C, hC⟩ := exists_le_mul_succ_pow_of_tendsto (fun q => Nat.cast_nonneg _) hlim
  refine ⟨C, fun q => ?_⟩
  have := hfinW q
  exact (Nat.cast_le.mpr
    (projectiveHyperplane_cartierRestrictedDim_le_pointClosure e g hg hggen η hgW q)).trans (hC q)

end Restricted

section Vanishing

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- Multiplication by a section of O(E) that does not vanish at η does not decrease the dimension
of the sections restricted at η. -/
theorem cartierRestrictedDim_le_add_of_not_mem (D E : CartierDivisor X) (η : X)
    (t : Γ(E.sheaf, ⊤)) (ht : t ∉ cartierSectionsVanishingAt K E η)
    [FiniteDimensional K Γ((D + E).sheaf, ⊤)] :
    cartierRestrictedDim K D η ≤ cartierRestrictedDim K (D + E) η := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt η
  obtain ⟨g, hg⟩ := E.exists_isLocalEquationAt η
  have htu : IsUnit (cartierLocalCoefficient E η g hg t) := by
    by_contra h
    exact ht ((mem_cartierSectionsVanishingAt_iff E η g hg t).mpr
      ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)))
  have hcoef : ∀ s : Γ(D.sheaf, ⊤),
      cartierSectionProductLinear (K := K) D E t s ∈ cartierSectionsVanishingAt K (D + E) η ↔
        s ∈ cartierSectionsVanishingAt K D η := by
    intro s
    rw [mem_cartierSectionsVanishingAt_iff (D + E) η (f * g) (hf.mul hg),
      mem_cartierSectionsVanishingAt_iff D η f hf]
    change cartierLocalCoefficient (D + E) η (f * g) (hf.mul hg)
      (cartierSectionProduct D E s t) ∈ _ ↔ _
    rw [cartierSectionProduct_localCoefficient D E η f g hf hg s t]
    exact Ideal.mul_unit_mem_iff_mem _ htu
  have hmaps : cartierSectionsVanishingAt K D η ≤
      (cartierSectionsVanishingAt K (D + E) η).comap (cartierSectionProductLinear (K := K) D E t) :=
    fun s hs => (hcoef s).mpr hs
  have hinj : Function.Injective
      (Submodule.mapQ _ _ (cartierSectionProductLinear (K := K) D E t) hmaps) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (hcoef s).mp hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

/-- The sections of O(D) vanishing at finitely many points have codimension at most the sum of the
dimensions of the sections restricted at those points. -/
theorem finrank_le_finrank_iInf_add_sum_cartierRestrictedDim (D : CartierDivisor X)
    [FiniteDimensional K Γ(D.sheaf, ⊤)] {ι : Type*} [Fintype ι] (η : ι → X) :
    Module.finrank K Γ(D.sheaf, ⊤) ≤
      Module.finrank K (⨅ i, cartierSectionsVanishingAt K D (η i) : Submodule K Γ(D.sheaf, ⊤)) +
        ∑ i, cartierRestrictedDim K D (η i) :=
  finrank_le_finrank_iInf_add_sum K fun i => cartierSectionsVanishingAt K D (η i)

end Vanishing

end MixedFujita

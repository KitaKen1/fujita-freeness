/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrongNumericalFreenessStatement
public import MixedFujita.CartierFiniteProducts

/-!
S-NF for sums of ample divisors and the reduction of F1 to S-NF (step 14), without Segre
embeddings. A Cartier divisor A is an ample sum if a positive multiple m A is linearly equivalent
to a positive combination Σ c_i H_i of hyperplane divisors of finitely many closed immersions
into projective spaces over K. An ample divisor is an ample sum (one term), and a finite sum
L_1 + ⋯ + L_s of ample divisors with m_i L_i ∼ H_i is an ample sum: with M = ∏ m_i,
M Σ L_i ∼ Σ (M/m_i) H_i. S-NF for ample sums implies S-NF; it is the form that the mixed bound
(13) for several hyperplane classes is designed for, and for A = Σ L_i it has the same
conclusion K_X + Σ L_i + N as F1. So F1 follows from S-NF for ample sums together with the
numerical input A^d · W ≥ (n + 1)^d for A = Σ L_i (step 4), written through restricted
sections; ampleness of the sum itself is never needed. The numerical hypotheses are stated for
finite-dimensional subspaces of sections, whose restrictions to W are counted; when the sections
form a finite-dimensional space this is the dimension of all restricted sections, and S-NF in the
form with all sections follows by lifting a basis of the restricted sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section AmpleSum

variable (K : Type u) [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- A positive multiple of A is linearly equivalent to a positive combination of hyperplane
divisors of finitely many closed immersions into projective spaces over K. -/
def CartierIsAmpleSum (A : CartierDivisor Y) : Prop :=
  ∃ (m : ℕ) (_ : 1 ≤ m) (s : ℕ) (_ : 1 ≤ s) (N : Fin s → ℕ)
    (e : ∀ i, Y ⟶ polynomialProjectiveScheme (N i) K) (_ : ∀ i, IsClosedImmersion (e i))
    (_ : ∀ i, e i ≫ polynomialProjectiveToBase (N i) K = Y ↘ Spec (CommRingCat.of K))
    (g : ∀ i, MvPolynomial (Fin (N i)) K) (hg : ∀ i, (g i).IsHomogeneous 1)
    (hggen : ∀ i, g i ∉ (e i (genericPoint Y)).asHomogeneousIdeal)
    (c : Fin s → ℕ) (_ : ∀ i, 1 ≤ c i) (f : Y.functionFieldˣ),
    m • A = ∑ i, c i • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i) +
      principalCartierDivisor Y f

variable {K}

/-- An ample divisor is an ample sum with one term. -/
theorem cartierIsAmpleProj_isAmpleSum {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) :
    CartierIsAmpleSum K A := by
  obtain ⟨m, hm, n, e, he, hbase, g, hg, hggen, f, hmA⟩ := hA
  refine ⟨m, hm, 1, le_rfl, fun _ => n, fun _ => e, fun _ => he, fun _ => hbase, fun _ => g,
    fun _ => hg, fun _ => hggen, fun _ => 1, fun _ => le_rfl, f, ?_⟩
  rw [hmA, Fin.sum_univ_one, one_smul]

/-- A sum of finitely many ample divisors is an ample sum: with m_i L_i ∼ H_i and M = ∏ m_i,
M Σ L_i ∼ Σ (M/m_i) H_i. No Segre embedding is used. -/
theorem cartierIsAmpleSum_sum {s : ℕ} (hs : 1 ≤ s) (L : Fin s → CartierDivisor Y)
    (hL : ∀ i, CartierIsAmpleProj K (L i)) : CartierIsAmpleSum K (∑ i, L i) := by
  choose m hm N e he hbase g hg hggen f hmL using hL
  have hdvd : ∀ i, m i ∣ ∏ j, m j := fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have hM : 1 ≤ ∏ j, m j :=
    Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => by
      have := hm i
      omega)
  refine ⟨∏ j, m j, hM, s, hs, N, e, he, hbase, g, hg, hggen, fun i => (∏ j, m j) / m i,
    fun i => Nat.div_pos (Nat.le_of_dvd hM (hdvd i)) (hm i),
    ∏ i, f i ^ ((∏ j, m j) / m i), ?_⟩
  have h1 : ∀ i, (∏ j, m j) • L i = ((∏ j, m j) / m i) • (m i • L i) := by
    intro i
    rw [smul_smul, Nat.div_mul_cancel (hdvd i)]
  rw [Finset.smul_sum, Finset.sum_congr rfl fun i _ => h1 i]
  simp_rw [hmL, smul_add]
  rw [Finset.sum_add_distrib, principalCartierDivisor_weighted_prod]

end AmpleSum

section Statements

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra

section Subspace

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- The dimension of the image of a subspace V of the sections of D in the sections restricted to
the closure of η. -/
noncomputable def cartierRestrictedSubspaceDim (D : CartierDivisor X) (η : X)
    (V : Submodule K Γ(D.sheaf, ⊤)) : ℕ :=
  Module.finrank K (V.map (cartierSectionsVanishingAt K D η).mkQ)

variable {K}

/-- Some finite-dimensional subspace of sections restricts with the dimension of all sections. -/
theorem exists_finiteDimensional_le_cartierRestrictedSubspaceDim (D : CartierDivisor X) (η : X) :
    ∃ V : Submodule K Γ(D.sheaf, ⊤), FiniteDimensional K V ∧
      cartierRestrictedDim K D η ≤ cartierRestrictedSubspaceDim K D η V := by
  classical
  by_cases hfin : FiniteDimensional K (Γ(D.sheaf, ⊤) ⧸ cartierSectionsVanishingAt K D η)
  · obtain ⟨S, hS⟩ := (Module.Finite.fg_top :
      (⊤ : Submodule K (Γ(D.sheaf, ⊤) ⧸ cartierSectionsVanishingAt K D η)).FG)
    let lift := Function.surjInv (Submodule.mkQ_surjective (cartierSectionsVanishingAt K D η))
    refine ⟨Submodule.span K (lift '' S),
      FiniteDimensional.span_of_finite K (S.finite_toSet.image lift), ?_⟩
    have hid : (fun x => (cartierSectionsVanishingAt K D η).mkQ (lift x)) = id :=
      funext fun x => Function.surjInv_eq _ x
    have hmap : (Submodule.span K (lift '' S)).map (cartierSectionsVanishingAt K D η).mkQ = ⊤ := by
      rw [Submodule.map_span, Set.image_image, hid, Set.image_id, hS]
    unfold cartierRestrictedSubspaceDim cartierRestrictedDim
    rw [hmap, finrank_top]
  · refine ⟨⊥, inferInstance, ?_⟩
    unfold cartierRestrictedDim
    rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

end Subspace

/-- S-NF for ample sums: as `StrongNumericalFreeness`, with A an ample sum (a positive multiple is
linearly equivalent to a positive combination of hyperplane divisors) instead of ample, and the
numerical hypothesis for finite-dimensional subspaces of sections: for every positive-dimensional
W and ε > 0, for large j some finite-dimensional subspace of sections of j A restricts to W with
dimension at least ((n + 1)^d - ε) j^d/d!. -/
def StrongNumericalFreenessSum : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A N : CartierDivisor X), CartierIsAmpleSum K A → CartierIsNef K N →
      (∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
          FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • A) η V) →
      CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + A + N)

/-- S-NF for ample sums implies S-NF. -/
theorem strongNumericalFreeness_of_sum (h : StrongNumericalFreenessSum.{u}) :
    StrongNumericalFreeness.{u} := by
  intro K _ _ _ _ X _ _ n hn hn1 _ c₀ A N hA hN hnum
  refine h K X n hn hn1 c₀ A N (cartierIsAmpleProj_isAmpleSum hA) hN ?_
  intro η d hd hd1 ε hε
  filter_upwards [hnum η d hd hd1 ε hε] with j hj
  obtain ⟨V, hV, hle⟩ := exists_finiteDimensional_le_cartierRestrictedSubspaceDim (K := K) (j • A) η
  exact ⟨V, hV, hj.trans (by exact_mod_cast hle)⟩

/-- The numerical input for F1 (step 4): for ample L_1, …, L_s with s ≥ n + 1, the sum
A = Σ L_i has A^d · W ≥ (n + 1)^d for every positive-dimensional W, in the form of the dimension
of the restriction to W of finite-dimensional spaces of sections of j A. -/
def MixedAmpleNumericalBound : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
      (s : ℕ), n + 1 ≤ s → ∀ (L : Fin s → CartierDivisor X), (∀ i, CartierIsAmpleProj K (L i)) →
      ∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • ∑ i, L i).sheaf, ⊤),
          FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • ∑ i, L i) η V

/-- F1 from S-NF for ample sums and the numerical bound: the sum of the L_i is an ample sum, so
no Segre embedding is needed. -/
theorem mixedFujitaFreeness_of_strongNumericalFreenessSum (h : StrongNumericalFreenessSum.{u})
    (hnum : MixedAmpleNumericalBound.{u}) : MixedFujitaFreeness.{u} := by
  intro K _ _ _ _ X _ _ n hn hn1 _ c₀ s hs L hL N hN
  exact h K X n hn hn1 c₀ (∑ i, L i) N (cartierIsAmpleSum_sum (by omega) L hL) hN
    (hnum K X n hn hn1 s hs L hL)

end Statements

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearEffectiveFreenessStatement
public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.AmpleCoprimeBridgeProof
public import MixedFujita.ProjectiveAmpleMinimizerData
public import MixedFujita.AmpleSumEqualityCase

/-!
F2 from K-NF on the base of the contraction (§9.2–9.5; steps 16 and 17).

Let (X, Δ) be a projective klt pair, D a nef Cartier divisor and a ≥ 1 with a D − (K_X + Δ) nef
and big, and κ = κ(D). The manuscript proceeds in three steps.

* §9.2 (base point free theorem, Stein factorization, Cartier descent): if κ = 0 then D is
  principal; if κ ≥ 1 there are a normal projective variety Y of dimension κ, a contraction
  f : X → Y and an ample Cartier divisor H on Y with D ∼ f*H.
* §9.3–9.4 (Kodaira's lemma, perturbation of the boundary, Ambro's canonical bundle formula for
  the contraction f): there is a klt pair (Y, B_Y) with K_Y + B_Y ∼_ℚ (a − ε) H for a rational
  ε > 0. In the language of pairs: r_Y (K_Y + B_Y) = u H + div φ with u < r_Y a.
These two steps are stated together as `KltContractionBaseStatement` (stated together because
Ambro's formula needs f to be the contraction produced by the first step; D ∼ f*H only up to
linear equivalence, since a Cartier divisor in the class need not be a pullback).
* §9.5 (proved here): for m ≥ a + κ + 1, put P = m H. Then r_Y P − r_Y (K_Y + B_Y) =
  c H − div φ with c = r_Y m − u > r_Y (κ + 1), which is ample, and every positive-dimensional
  closure of a point of Y satisfies the numerical hypothesis of K-NF with constant c^d: c H is the
  sum of c copies of an ample divisor, and an ample divisor has two coprime very ample multiples
  (`coprimeAmpleSum_restrictedSubspaceDim_eventually`), which gives H^d · W ≥ 1. The volume
  inequality is strict because c > r_Y (κ + 1). So K-NF on Y makes m H globally generated, and
  m D, its pullback up to a principal divisor, is globally generated on X.

Hence F2 (`LinearEffectiveFreeness`) follows from K-NF and this statement
(`linearEffectiveFreeness_of_kawamataNumericalFreeness`), and so from the Kawamata–Viehweg
statement, the existence of the data of the minimizer for klt pairs and this statement.
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

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Ample

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- Ampleness in the projective sense is invariant under principal shifts. -/
theorem cartierIsAmpleProj_add_principal {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A)
    (g : Y.functionFieldˣ) : CartierIsAmpleProj K (A + principalCartierDivisor Y g) := by
  obtain ⟨m, hm, n, e, he, hbase, g', hg', hggen, f, hmA⟩ := hA
  exact ⟨m, hm, n, e, he, hbase, g', hg', hggen, f * g ^ m, by
    rw [smul_add, hmA, principalCartierDivisor_mul, principalCartierDivisor_power, add_assoc]⟩

/-- A positive multiple of an ample divisor is ample. -/
theorem cartierIsAmpleProj_nsmul {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) {c : ℕ}
    (hc : 1 ≤ c) : CartierIsAmpleProj K (c • A) := by
  have h := cartierIsAmpleProj_of_isAmpleSum (cartierIsAmpleSum_sum hc (fun _ : Fin c => A)
    (fun _ => hA))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

end Ample

section Base

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The numerical hypothesis of K-NF for c H − div φ with H ample: on every closure of a point
of dimension d ≥ 1 the restricted dimensions of its multiples grow at least like c^d j^d / d!. -/
theorem ample_nsmul_restrictedDim_eventually {k : ℕ} (hdim : topologicalKrullDim Y = k)
    (hk : 1 ≤ k) {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) {c : ℕ} (hc : 1 ≤ c)
    (G : CartierDivisor Y) (φ : Y.functionFieldˣ)
    (hG : G + principalCartierDivisor Y φ = c • H) (η : Y) {d : ℕ}
    (hd : topologicalKrullDim (closure ({η} : Set Y)) = d) (hd1 : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, ((c : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
      cartierRestrictedDim K (j • G) η := by
  have hcop := cartierIsAmpleCoprime_of_ampleProj hH
  have hsum : 1 • ∑ _i : Fin c, H = G + principalCartierDivisor Y φ := by
    rw [one_smul, hG, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hgrow := restrictedGrowth_of_nsmul_eq_add_principal (∑ _i : Fin c, H) G le_rfl φ hsum η
    (d := d) (c := (c : ℝ) ^ d) (fun ε hε =>
      coprimeAmpleSum_restrictedSubspaceDim_eventually hc (fun _ : Fin c => H) (fun _ => hcop) η
        hd hd1 hε) ε hε
  filter_upwards [hgrow] with j ⟨V, _, hle⟩
  have : FiniteDimensional K Γ((j • G).sheaf, ⊤) :=
    cartier_finiteDimensional_sections_of_ample hdim hk hH (j • G)
  refine le_trans ?_ (hle.trans (Nat.cast_le.mpr (cartierRestrictedSubspaceDim_le K (j • G) η V)))
  simp only [Nat.cast_one, one_pow, one_mul, le_refl]

end Base

/-- §9.2–9.4 of the manuscript: under the hypotheses of F2, if κ(D) = 0 then D is principal, and
if κ(D) = k ≥ 1 there are a normal projective variety Y of dimension k (with the codimension-one
points in étale charts), a surjective morphism f : X → Y, an ample Cartier divisor H on Y with
D ∼ f*H, and a klt pair (Y, B_Y) with effective boundary and r_Y (K_Y + B_Y) = u H + div φ for
natural numbers u < r_Y a, that is K_Y + B_Y ∼_ℚ (a − ε) H with ε > 0. In the manuscript: the
base point free theorem for klt pairs, the Stein factorization f of the morphism of a free
multiple of D and the descent of D itself (§9.2); Kodaira's lemma and a small perturbation of the
boundary keeping the pair klt, giving K_X + Δ' ∼_ℚ (a − ε) D (§9.3); Ambro's canonical bundle
formula for the contraction f (§9.4). Only linear equivalence D ∼ f*H is asserted: a Cartier
divisor in the class need not be a pullback. -/
def KltContractionBaseStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, CartierIsNef K D → ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∀ k : ℕ, CartierIitakaDimension K D k →
        (k = 0 → ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ) ∧
        (1 ≤ k → ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
          (_ : Y.Over (Spec (CommRingCat.of K)))
          (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))) (f : X ⟶ Y) (_ : IsDominant f)
          (_ : f.IsOver (Spec (CommRingCat.of K))) (H : CartierDivisor Y) (ψ : X.functionFieldˣ)
          (cY : EtaleChart K Y k) (fY : Y.functionFieldˣ) (rY : ℕ) (_ : 1 ≤ rY)
          (DY : CartierDivisor Y) (u : ℕ) (φ : Y.functionFieldˣ),
          topologicalKrullDim Y = k ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
          CodimOneChartCovered k K Y ∧ CartierIsAmpleProj K H ∧
          D = cartierPullback f H + principalCartierDivisor X ψ ∧
          LogPairBoundaryEffective cY fY rY DY ∧ LogPairIsKlt cY fY rY DY ∧
          DY = u • H + principalCartierDivisor Y φ ∧ u < rY * a)

/-- F2 from K-NF on the base of the contraction (§9.5), given §9.2–9.4. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness
    (hKNF : KawamataNumericalFreeness.{u}) (hcontr : KltContractionBaseStatement.{u}) :
    LinearEffectiveFreeness.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig k
    hk m hm
  obtain ⟨h0, hpos⟩ := hcontr K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef
    hbig k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- κ(D) = 0: D is principal
    obtain ⟨φ, hφ⟩ := h0 rfl
    obtain ⟨H₀, hH₀'⟩ := hH₀
    obtain ⟨p, -, hgg⟩ := cartierIsAmpleProj_exists_globallyGenerated_divisible_sequence H₀ hH₀'
    have hzero : CartierIsGloballyGenerated (0 : CartierDivisor X) := by
      simpa only [zero_mul, zero_smul] using hgg 0
    have h := cartierIsGloballyGenerated_add_principal (φ ^ m) hzero
    rwa [zero_add, principalCartierDivisor_power, ← hφ] at h
  · -- κ(D) ≥ 1: descend to the base and apply K-NF there
    obtain ⟨Y, _, _, _, _, f, _, _, H, ψ, cY, fY, rY, hrY, DY, u, φ, hdimY, hnormY, hcovY, hH,
      hDf, heffY, hkltY, hDY, hu⟩ := hpos hkpos
    -- the arithmetic of c = r_Y m − u
    have h1 : rY * (a + k + 1) ≤ rY * m := Nat.mul_le_mul_left rY hm
    have h2 : rY * (a + k + 1) = rY * a + rY * (k + 1) := by ring
    have hgt : rY * (k + 1) < rY * m - u := by omega
    set c := rY * m - u with hcdef
    have hcu : rY * m = c + u := by omega
    have hc1 : 1 ≤ c := by omega
    have hG : rY • (m • H) - DY + principalCartierDivisor Y φ = c • H := by
      rw [hDY, smul_smul, hcu, add_smul]
      abel
    have hGeq : rY • (m • H) - DY = c • H + principalCartierDivisor Y φ⁻¹ := by
      rw [principalCartierDivisor_inv, ← hG]
      abel
    have hample : CartierIsAmpleProj K (rY • (m • H) - DY) := by
      rw [hGeq]
      exact cartierIsAmpleProj_add_principal (cartierIsAmpleProj_nsmul hH hc1) _
    have hcR : ((rY * (k + 1) : ℕ) : ℝ) < (c : ℝ) := by exact_mod_cast hgt
    have hcR0 : (0 : ℝ) ≤ ((rY * (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    -- the volume (the generic point)
    have hvol : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
        ((((rY * (k + 1) : ℕ) : ℝ) ^ k + δ) * (j : ℝ) ^ k / k.factorial ≤
          cartierRestrictedDim K (j • (rY • (m • H) - DY)) (genericPoint Y)) := by
      have hpow : ((rY * (k + 1) : ℕ) : ℝ) ^ k < (c : ℝ) ^ k := pow_lt_pow_left₀ hcR hcR0 (by omega)
      set δ := ((c : ℝ) ^ k - ((rY * (k + 1) : ℕ) : ℝ) ^ k) / 2 with hδ
      have hδ0 : 0 < δ := by rw [hδ]; linarith
      refine ⟨δ, hδ0, ?_⟩
      filter_upwards [ample_nsmul_restrictedDim_eventually hdimY hkpos hH hc1 _ φ hG
        (genericPoint Y) (topologicalKrullDim_closure_genericPoint hdimY) hkpos hδ0] with j hj
      refine le_trans (le_of_eq ?_) hj
      congr 2
      rw [hδ]
      ring
    -- the proper closures of points
    have hsub : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
        d < k → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
          ((((rY * (k + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedDim K (j • (rY • (m • H) - DY)) η) := by
      intro η d hd hd1 _ ε hε
      have hpow : ((rY * (k + 1) : ℕ) : ℝ) ^ d ≤ (c : ℝ) ^ d := pow_le_pow_left₀ hcR0 hcR.le d
      filter_upwards [ample_nsmul_restrictedDim_eventually hdimY hkpos hH hc1 _ φ hG η hd hd1 hε]
        with j hj
      refine le_trans ?_ hj
      have hj0 : (0 : ℝ) ≤ (j : ℝ) ^ d / d.factorial := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hj0
    have hgen : CartierIsGloballyGenerated (m • H) :=
      hKNF K Y k hdimY hkpos hnormY hcovY cY fY rY hrY DY heffY hkltY (m • H) hample hvol hsub
    rw [hDf, smul_add, ← cartierPullback_nsmul, ← principalCartierDivisor_power]
    exact cartierIsGloballyGenerated_add_principal _
      (cartierIsGloballyGenerated_cartierPullback f _ hgen)

/-- F2 from the Kawamata–Viehweg statement, the existence of the data of the minimizer for klt
pairs (which give K-NF) and §9.2–9.4. -/
theorem linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hmin : KltMinimizerDataStatement.{u}) (hcontr : KltContractionBaseStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness
    (kawamataNumericalFreeness_of_kawamataViehweg_of_minimizerData hKV hmin) hcontr

end MixedFujita

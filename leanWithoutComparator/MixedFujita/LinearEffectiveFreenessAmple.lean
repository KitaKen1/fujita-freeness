/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KodairaLemmaNormal

/-!
F2 for an ample divisor D, from K-NF and "nef plus ample is ample" (steps 16 and 17).

When D is ample, the contraction of §9.2 is the identity: no base point free theorem, no Stein
factorization and no canonical bundle formula are needed. The Iitaka dimension of an ample D is the
dimension n of X (`eq_of_iitakaDimension_of_isAmpleProj`: h⁰(m D) ≥ c m^n infinitely often since
D is big, and h⁰(j D) ≤ C (j + 1)^n since j D embeds into j M D for a very ample M D; growth
exponents compare by `le_of_frequently_mul_pow_le`). The perturbation of §9.3
(`kodairaPerturbation_of_kltPerturbation`, from "nef plus ample is ample") gives a klt pair
(X, Δ') with r' (K_X + Δ') = u D + div ψ, u < r' a, and K-NF applied on X itself to m D with
r' m D − r' (K_X + Δ') ∼ (r' m − u) D, as in §9.5, makes m D globally generated for every
m ≥ a + n + 1 (`linearEffectiveFreenessAmple_of_kawamataNumericalFreeness_of_nefAddAmple`).
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
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- If c j^a ≤ C (j + 1)^b for infinitely many j with c > 0, then a ≤ b. -/
theorem le_of_frequently_mul_pow_le {a b : ℕ} {c C : ℝ} (hc : 0 < c)
    (h : ∃ᶠ j : ℕ in atTop, c * (j : ℝ) ^ a ≤ C * ((j : ℝ) + 1) ^ b) : a ≤ b := by
  by_contra hab
  push Not at hab
  obtain ⟨M, hM⟩ := exists_nat_gt (|C| * 2 ^ b / c)
  obtain ⟨j, hj, hjM⟩ := (h.and_eventually (eventually_ge_atTop (M + 1))).exists
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
  have hjpos : (0 : ℝ) < j := by linarith
  have h1 : ((j : ℝ) + 1) ^ b ≤ (2 * (j : ℝ)) ^ b :=
    pow_le_pow_left₀ (by positivity) (by linarith) b
  have h2 : (j : ℝ) * (j : ℝ) ^ b ≤ (j : ℝ) ^ a := by
    calc (j : ℝ) * (j : ℝ) ^ b = (j : ℝ) ^ (b + 1) := by ring
      _ ≤ (j : ℝ) ^ a := pow_le_pow_right₀ hj1 (by omega)
  have hjb : (0 : ℝ) < (j : ℝ) ^ b := pow_pos hjpos b
  have h3 : c * j * (j : ℝ) ^ b ≤ |C| * 2 ^ b * (j : ℝ) ^ b := by
    calc c * j * (j : ℝ) ^ b = c * ((j : ℝ) * (j : ℝ) ^ b) := by ring
      _ ≤ c * (j : ℝ) ^ a := mul_le_mul_of_nonneg_left h2 hc.le
      _ ≤ C * ((j : ℝ) + 1) ^ b := hj
      _ ≤ |C| * ((j : ℝ) + 1) ^ b := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (2 * (j : ℝ)) ^ b := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ = |C| * 2 ^ b * (j : ℝ) ^ b := by rw [mul_pow]; ring
  have h4 : c * j ≤ |C| * 2 ^ b := le_of_mul_le_mul_right h3 hjb
  have h5 : |C| * 2 ^ b / c < j := lt_of_lt_of_le hM (by exact_mod_cast (show M ≤ j by omega))
  rw [div_lt_iff₀ hc] at h5
  linarith

section Iitaka

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The Iitaka dimension of an ample divisor is the dimension of the variety. -/
theorem eq_of_iitakaDimension_of_isAmpleProj {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hn : 1 ≤ n) {D : CartierDivisor X} (hD : CartierIsAmpleProj K D) {k : ℕ}
    (hk : CartierIitakaDimension K D k) : k = n := by
  obtain ⟨⟨c', hc', hfreq'⟩, C, hC⟩ := hk
  obtain ⟨d, hd, c, hc, hfreq⟩ := cartierIsAmpleProj_isBig hdim hn hD
  have hdn : d = n := by
    have h := hd.symm.trans hdim
    exact_mod_cast h
  rw [hdn] at hfreq
  -- n ≤ k: the lower bound for the ample D against the upper bound of the Iitaka dimension
  have hnk : n ≤ k := le_of_frequently_mul_pow_le hc (hfreq.mono fun m hm => hm.trans (hC m))
  -- k ≤ n: j D embeds into j M D for a very ample M D
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_veryAmple hD
  obtain ⟨j₁, hj₁⟩ := cartierIsAmpleProj_eventually_globallyGenerated hD
  set M := j₀ + j₁ + 1 with hM
  obtain ⟨Nv, e, he, hbase, g, hg, hggen, f, hMD⟩ := hj₀ M (by omega)
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hj₁ (M - 1) (by omega))
  obtain ⟨-, -, hfinJ, -⟩ :=
    projectiveHyperplane_hilbert_leading_integral e g hg hggen hbase hdim hn
  obtain ⟨C₂, hC₂⟩ := projectiveHyperplane_exists_finrank_le_mul_pow e g hg hggen hbase hdim hn
  have hupper : ∀ j : ℕ, (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      (|C₂| * (M : ℝ) ^ n) * ((j : ℝ) + 1) ^ n := by
    intro j
    have hjM : j • D + j • ((M - 1) • D) = j • (M • D) := by
      rw [← nsmul_add, ← succ_nsmul', Nat.sub_add_cancel (show 1 ≤ M by omega)]
    have hdiv : j • D + j • ((M - 1) • D) =
        j • projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor X (f ^ j) := by
      rw [hjM, hMD, nsmul_add, principalCartierDivisor_power]
    have := hfinJ j
    have hfinT : FiniteDimensional K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) := by
      rw [hdiv]
      exact Module.Finite.equiv (cartierPrincipalShiftEquiv (K := K) _ _).symm
    have hinj : Function.Injective (cartierSectionProductLinear (K := K) (j • D)
        (j • ((M - 1) • D)) (cartierSectionPower _ t j)) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro s hs
      rw [LinearMap.mem_ker] at hs
      by_contra hs0
      exact cartierSectionProduct_ne_zero _ _ s _ hs0 (cartierSectionPower_ne_zero _ t ht j) hs
    have hle : Module.finrank K Γ((j • D).sheaf, ⊤) ≤
        Module.finrank K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    have heq : Module.finrank K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) =
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
      rw [hdiv, finrank_add_principal]
    have hbound := hC₂ j
    have hle' : (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
      exact_mod_cast hle.trans heq.le
    have hM1 : (1 : ℝ) ≤ (M : ℝ) ^ n := one_le_pow₀ (by exact_mod_cast (show 1 ≤ M by omega))
    have hj0 : (0 : ℝ) ≤ ((j : ℝ) + 1) ^ n := by positivity
    calc (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ)
        ≤ C₂ * ((j : ℝ) + 1) ^ n := hle'.trans hbound
      _ ≤ |C₂| * ((j : ℝ) + 1) ^ n := mul_le_mul_of_nonneg_right (le_abs_self C₂) hj0
      _ ≤ |C₂| * (M : ℝ) ^ n * ((j : ℝ) + 1) ^ n := by
        have h0 : 0 ≤ |C₂| * ((j : ℝ) + 1) ^ n := by positivity
        nlinarith [h0, hM1]
  have hkn : k ≤ n := le_of_frequently_mul_pow_le hc' (hfreq'.mono fun j hj => hj.trans (hupper j))
  omega

end Iitaka

/-- F2 for an ample divisor D: under the hypotheses of F2 with D ample, m D is globally generated
for every m ≥ a + κ(D) + 1. -/
def LinearEffectiveFreenessAmple : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, CartierIsAmpleProj K D → ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∀ k : ℕ, CartierIitakaDimension K D k →
        ∀ m : ℕ, a + k + 1 ≤ m → CartierIsGloballyGenerated (m • D)

/-- F2 for an ample divisor from K-NF and "nef plus ample is ample". -/
theorem linearEffectiveFreenessAmple_of_kawamataNumericalFreeness_of_nefAddAmple
    (hKNF : KawamataNumericalFreeness.{u}) (hna : NefAddAmpleStatement.{u}) :
    LinearEffectiveFreenessAmple.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
    k hk m hm
  have hkn : k = n := eq_of_iitakaDimension_of_isAmpleProj hdim hn hD hk
  rw [hkn] at hm
  obtain ⟨f₁, rY, hrY, DY, u, φ, heffY, hkltY, hDY, hu⟩ :=
    kodairaPerturbation_of_kltPerturbation (kltPerturbation_of_nefAddAmple hna) K X n hdim hn
      hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig
  have h1 : rY * (a + n + 1) ≤ rY * m := Nat.mul_le_mul_left rY hm
  have h2 : rY * (a + n + 1) = rY * a + rY * (n + 1) := by ring
  have hgt : rY * (n + 1) < rY * m - u := by omega
  set c := rY * m - u with hcdef
  have hcu : rY * m = c + u := by omega
  have hc1 : 1 ≤ c := by omega
  have hG : rY • (m • D) - DY + principalCartierDivisor X φ = c • D := by
    rw [hDY, smul_smul, hcu, add_smul]
    abel
  have hGeq : rY • (m • D) - DY = c • D + principalCartierDivisor X φ⁻¹ := by
    rw [principalCartierDivisor_inv, ← hG]
    abel
  have hample : CartierIsAmpleProj K (rY • (m • D) - DY) := by
    rw [hGeq]
    exact cartierIsAmpleProj_add_principal (cartierIsAmpleProj_nsmul hD hc1) _
  have hcR : ((rY * (n + 1) : ℕ) : ℝ) < (c : ℝ) := by exact_mod_cast hgt
  have hcR0 : (0 : ℝ) ≤ ((rY * (n + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hvol : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
      ((((rY * (n + 1) : ℕ) : ℝ) ^ n + δ) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • (rY • (m • D) - DY)) (genericPoint X)) := by
    have hpow : ((rY * (n + 1) : ℕ) : ℝ) ^ n < (c : ℝ) ^ n := pow_lt_pow_left₀ hcR hcR0 (by omega)
    set δ := ((c : ℝ) ^ n - ((rY * (n + 1) : ℕ) : ℝ) ^ n) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    refine ⟨δ, hδ0, ?_⟩
    filter_upwards [ample_nsmul_restrictedDim_eventually hdim hn hD hc1 _ φ hG
      (genericPoint X) (topologicalKrullDim_closure_genericPoint hdim) hn hδ0] with j hj
    refine le_trans (le_of_eq ?_) hj
    congr 2
    rw [hδ]
    ring
  have hsub : ∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
      d < n → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((rY * (n + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedDim K (j • (rY • (m • D) - DY)) η) := by
    intro η d hd hd1 _ ε hε
    have hpow : ((rY * (n + 1) : ℕ) : ℝ) ^ d ≤ (c : ℝ) ^ d := pow_le_pow_left₀ hcR0 hcR.le d
    filter_upwards [ample_nsmul_restrictedDim_eventually hdim hn hD hc1 _ φ hG η hd hd1 hε]
      with j hj
    refine le_trans ?_ hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) ^ d / d.factorial := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hj0
  exact hKNF K X n hdim hn hnorm hcov c₀ f₁ rY hrY DY heffY hkltY (m • D) hample hvol hsub

end MixedFujita

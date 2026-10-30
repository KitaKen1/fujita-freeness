/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SemiampleIitakaZero
public import MixedFujita.SNCModelFreeKltPerturbations
public import MixedFujita.AmpleEffectiveComparison
public import MixedFujita.ProjectiveCurveCohomology

/-!
The perturbation of §9.3 from "nef plus ample is ample" (step 17).

`KltPerturbationStatement` asks, for a klt pair (X, Δ) with effective boundary, r (K_X + Δ) = D',
T₀ = a D − (K_X + Δ) nef and big, an ample H and a nonzero section s of m r T₀ − H, for a klt pair
(X, Δ') with effective boundary and r' (K_X + Δ') = u D + div ψ, u < r' a. As in the manuscript:

* the zero divisor G of s, with a small coefficient 1/(m₁ r), keeps the pair klt
  (`logPairIsKlt_exists_small_fixed_effective_divisor_perturbation`, which takes the simple normal
  crossing model from the vendored resolution); the coefficient is chosen with m₁ > m;
* B = (m₁ − m) r T₀ + H is ample by `NefAddAmpleStatement` (Kleiman's criterion: nef plus ample
  is ample), and A' = k B − D is very ample for large k
  (`cartierIsAmpleProj_eventually_twist_veryAmple`);
* an effective representative of A'/q, q = k m₁ r, from a section of a multiple of A' keeps the
  pair klt (`logPairIsKlt_exists_effective_rational_ample_perturbation`).

Then K_X + Δ' ∼_ℚ (a − 1/(k m₁ r)) D: with D₁ = m₁ D' + G and d₁ = m₁ r,
q D₁ + d₁ A' + d₁ D = d₁ (k m₁ r a) D + q div σ (`perturbation_divisor_identity`). Hence
`KltPerturbationStatement` follows from `NefAddAmpleStatement` (`kltPerturbation_of_nefAddAmple`),
and F2 follows from K-NF, the base point free theorem, the contraction of a semiample divisor of
positive Iitaka dimension, Kodaira's lemma, `NefAddAmpleStatement` and Ambro's canonical bundle
formula (`linearEffectiveFreeness_of_kawamataNumericalFreeness_of_nefAddAmple`).
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

/-- Nef plus ample is ample (a consequence of Kleiman's criterion): on a variety over an
algebraically closed field of characteristic zero, the sum of a nef Cartier divisor and an ample
Cartier divisor is ample. (An ample divisor makes the variety projective.) -/
def NefAddAmpleStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (N A : CartierDivisor X), CartierIsNef K N → CartierIsAmpleProj K A →
      CartierIsAmpleProj K (N + A)

/-- The divisor identity behind §9.3: with D₁ = m₁ D' + G, G = m (r a D − D') − H + P,
A' = −D + k ((e + 1)(r a D − D') + H), m₁ = m + e + 1, q = k m₁ r and d₁ = m₁ r,
q D₁ + d₁ A' + d₁ D = d₁ (k m₁ r a) D + q P. -/
theorem perturbation_divisor_identity {X : Scheme.{u}} [IsIntegral X]
    (D D' H P : CartierDivisor X) (m e r a k : ℕ) :
    (k * (m + e + 1) * r) • ((m + e + 1) • D' + (m • ((r * a) • D - D') - H + P)) +
        ((m + e + 1) * r) • (-D + k • ((e + 1) • ((r * a) • D - D') + H)) +
        ((m + e + 1) * r) • D =
      ((m + e + 1) * r * (k * (m + e + 1) * r * a)) • D + (k * (m + e + 1) * r) • P := by
  module

/-- The perturbation of §9.3 follows from "nef plus ample is ample". -/
theorem kltPerturbation_of_nefAddAmple (hna : NefAddAmpleStatement.{u}) :
    KltPerturbationStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig m
    hm H hH s hs
  obtain ⟨-, -, N₀, e₀, he₀, hbase₀, -⟩ := id hH
  have : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e₀ hbase₀
  have hGeff := cartierSectionZeroDivisor_isEffective _ s hs
  have hmr : (0 : ℚ) < ((m * r : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  obtain ⟨m₁, hm₁, -, hsmall, heff₁, hklt₁⟩ :=
    logPairIsKlt_exists_small_fixed_effective_divisor_perturbation c₀ f₀ r hr D'
      (cartierSectionZeroDivisor _ s hs) hklt heff hGeff (1 / ((m * r : ℕ) : ℚ))
      (one_div_pos.mpr hmr)
  have hm₁r : (0 : ℚ) < ((m₁ * r : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hlt : m * r < m₁ * r := by
    have := (one_div_lt_one_div hm₁r hmr).mp hsmall
    exact_mod_cast this
  have hmm₁ : m < m₁ := Nat.lt_of_mul_lt_mul_right hlt
  obtain ⟨e, rfl⟩ : ∃ e, m₁ = m + e + 1 := ⟨m₁ - m - 1, by omega⟩
  have hB : CartierIsAmpleProj K ((e + 1) • ((r * a) • D - D') + H) :=
    hna K X _ H (cartierIsNef_nsmul hnef (e + 1)) hH
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hB (-D)
  have hA' : CartierIsAmpleProj K (-D + (j₀ + 1) • ((e + 1) • ((r * a) • D - D') + H)) :=
    cartierIsAmpleProj_of_veryAmple (hj₀ (j₀ + 1) (by omega))
  have hd₁ : 1 ≤ (m + e + 1) * r := Nat.mul_pos (by omega) (by omega)
  have hq : 1 ≤ (j₀ + 1) * (m + e + 1) * r := Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
    (by omega)
  obtain ⟨m₂, r₂, s₂, hs₂, hm₂, -, -, -, -, -, -, heff₂, hklt₂, hclass, -⟩ :=
    logPairIsKlt_exists_effective_rational_ample_perturbation hnorm c₀ f₀ ((m + e + 1) * r) hd₁
      ((m + e + 1) • D' + cartierSectionZeroDivisor _ s hs) hklt₁ heff₁ _ hA'
      ((j₀ + 1) * (m + e + 1) * r) hq 0 1 one_pos ∅ Set.finite_empty
  have hpos : 1 ≤ (j₀ + 1) * (m + e + 1) * r * a := Nat.mul_pos hq (by omega)
  obtain ⟨t, ht⟩ : ∃ t, (j₀ + 1) * (m + e + 1) * r * a = t + 1 :=
    ⟨_, (Nat.sub_add_cancel hpos).symm⟩
  set q := (j₀ + 1) * (m + e + 1) * r with hqdef
  set d₁ := (m + e + 1) * r with hd₁def
  set σ := cartierSectionUnit (m • ((r * a) • D - D') - H) s hs with hσ
  set τ := cartierSectionUnit (r₂ • (-D + (j₀ + 1) • ((e + 1) • ((r * a) • D - D') + H))) s₂ hs₂
    with hτ
  have hkey : q • ((m + e + 1) • D' + cartierSectionZeroDivisor _ s hs) +
      d₁ • (-D + (j₀ + 1) • ((e + 1) • ((r * a) • D - D') + H)) =
        (d₁ * t) • D + q • principalCartierDivisor X σ := by
    have h := perturbation_divisor_identity D D' H (principalCartierDivisor X σ) m e r a (j₀ + 1)
    rw [← hqdef, ← hd₁def, ht, show (d₁ * (t + 1)) • D = (d₁ * t) • D + d₁ • D by
      rw [mul_add_one, add_nsmul]] at h
    rw [cartierSectionZeroDivisor]
    exact add_right_cancel (h.trans (by abel))
  have hqa : t < q * a := by rw [ht]; exact Nat.lt_add_one t
  refine ⟨f₀, q * (m₂ * d₁), Nat.mul_pos hq (Nat.mul_pos (by omega) hd₁),
    q • (m₂ • ((m + e + 1) • D' + cartierSectionZeroDivisor _ s hs) +
      cartierSectionZeroDivisor _ s₂ hs₂), m₂ * (d₁ * t), σ ^ (m₂ * q) * τ ^ q,
    (logPairBoundaryEffective_scale_denominator_iff c₀ f₀ (m₂ * d₁) q hq _).mpr heff₂,
    (logPairIsKlt_scale_denominator_iff c₀ f₀ (m₂ * d₁) q hq _).mpr hklt₂, ?_, ?_⟩
  · rw [hclass, hkey]
    simp only [principalCartierDivisor_mul, principalCartierDivisor_power, nsmul_add, smul_smul]
    abel
  · calc m₂ * (d₁ * t) = (m₂ * d₁) * t := by ring
      _ < (m₂ * d₁) * (q * a) := Nat.mul_lt_mul_of_pos_left hqa (Nat.mul_pos (by omega) hd₁)
      _ = q * (m₂ * d₁) * a := by ring

/-- F2 from K-NF, the base point free theorem, the contraction of a semiample divisor of positive
Iitaka dimension, Kodaira's lemma, "nef plus ample is ample" and Ambro's canonical bundle
formula. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_nefAddAmple
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionPositiveStatement.{u}) (hkl : KodairaLemmaStatement.{u})
    (hna : NefAddAmpleStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_positiveInputs hKNF hbpf hsa hkl
    (kltPerturbation_of_nefAddAmple hna) hamb

/-- F2 from the Kawamata–Viehweg statement, the existence of the data of the minimizer for klt
pairs, the base point free theorem, the contraction of a semiample divisor of positive Iitaka
dimension, Kodaira's lemma, "nef plus ample is ample" and Ambro's canonical bundle formula. -/
theorem linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData_of_nefAddAmple
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hmin : KltMinimizerDataStatement.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionPositiveStatement.{u}) (hkl : KodairaLemmaStatement.{u})
    (hna : NefAddAmpleStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_nefAddAmple
    (kawamataNumericalFreeness_of_kawamataViehweg_of_minimizerData hKV hmin) hbpf hsa hkl hna hamb

end MixedFujita

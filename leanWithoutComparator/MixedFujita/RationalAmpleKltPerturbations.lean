/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleDivisibleGlobalGeneration

/-!
Given the original proper SNC model of a normal klt source, a rational ample
class A/q has an actual effective klt representative from a Bertini section.
The denominator l = m*d = r*q is arbitrarily large and its reciprocal is
arbitrarily small. Global generation of r*A is constructed from projective
ampleness. The actual principal-divisor identity certifies that J/l has the
specified rational class A/q. Original SNC model existence, Kodaira
decomposition, ampleness of the class arising in F2, and Ambro descent remain
separate geometric obligations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The common denominator gives precisely the requested rational ample weight. -/
theorem common_denominator_rational_weight (d q m r : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (h : m * d = r * q) : (r : ℚ) / ((m * d : ℕ) : ℚ) = 1 / (q : ℚ) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [h, Nat.cast_mul]
  field_simp

variable {X : Scheme.{u}} [IsIntegral X]

/-- The actual section zero divisor realizes the specified rational Cartier class
after clearing the two denominators; the rational unit is explicit. -/
theorem cartierSection_common_denominator_perturbation_identity (D A : CartierDivisor X)
    (d q m r : ℕ) (h : m * d = r * q) (s : Γ((r • A).sheaf, ⊤)) (hs : s ≠ 0) :
    q • (m • D + cartierSectionZeroDivisor (r • A) s hs) =
      m • (q • D + d • A) +
        principalCartierDivisor X (cartierSectionUnit (r • A) s hs ^ q) := by
  simp only [cartierSectionZeroDivisor, nsmul_add, principalCartierDivisor_power, smul_smul]
  rw [Nat.mul_comm q m, Nat.mul_comm q r, ← h]
  abel

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {T : Scheme.{u}}
  [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- A rational ample class supplies an actual source klt cut with arbitrarily large
compatible denominator, precise rational class and finite point avoidance. -/
theorem logPairIsKlt_exists_rational_ample_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)
    {v : ℕ} (ξ : Fin v → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (ε : ℚ) (hε : 0 < ε) (Z : Set X) (hZ : Z.Finite) :
    ∃ (m r : ℕ) (s : Γ((r • A).sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      q • (m • D + cartierSectionZeroDivisor (r • A) s hs) =
        m • (q • D + d • A) +
          principalCartierDivisor X (cartierSectionUnit (r • A) s hs ^ q) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus (r • A) s) := by
  obtain ⟨m, r, hm, hr, heq, hN, hmd, hpos, hsmall, hgen⟩ :=
    cartierIsAmpleProj_exists_common_denominator_global_generation A hA d q N hd hq ε hε
  have hscaled := (logPairIsKlt_scale_denominator_iff c f d m (by omega) D).mpr hklt
  have hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f (m * d) (m • D)
        cT etaleCharts_cover) (t : T) = 0 := by
    intro t ht
    rw [crepantBoundaryCartier_scale_denominator, cartierCoefficient_nsmul,
      hsupport t ht, mul_zero]
  obtain ⟨s, hs, hklt', havoid⟩ :=
    logPairIsKlt_exists_source_perturbation_avoiding_of_crepant_snc_model ρ hρ
      hnorm c f (m * d) (m • D) hscaled cT (r • A) hgen ξ hinj hξ hsnc hsupp 1 hmd Z hZ
  exact ⟨m, r, s, hs, hm, hr, heq, hN, hmd, hpos, hsmall,
    by simpa only [one_nsmul] using hklt',
    cartierSection_common_denominator_perturbation_identity D A d q m r heq s hs, havoid⟩

/-- An effective original boundary gives an actual effective klt representative
after adding the prescribed rational ample class. -/
theorem logPairIsKlt_exists_effective_rational_ample_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (heff : LogPairBoundaryEffective c f d D) (cT : EtaleChart K T n)
    {v : ℕ} (ξ : Fin v → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (ε : ℚ) (hε : 0 < ε) (Z : Set X) (hZ : Z.Finite) :
    ∃ (m r : ℕ) (s : Γ((r • A).sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d) (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      q • (m • D + cartierSectionZeroDivisor (r • A) s hs) =
        m • (q • D + d • A) +
          principalCartierDivisor X (cartierSectionUnit (r • A) s hs ^ q) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus (r • A) s) := by
  obtain ⟨m, r, s, hs, hm, hr, heq, hN, hmd, hpos, hsmall, hklt', hclass, havoid⟩ :=
    logPairIsKlt_exists_rational_ample_perturbation_avoiding ρ hρ hnorm c f d hd D hklt cT
      ξ hinj hξ hsnc hsupport A hA q hq N ε hε Z hZ
  refine ⟨m, r, s, hs, hm, hr, heq, hN, hmd, hpos, hsmall, ?_, hklt', hclass, havoid⟩
  have hscaled := (logPairBoundaryEffective_scale_denominator_iff c f d m (by omega) D).mpr heff
  simpa only [one_nsmul] using logPairBoundaryEffective_section_perturbation
    c f (m * d) 1 (m • D) (r • A) s hs hscaled

end MixedFujita

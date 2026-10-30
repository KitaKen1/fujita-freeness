/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataViehwegSumReduction

/-!
Big plus nef is big on a projective variety, from "nef plus ample is ample" (step 10).

On a normal variety of dimension n ≥ 1 over an algebraically closed field of characteristic zero
with an ample Cartier divisor H, a big B and a nef N have B + N big, given
`NefAddAmpleStatement` (`cartierIsBig_add_of_isNef_of_nefAddAmple`): Kodaira's lemma (proved)
gives a nonzero section of m B − H, the divisor m N + H is ample, hence big, and multiplication by
the k-th power of the section embeds the sections of k (m N + H) into those of (k m)(B + N). On a
smooth proper variety with an ample divisor this is the content of `BigAddNefStatement`
(`cartierIsBig_add_of_smooth_of_nefAddAmple`), so on projective varieties the hypothesis
`BigAddNefStatement` used for F1 follows from the hypothesis `NefAddAmpleStatement` used for F2.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Big plus nef is big on a normal variety with an ample divisor, given "nef plus ample is
ample". -/
theorem cartierIsBig_add_of_isNef_of_nefAddAmple (hna : NefAddAmpleStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    {B N : CartierDivisor X} (hB : CartierIsBig K B) (hN : CartierIsNef K N) :
    CartierIsBig K (B + N) := by
  classical
  obtain ⟨c₀⟩ := nonempty_etaleChart_of_charZero (K := K) hdim
  obtain ⟨m, hm, s, hs⟩ :=
    exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdim hn hnorm c₀ B H hB hH
  have hA : CartierIsAmpleProj K (m • N + H) := hna K X (m • N) H (cartierIsNef_nsmul hN m) hH
  obtain ⟨d, hd, c, hc, hfreq⟩ := cartierIsAmpleProj_isBig hdim hn hA
  have hdn : d = n := by
    have h := hd.symm.trans hdim
    exact_mod_cast h
  rw [hdn] at hfreq
  have hstep : ∀ k : ℕ, (Module.finrank K Γ((k • (m • N + H)).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ(((k * m) • (B + N)).sheaf, ⊤) := by
    intro k
    have hdivk : k • (m • N + H) + k • (m • B - H) = (k * m) • (B + N) := by module
    have hfin : FiniteDimensional K Γ((k • (m • N + H) + k • (m • B - H)).sheaf, ⊤) :=
      cartier_finiteDimensional_sections_of_ample hdim hn hH _
    have hinj : Function.Injective (cartierSectionProductLinear (K := K) (k • (m • N + H))
        (k • (m • B - H)) (cartierSectionPower _ s k)) := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro t ht
      rw [LinearMap.mem_ker] at ht
      by_contra ht0
      exact cartierSectionProduct_ne_zero _ _ t _ ht0 (cartierSectionPower_ne_zero _ s hs k) ht
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hdivk] at hle
    exact_mod_cast hle
  have hmR : (0 : ℝ) < (m : ℝ) ^ n := pow_pos (by exact_mod_cast hm) n
  refine ⟨n, hdim, c / (m : ℝ) ^ n, div_pos hc hmR, ?_⟩
  have hfreq' : ∃ᶠ k : ℕ in atTop, c / (m : ℝ) ^ n * ((k * m : ℕ) : ℝ) ^ n ≤
      Module.finrank K Γ(((k * m) • (B + N)).sheaf, ⊤) := by
    refine hfreq.mono fun k hk => ?_
    have heq : c / (m : ℝ) ^ n * ((k * m : ℕ) : ℝ) ^ n = c * (k : ℝ) ^ n := by
      push_cast
      rw [mul_pow]
      field_simp
    rw [heq]
    exact hk.trans (hstep k)
  have htend : Tendsto (fun k : ℕ => k * m) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun k hk => le_trans hk (Nat.le_mul_of_pos_right k hm)⟩
  exact htend.frequently hfreq'

/-- On a smooth proper variety with an ample divisor, big plus nef is big, given "nef plus ample is
ample". -/
theorem cartierIsBig_add_of_smooth_of_nefAddAmple (hna : NefAddAmpleStatement.{u})
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (T : Scheme.{u})
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim T = n) (hn : 1 ≤ n)
    (hH : ∃ H : CartierDivisor T, CartierIsAmpleProj K H) (D₁ D₂ : CartierDivisor T)
    (hbig₁ : CartierIsBig K D₁) (hnef₂ : CartierIsNef K D₂) : CartierIsBig K (D₁ + D₂) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨H, hH⟩ := hH
  exact cartierIsBig_add_of_isNef_of_nefAddAmple hna hdim hn
    (fun t => smooth_stalk_isIntegrallyClosed (K := K) t) hH hbig₁ hnef₂

end MixedFujita

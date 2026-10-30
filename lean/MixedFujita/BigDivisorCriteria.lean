/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BigAddNefProjective

/-!
Criteria for big divisors on a normal projective variety (step 17).

On a normal variety of dimension n ≥ 1 over an algebraically closed field of characteristic zero
with an ample Cartier divisor H:

* Kodaira's lemma holds for every Cartier divisor F in place of H: for a big B some m B − F with
  m ≥ 1 has a nonzero section (`exists_section_nsmul_sub_of_isBig`): c H − F has a nonzero section
  for large c, and Kodaira's lemma for the ample c H gives one of m B − c H;
* conversely, if some m B − H with m ≥ 1 has a nonzero section, B is big
  (`cartierIsBig_of_section_nsmul_sub`): multiplication by its powers embeds the sections of k H
  into those of (k m) B, and H is big.

So B is big exactly when some m B − H has a nonzero section.
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- Kodaira's lemma for an arbitrary Cartier divisor F: for a big B on a normal projective variety
some m B − F with m ≥ 1 has a nonzero section. -/
theorem exists_section_nsmul_sub_of_isBig {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hn : 1 ≤ n) (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) {B : CartierDivisor X}
    (hB : CartierIsBig K B) (F : CartierDivisor X) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (s : Γ((m • B - F).sheaf, ⊤)), s ≠ 0 := by
  obtain ⟨c₀⟩ := nonempty_etaleChart_of_charZero (K := K) hdim
  obtain ⟨c, hc⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (-F)
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hc (c + 1) (by omega))
  obtain ⟨m, hm, s, hs⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdim hn hnorm c₀ B
    ((c + 1) • H) hB (cartierIsAmpleProj_nsmul hH (by omega))
  have hdiv : m • B - (c + 1) • H + (-F + (c + 1) • H) = m • B - F := by abel
  refine ⟨m, hm, ?_⟩
  rw [← hdiv]
  exact ⟨cartierSectionProduct _ _ s t, cartierSectionProduct_ne_zero _ _ _ _ hs ht⟩

omit [CharZero K] [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- If some m B − H with m ≥ 1 has a nonzero section, B is big. -/
theorem cartierIsBig_of_section_nsmul_sub {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hn : 1 ≤ n) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) {B : CartierDivisor X}
    {m : ℕ} (hm : 1 ≤ m) (s : Γ((m • B - H).sheaf, ⊤)) (hs : s ≠ 0) : CartierIsBig K B := by
  classical
  obtain ⟨d, hd, c, hc, hfreq⟩ := cartierIsAmpleProj_isBig hdim hn hH
  have hdn : d = n := by
    have h := hd.symm.trans hdim
    exact_mod_cast h
  rw [hdn] at hfreq
  have hstep : ∀ k : ℕ, (Module.finrank K Γ((k • H).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ(((k * m) • B).sheaf, ⊤) := by
    intro k
    have hdivk : k • H + k • (m • B - H) = (k * m) • B := by module
    have hfin : FiniteDimensional K Γ((k • H + k • (m • B - H)).sheaf, ⊤) :=
      cartier_finiteDimensional_sections_of_ample hdim hn hH _
    have hinj : Function.Injective (cartierSectionProductLinear (K := K) (k • H)
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
      Module.finrank K Γ(((k * m) • B).sheaf, ⊤) := by
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

end MixedFujita

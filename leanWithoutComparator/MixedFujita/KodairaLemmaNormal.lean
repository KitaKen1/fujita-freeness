/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KodairaLemmaSmooth
public import MixedFujita.KltPerturbationNefAmple
public import MixedFujita.EtaleChartDimension
public import MixedFujita.CartierPositivityPullback

/-!
Kodaira's lemma on a normal projective variety, and F2 without it as a hypothesis (step 17).

Let X be a normal integral variety of dimension n ≥ 1 over an algebraically closed field of
characteristic zero with an étale chart and an ample Cartier divisor H, and B a big Cartier
divisor. Then some m B − H with m ≥ 1 has a nonzero section
(`exists_section_nsmul_sub_of_isBig_of_isAmpleProj`): X is proper over K, the vendored resolution
gives a smooth projective model ρ : T → X with a very ample class (hyperplane class J₀), ρ*B is
big on T, Kodaira's lemma on T (`exists_section_nsmul_sub_projectiveHyperplane_of_isBig`) gives a
section of m ρ*B − J₀, a large multiple of J₀ dominates ρ*H, and h⁰(T, ρ*D) = h⁰(X, D)
(`finrank_sections_cartierPullback`) brings the section down to X.

The perturbation of §9.3 then needs only `KltPerturbationStatement`
(`kodairaPerturbation_of_kltPerturbation`), and F2 follows from K-NF, the base point free theorem,
the contraction of a semiample divisor of positive Iitaka dimension, "nef plus ample is ample" and
Ambro's canonical bundle formula, without Kodaira's lemma as a hypothesis
(`linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_nefAddAmple`).
(`KodairaLemmaStatement` itself is stated without an étale chart and is not used any more.)
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

/-- Kodaira's lemma on a normal projective variety with an étale chart: for a big B and an ample H
some m B − H with m ≥ 1 has a nonzero section. -/
theorem exists_section_nsmul_sub_of_isBig_of_isAmpleProj {K : Type u} [Field K] [IsAlgClosed K]
    [CharZero K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (c₀ : EtaleChart K X n)
    (B H : CartierDivisor X) (hB : CartierIsBig K B) (hH : CartierIsAmpleProj K H) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (s : Γ((m • B - H).sheaf, ⊤)), s ≠ 0 := by
  classical
  obtain ⟨-, -, N₀, e₀, he₀, hbase₀, -⟩ := id hH
  have : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e₀ hbase₀
  obtain ⟨T, _, _, _, _, ρ, _, _, _, hρ, cT, r, ξ, -, -, hsnc, -, -, hJ⟩ :=
    exists_projective_snc_model_with_ample c₀ (1 : X.functionFieldˣ) 1 0
      (fun i : PEmpty.{1} => i.elim) hH
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hTdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hBT : CartierIsBig K (cartierPullback ρ B) :=
    cartierIsBig_cartierPullback hnorm hnormT ρ hρ (hTdim.trans hdim.symm) hB
  obtain ⟨-, Nj, e, he, hbase, g, hg, hggen, -, -⟩ := hJ
  obtain ⟨m, hm, s, hs⟩ := exists_section_nsmul_sub_projectiveHyperplane_of_isBig e g hg hggen
    hbase hTdim hn ξ hsnc (cartierPullback ρ B) hBT
  have hJ₀amp : CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) :=
    projectiveHyperplaneCartier_isAmpleProj e g hg hggen hbase
  obtain ⟨-, -, hfinJ, -⟩ :=
    projectiveHyperplane_hilbert_leading_integral e g hg hggen hbase hTdim hn
  obtain ⟨c, hc⟩ :=
    cartierIsAmpleProj_eventually_twist_globallyGenerated hJ₀amp (-(cartierPullback ρ H))
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hc (c + 1) (by omega))
  have hidentity : (c + 1) • (m • cartierPullback ρ B - projectiveHyperplaneCartier e g hg hggen) +
      (-(cartierPullback ρ H) + (c + 1) • projectiveHyperplaneCartier e g hg hggen) =
        cartierPullback ρ (((c + 1) * m) • B - H) := by
    rw [cartierPullback_sub, cartierPullback_nsmul]
    module
  have hsecT : ∃ σ : Γ((cartierPullback ρ (((c + 1) * m) • B - H)).sheaf, ⊤), σ ≠ 0 := by
    rw [← hidentity]
    exact ⟨cartierSectionProduct _ _ (cartierSectionPower _ s (c + 1)) t,
      cartierSectionProduct_ne_zero _ _ _ _ (cartierSectionPower_ne_zero _ s hs (c + 1)) ht⟩
  obtain ⟨k, hk⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hJ₀amp
    (-(cartierPullback ρ (((c + 1) * m) • B - H)))
  obtain ⟨t₂, ht₂⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hk k le_rfl)
  have hfin2 : FiniteDimensional K Γ((cartierPullback ρ (((c + 1) * m) • B - H) +
      (-(cartierPullback ρ (((c + 1) * m) • B - H)) +
        k • projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤) := by
    rw [add_neg_cancel_left]
    exact hfinJ k
  have hfinT : FiniteDimensional K Γ((cartierPullback ρ (((c + 1) * m) • B - H)).sheaf, ⊤) :=
    finiteDimensional_of_section_mul _ _ t₂ ht₂
  obtain ⟨σ, hσ⟩ := hsecT
  have hposT : 0 < Module.finrank K Γ((cartierPullback ρ (((c + 1) * m) • B - H)).sheaf, ⊤) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ, hσ⟩
  rw [finrank_sections_cartierPullback K hnorm ρ hρ.2] at hposT
  have : FiniteDimensional K Γ((((c + 1) * m) • B - H).sheaf, ⊤) :=
    Module.finite_of_finrank_pos hposT
  obtain ⟨sX, hsX⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hposT
  exact ⟨(c + 1) * m, Nat.mul_pos (by omega) hm, sX, hsX⟩

/-- §9.3 (Kodaira's lemma and the perturbation) from the perturbation alone: Kodaira's lemma is
proved. -/
theorem kodairaPerturbation_of_kltPerturbation (hpert : KltPerturbationStatement.{u}) :
    KodairaPerturbationStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig
  obtain ⟨H, hH⟩ := hH₀
  obtain ⟨m, hm, s, hs⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj hdim hn hnorm c₀
    ((r * a) • D - D') H hbig hH
  exact hpert K X n hdim hn hnorm hcov ⟨H, hH⟩ c₀ f₀ r hr D' heff hklt D a ha hnef hbig m hm H hH
    s hs

/-- F2 from K-NF, the base point free theorem, the contraction of a semiample divisor of positive
Iitaka dimension, "nef plus ample is ample" and Ambro's canonical bundle formula. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_nefAddAmple
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionPositiveStatement.{u}) (hna : NefAddAmpleStatement.{u})
    (hamb : AmbroContractionStatement.{u}) : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_inputs hKNF
    (nefContraction_of_basePointFree_of_semiampleContraction hbpf
      (semiampleContraction_of_positive hsa))
    (kodairaPerturbation_of_kltPerturbation (kltPerturbation_of_nefAddAmple hna)) hamb

/-- F2 from the Kawamata–Viehweg statement, the existence of the data of the minimizer for klt
pairs, the base point free theorem, the contraction of a semiample divisor of positive Iitaka
dimension, "nef plus ample is ample" and Ambro's canonical bundle formula. -/
theorem linearEffectiveFreeness_of_kawamataViehweg_of_minimizerData_of_basePointFree_of_nefAddAmple
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hmin : KltMinimizerDataStatement.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hsa : SemiampleContractionPositiveStatement.{u}) (hna : NefAddAmpleStatement.{u})
    (hamb : AmbroContractionStatement.{u}) : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_nefAddAmple
    (kawamataNumericalFreeness_of_kawamataViehweg_of_minimizerData hKV hmin) hbpf hsa hna hamb

end MixedFujita

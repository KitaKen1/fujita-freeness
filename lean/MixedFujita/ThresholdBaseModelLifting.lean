/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ThresholdModelLifting

/-!
The lifting of §8 from (34) on, with the fixed part of the linear system instead of a general
member (§8; steps 13 and 14).

`ThresholdModelStatement` asks for one section σ of e A whose zero divisor satisfies the
inequalities along E'. Its proof in the manuscript needs a general member of the span of the
sections s_ℓ (Bertini). The lifting of §6.3 also accepts a divisor G of the model with
ρ*(u L_X) − G globally generated, weighted by η / M. With η = 1, M = h, u = e and no sections at
all, its conditions only concern G. On a log resolution ρ : T → X of the base ideal of the span of
the s_ℓ through the blow-up of x, the fixed part G of ρ* of that span has ρ*(e A) − G globally
generated, ord_{E'}(G) = n h = h A(E'), and for every other prime divisor t meeting E' the
inequality ord_t(G) < h A(t) is (34) for the base ideal restricted to the exceptional divisor,
transported to E' by adjunction on the simple normal crossing model. This is
`ThresholdBaseModelStatement`; no general member is needed.

Hence `ThresholdLiftingStatement` follows from the sum form of the Kawamata–Viehweg statement and
`ThresholdBaseModelStatement` (`thresholdLifting_of_thresholdBaseModel`), and F1 from the sum form
of the Kawamata–Viehweg statement, the closedness of the realization sets, Lemma 3 in its
degeneration form and `ThresholdBaseModelStatement`.
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

section Arithmetic

/-- The coefficient condition of §6.3 at E' for the divisor G alone with weight 1/h. -/
theorem thresholdBase_seq_real {h : ℕ} (hh : 0 < h) {g b : ℤ} (hgb : g = h * (1 + b))
    (c a : Fin 0 → ℝ) :
    (1 - (1 : ℝ)) * ∑ i, c i * a i + 1 / ((h : ℕ) : ℝ) * (g : ℝ) =
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [hgb]
  push_cast
  field_simp
  ring

/-- The coefficient inequality of §6.3 for the divisor G alone with weight 1/h. -/
theorem thresholdBase_le_real {h : ℕ} (hh : 0 < h) {g b : ℤ} (hgb : g ≤ h * (1 + b))
    (c a : Fin 0 → ℝ) :
    (1 - (1 : ℝ)) * ∑ i, c i * a i + 1 / ((h : ℕ) : ℝ) * (g : ℝ) ≤
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hgb' : (g : ℝ) ≤ h * (1 + b) := by exact_mod_cast hgb
  simp only [sub_self, zero_mul, zero_add, Nat.cast_one, div_one]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hh']
  linarith

/-- Equality in the coefficient condition of §6.3 for the divisor G alone with weight 1/h. -/
theorem thresholdBase_eq_real {h : ℕ} (hh : 0 < h) {g b : ℤ} (c a : Fin 0 → ℝ)
    (hgb : (1 - (1 : ℝ)) * ∑ i, c i * a i + 1 / ((h : ℕ) : ℝ) * (g : ℝ) =
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ)) : g = h * (1 + b) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [sub_self, zero_mul, zero_add, Nat.cast_one, div_one] at hgb
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hh'] at hgb
  have : (g : ℝ) = ((h * (1 + b) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

end Arithmetic

/-- The local part of the lifting of §8 (from (34) on) with the fixed part of the linear system:
given the sections of the equality case and (34) for their leading forms, there are a smooth proper
simple normal crossing model ρ : T → X (of the smooth variety with zero boundary) supporting the
exceptional divisors, an effective divisor G of T supported on the family with ρ*(e A) − G
globally generated, and a member E' over x such that ord_{E'}(G) = h A(E') and ord_t(G) ≤ h A(t)
for every prime divisor t of T meeting E', with equality only for E'. In the manuscript: a log
resolution of the base ideal of the span of the s_ℓ through the blow-up of x, G its fixed part,
and adjunction from T to the strict transform E' of the exceptional divisor, where (34) is the
threshold bound for the base ideal restricted to the exceptional divisor. -/
def ThresholdBaseModelStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
      (c₀ : EtaleChart K X n) (A : CartierDivisor X), CartierIsAmpleSum K A →
      ∀ x : X, IsClosed ({x} : Set X) →
      ∀ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
        (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) (e h : ℕ), 0 < h → e < h →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → Γ((e • A).sheaf, ⊤)),
          (∀ l, s l ≠ 0) →
          (∀ l, cartierSectionVanishingOrder _ x (s l) = (n * h : ℕ)) →
          ProjectiveThresholdCondition (fun l => homogeneousTaylorForm (n * h)
            (cartierTaylorCoordinates _ x (f ^ e) (cartierLocalEquation_pow A x f hf e)
              coordinates (s l))) h →
          ∃ (T : Scheme.{u}) (_ : IsIntegral T)
            (_ : IsLocallyNoetherian T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (_ : IsProper (T ↘ Spec (CommRingCat.of K))) (ρ : T ⟶ X) (_ : IsDominant ρ)
            (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
            (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
            (cT : EtaleChart K T n) (r : ℕ) (ξT : Fin r → T) (k₀ : Fin r) (G : CartierDivisor T),
            Function.Injective ξT ∧ (∀ k, Order.coheight (ξT k) = 1) ∧ IsSNCFamily K n ξT ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (t : T) = 0) ∧
            G.IsEffective ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient G (t : T) = 0) ∧
            CartierIsGloballyGenerated (cartierPullback ρ (e • A) - G) ∧
            ρ (ξT k₀) = x ∧
            cartierCoefficient G (ξT k₀) =
              (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (ξT k₀)) ∧
            ∀ t : CodimensionOnePoint T,
              (closure ({(t : T)} : Set T) ∩ closure ({ξT k₀} : Set T)).Nonempty →
              cartierCoefficient G (t : T) ≤
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) ∧
              (cartierCoefficient G (t : T) =
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) → (t : T) = ξT k₀)

/-- The lifting of §8 from (34) on follows from the sum form of the Kawamata–Viehweg statement and
the local statement with the fixed part, by the lifting of §6.3 on the isolation model with no
sections, η = 1 and the divisor G. -/
theorem thresholdLifting_of_thresholdBaseModel
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hmodel : ThresholdBaseModelStatement.{u}) : ThresholdLiftingStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN x hx f hf coordinates e h hh he ι _ _ s hs hord
    h34
  obtain ⟨T, _, _, _, _, _, ρ, _, _, _, hρ, cT, r, ξT, k₀, G, hinj, hξ, hsnc, hTB, hGeff, hTG,
    hGG, hρx, hEq, hmeet⟩ := hmodel K X n hdim hn c₀ A hA x hx f hf coordinates e h hh he s hs
    hord h34
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hnormT : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  obtain ⟨E, hE, -, hEc⟩ := exists_snc_component_cartier (K := K) ξT hξ hsnc
  obtain ⟨H, hH⟩ := cartierIsAmpleSum_exists_ample hA
  have hAp : CartierIsAmpleProj K A := cartierIsAmpleProj_of_isAmpleSum hA
  have hdimT : topologicalKrullDim T = topologicalKrullDim X :=
    (etaleChart_topologicalKrullDim cT).trans hdim.symm
  obtain ⟨g, f', u', hg, hf', hu'⟩ :=
    isolation_model_exists_section_generating_of_kawamataViehwegSum ρ hρ (hKV K n) hnormX (𝟙 X)
      dominantFunctionFieldMap_id_bijective (smoothCanonicalDivisor c₀ + A + N) x hx c₀ 1 1 le_rfl 0
      (fun z _ => by rw [cartierCoefficient_zero])
      (Fin.elim0 : Fin 0 → CartierDivisor X) (fun i => i.elim0) cT ξT hinj hξ hsnc E hE hEc hTB
      (fun i => i.elim0) G hGeff hTG (Fin.elim0 : Fin 0 → ℝ) (fun i => i.elim0) h 1 zero_le_one
      le_rfl {k₀} (Set.singleton_nonempty k₀)
      (fun k hk => by rw [Set.mem_singleton_iff.mp hk]; exact hρx)
      (fun k hk => by
        obtain rfl := Set.mem_singleton_iff.mp hk
        exact thresholdBase_seq_real hh hEq _ _)
      (fun t ⟨k, hk, hne⟩ => by
        obtain rfl := Set.mem_singleton_iff.mp hk
        obtain ⟨hle, heq⟩ := hmeet t hne
        exact ⟨thresholdBase_le_real hh hle _ _,
          fun h' => ⟨_, Set.mem_singleton _, heq (thresholdBase_eq_real hh _ _ h')⟩⟩)
      A N (by rw [cartierPullback_id, one_smul, one_smul, principalCartierDivisor_one, add_zero,
        add_zero]; abel)
      e (fun i => i.elim0) h hh (Fin.elim0 : Fin 0 → ℕ) 1 e (h - e) (fun i => i.elim0)
      (by push_cast; field_simp) (by simp; omega) (by omega)
      (cartierIsNef_cartierPullback_of_ample hH (cartierIsAmpleProj_isNef hAp) ρ)
      (cartierIsBig_cartierPullback hnormX hnormT ρ hρ hdimT (cartierIsAmpleSum_isBig hdim hn hA))
      (fun k => by
        rw [← cartierPullback_nsmul]
        exact finiteDimensional_sections_cartierPullback hnormX ρ hρ _
          (cartier_finiteDimensional_sections_of_ample hdim hn hH (k • A)))
      hGG (cartierIsNef_cartierPullback_of_ample hH hN ρ)
  exact ⟨f', hf', CartierDivisor.sectionMk _ hg,
    isUnit_cartierLocalCoefficient_sectionMk _ x g hg f' hf' u' hu'⟩

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, Lemma 3 in its degeneration
form, and the local statement with the fixed part for the lifting of §8. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_thresholdBaseModel
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hmodel : ThresholdBaseModelStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_thresholdLifting hKV hcl hdeg
    (thresholdLifting_of_thresholdBaseModel hKV hmodel)

end MixedFujita

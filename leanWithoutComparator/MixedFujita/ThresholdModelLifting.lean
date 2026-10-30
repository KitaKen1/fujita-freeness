/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityCaseThreshold
public import MixedFujita.IsolationModelNefBig
public import MixedFujita.KltIsolationGeneration
public import MixedFujita.SNCComponentCartier

/-!
The lifting of §8 from (34) on, from Kawamata–Viehweg vanishing and a local statement on a
resolution (§8; steps 13 and 14).

In §8 the sections s_ℓ of e A (e < h) vanish to order n h at the closed point x and their leading
forms satisfy (34) for h. The manuscript blows up x, takes a log resolution T, and lifts a section
from the strict transform E' of the exceptional divisor by Kawamata–Viehweg vanishing, adjunction
and descent. Here the cohomological part is the lifting of §6.3 on an isolation model, which is
proved (`isolation_model_exists_section_generating_of_kawamataViehwegSum`), applied with V = X,
the identity of X, d = 1, zero boundary, the single section σ of e A, the coefficient 1/h, η = 0,
G = 0, S = {E'}, L_X = A, N_X = N, m' = h, p = 1, w = 0 and e₁ = h − e ≥ 1. What is left is the
local statement `ThresholdModelStatement`: a nonzero σ ∈ Γ(e A) and a smooth proper simple normal
crossing model ρ : T → X with a member E' over x such that ord_{E'}(ρ* div σ) = h A(E') and
ord_t(ρ* div σ) < h A(t) for every other prime divisor t of T meeting E'. In the manuscript this is
a general member σ of the span of the s_ℓ (for which the pair (E, (1/h) div of its leading form)
is klt, by (34)), a log resolution through the blow-up of x, and adjunction from T to E' on the
simple normal crossing model; no inversion of adjunction and no cohomology is involved.

Hence `ThresholdLiftingStatement` follows from the sum form of the Kawamata–Viehweg statement and
`ThresholdModelStatement` (`thresholdLifting_of_thresholdModel`), and F1 from the sum form of the
Kawamata–Viehweg statement, the closedness of the realization sets, Lemma 3 in its degeneration
form and `ThresholdModelStatement`.
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

section Identity

variable {X : Scheme.{u}} [IsIntegral X]

/-- The function-field map of the identity is the identity. -/
theorem dominantFunctionFieldMap_id : dominantFunctionFieldMap (𝟙 X) = 𝟙 X.functionField := by
  ext a
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨genericPoint X, hV⟩⟩
  have : Nonempty ((𝟙 X) ⁻¹ᵁ V) := dominant_preimage_nonempty (𝟙 X) V
  change (dominantFunctionFieldMap (𝟙 X)).hom (X.germToFunctionField V s) =
    X.germToFunctionField V s
  rw [dominantFunctionFieldMap_germ (𝟙 X) V ((𝟙 X) ⁻¹ᵁ V) le_rfl, Scheme.Hom.appLE_eq_app,
    Scheme.Hom.id_app]
  rfl

/-- The function-field map of the identity is bijective. -/
theorem dominantFunctionFieldMap_id_bijective :
    Function.Bijective (dominantFunctionFieldMap (𝟙 X)).hom := by
  rw [dominantFunctionFieldMap_id]
  exact Function.bijective_id

/-- The pullback along the identity is the identity. -/
theorem cartierPullback_id (D : CartierDivisor X) : cartierPullback (𝟙 X) D = D := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt t
  have hmap : Units.map (dominantFunctionFieldMap (𝟙 X)).hom.toMonoidHom f = f := by
    apply Units.ext
    rw [Units.coe_map, dominantFunctionFieldMap_id]
    rfl
  refine ⟨f, ?_, hf⟩
  have h := cartierPullback_isLocalEquationAt (𝟙 X) D t (f := f) hf
  rwa [hmap] at h

end Identity

section Arithmetic

/-- The coefficient condition of §6.3 at E' for a single section with coefficient 1/h. -/
theorem thresholdModel_seq_real {h : ℕ} (hh : 0 < h) {a b : ℤ} (hab : a = h * (1 + b)) :
    (1 - (0 : ℝ)) * ∑ _i : Fin 1, 1 / (h : ℝ) * (a : ℝ) + 0 / ((1 : ℕ) : ℝ) * ((0 : ℤ) : ℝ) =
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [Fin.sum_univ_one, hab]
  push_cast
  field_simp
  ring

/-- The coefficient inequality of §6.3 for a single section with coefficient 1/h. -/
theorem thresholdModel_le_real {h : ℕ} (hh : 0 < h) {a b : ℤ} (hab : a ≤ h * (1 + b)) :
    (1 - (0 : ℝ)) * ∑ _i : Fin 1, 1 / (h : ℝ) * (a : ℝ) + 0 / ((1 : ℕ) : ℝ) * ((0 : ℤ) : ℝ) ≤
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hab' : (a : ℝ) ≤ h * (1 + b) := by exact_mod_cast hab
  simp only [sub_zero, one_mul, Fin.sum_univ_one, Nat.cast_one, div_one, Int.cast_zero, mul_zero,
    add_zero]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hh']
  linarith

/-- Equality in the coefficient condition of §6.3 for a single section with coefficient 1/h. -/
theorem thresholdModel_eq_real {h : ℕ} (hh : 0 < h) {a b : ℤ}
    (hab : (1 - (0 : ℝ)) * ∑ _i : Fin 1, 1 / (h : ℝ) * (a : ℝ) + 0 / ((1 : ℕ) : ℝ) * ((0 : ℤ) : ℝ) =
      (((1 : ℕ) : ℝ) + (b : ℝ)) / ((1 : ℕ) : ℝ)) : a = h * (1 + b) := by
  have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [sub_zero, one_mul, Fin.sum_univ_one, Nat.cast_one, div_one, Int.cast_zero, mul_zero,
    add_zero] at hab
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hh'] at hab
  have : (a : ℝ) = ((h * (1 + b) : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast this

end Arithmetic

/-- The local part of the lifting of §8 (from (34) on): given the sections of the equality case
and (34) for their leading forms, there are a nonzero section σ of e A and a smooth proper simple
normal crossing model ρ : T → X (of the smooth variety with zero boundary) supporting the
exceptional divisors and ρ* div σ, with a member E' over x such that ord_{E'}(ρ* div σ) = h A(E')
and ord_t(ρ* div σ) ≤ h A(t) for every prime divisor t of T meeting E', with equality only for
E'. In the manuscript: a general member σ of the span of the s_ℓ, a log resolution through the
blow-up of x, and adjunction from T to the strict transform E' of the exceptional divisor, where
(34) makes the pair (E, (1/h) div of the leading form of σ) klt. -/
def ThresholdModelStatement : Prop :=
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
          ∃ (σ : Γ((e • A).sheaf, ⊤)) (hσ : σ ≠ 0) (T : Scheme.{u}) (_ : IsIntegral T)
            (_ : IsLocallyNoetherian T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (_ : IsProper (T ↘ Spec (CommRingCat.of K))) (ρ : T ⟶ X) (_ : IsDominant ρ)
            (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
            (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
            (cT : EtaleChart K T n) (r : ℕ) (ξT : Fin r → T) (k₀ : Fin r),
            Function.Injective ξT ∧ (∀ k, Order.coheight (ξT k) = 1) ∧ IsSNCFamily K n ξT ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (t : T) = 0) ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (e • A) σ hσ))
                (t : T) = 0) ∧
            ρ (ξT k₀) = x ∧
            cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (e • A) σ hσ))
                (ξT k₀) =
              (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (ξT k₀)) ∧
            ∀ t : CodimensionOnePoint T,
              (closure ({(t : T)} : Set T) ∩ closure ({ξT k₀} : Set T)).Nonempty →
              cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (e • A) σ hσ))
                  (t : T) ≤
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) ∧
              (cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor (e • A) σ hσ))
                  (t : T) =
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) → (t : T) = ξT k₀)

/-- The lifting of §8 from (34) on follows from the sum form of the Kawamata–Viehweg statement and
the local statement on a resolution, by the lifting of §6.3 on the isolation model. -/
theorem thresholdLifting_of_thresholdModel
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hmodel : ThresholdModelStatement.{u}) : ThresholdLiftingStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN x hx f hf coordinates e h hh he ι _ _ s hs hord
    h34
  obtain ⟨σ, hσ, T, _, _, _, _, _, ρ, _, _, _, hρ, cT, r, ξT, k₀, hinj, hξ, hsnc, hTB, hTD, hρx,
    hEq, hmeet⟩ := hmodel K X n hdim hn c₀ A hA x hx f hf coordinates e h hh he s hs hord h34
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hnormT : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  obtain ⟨E, hE, -, hEc⟩ := exists_snc_component_cartier (K := K) ξT hξ hsnc
  obtain ⟨H, hH⟩ := cartierIsAmpleSum_exists_ample hA
  obtain ⟨m₀, -, hAgg⟩ := cartierIsAmpleSum_exists_globallyGenerated_divisible_sequence hA
  have hAp : CartierIsAmpleProj K A := cartierIsAmpleProj_of_isAmpleSum hA
  have hdimT : topologicalKrullDim T = topologicalKrullDim X :=
    (etaleChart_topologicalKrullDim cT).trans hdim.symm
  obtain ⟨g, f', u', hg, hf', hu'⟩ :=
    isolation_model_exists_section_generating_of_kawamataViehwegSum ρ hρ (hKV K n) hnormX (𝟙 X)
      dominantFunctionFieldMap_id_bijective (smoothCanonicalDivisor c₀ + A + N) x hx c₀ 1 1 le_rfl 0
      (fun z _ => by rw [cartierCoefficient_zero])
      (fun _ : Fin 1 => cartierSectionZeroDivisor (e • A) σ hσ)
      (fun _ => cartierSectionZeroDivisor_isEffective _ σ hσ) cT ξT hinj hξ hsnc E hE hEc hTB
      (fun _ => hTD) 0 CartierDivisor.isEffective_zero (fun t _ => cartierCoefficient_zero _)
      (fun _ => 1 / (h : ℝ)) (fun _ => by positivity) 1 0 le_rfl zero_le_one {k₀}
      (Set.singleton_nonempty k₀)
      (fun k hk => by rw [Set.mem_singleton_iff.mp hk]; exact hρx)
      (fun k hk => by
        obtain rfl := Set.mem_singleton_iff.mp hk
        rw [cartierCoefficient_zero]
        exact thresholdModel_seq_real hh hEq)
      (fun t ⟨k, hk, hne⟩ => by
        obtain rfl := Set.mem_singleton_iff.mp hk
        obtain ⟨hle, heq⟩ := hmeet t hne
        rw [cartierCoefficient_zero]
        exact ⟨thresholdModel_le_real hh hle,
          fun h' => ⟨_, Set.mem_singleton _, heq (thresholdModel_eq_real hh h')⟩⟩)
      A N (by rw [cartierPullback_id, one_smul, one_smul, principalCartierDivisor_one, add_zero,
        add_zero]; abel)
      e (fun _ => ⟨_, rfl⟩) h hh (fun _ => 1) 0 (0 * m₀) (h - e)
      (fun _ => by rw [sub_zero]; push_cast; field_simp) (by simp) (by simp; omega) (by omega)
      (cartierIsNef_cartierPullback_of_ample hH (cartierIsAmpleProj_isNef hAp) ρ)
      (cartierIsBig_cartierPullback hnormX hnormT ρ hρ hdimT (cartierIsAmpleSum_isBig hdim hn hA))
      (fun k => by
        rw [← cartierPullback_nsmul]
        exact finiteDimensional_sections_cartierPullback hnormX ρ hρ _
          (cartier_finiteDimensional_sections_of_ample hdim hn hH (k • A)))
      (by rw [sub_zero]; exact cartierIsGloballyGenerated_cartierPullback ρ _ (hAgg 0))
      (cartierIsNef_cartierPullback_of_ample hH hN ρ)
  exact ⟨f', hf', CartierDivisor.sectionMk _ hg,
    isUnit_cartierLocalCoefficient_sectionMk _ x g hg f' hf' u' hu'⟩

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, Lemma 3 in its degeneration
form, and the local statement on a resolution for the lifting of §8. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_thresholdModel
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
    (hmodel : ThresholdModelStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_thresholdLifting hKV hcl hdeg
    (thresholdLifting_of_thresholdModel hKV hmodel)

end MixedFujita

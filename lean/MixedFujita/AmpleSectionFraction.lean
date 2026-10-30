/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ScaledHilbertRatio
public import MixedFujita.RealizationSetsPrincipalShift
public import MixedFujita.RestrictedDimUpperBounds

/-!
A uniform positive fraction of sections in a small degree for every ample divisor.

Write l A = J + div(phi) for one hyperplane class. Ample comparison gives a section of M J − A,
so h⁰(j A) ≤ h⁰(M j J), while h⁰(l floor(theta j) A) = h⁰(floor(theta j) J).
The scaled Hilbert ratio is positive. Choosing theta small leaves (j − l floor(theta j)) A
globally generated and makes C l floor(theta j)/j ≤ 1/(2b). No Hilbert limit for A is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- Ample comparison bounds every degree of an arbitrary Cartier divisor by a fixed multiple of
a hyperplane class. -/
theorem cartier_finrank_le_hyperplane_multiple {N n : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
    (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (hdim : topologicalKrullDim Y = n) (hn : 1 ≤ n) (A : CartierDivisor Y) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ j : ℕ, Module.finrank K Γ((j • A).sheaf, ⊤) ≤
      Module.finrank K Γ(((M * j) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
  let J := projectiveHyperplaneCartier e g hg hggen
  have hJ : CartierIsAmpleProj K J := projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hJ (-A)
  have hGG : CartierIsGloballyGenerated ((j₀ + 1) • J - A) := by
    simpa only [sub_eq_add_neg, add_comm] using hj₀ (j₀ + 1) (by omega)
  obtain ⟨τ, hτ⟩ := cartierIsGloballyGenerated_exists_nonzero_section hGG
  obtain ⟨-, -, hfinJ, -⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdim hn
  refine ⟨j₀ + 1, by omega, fun j => ?_⟩
  have hdiv : j • A + j • ((j₀ + 1) • J - A) = ((j₀ + 1) * j) • J := by module
  have : FiniteDimensional K Γ((j • A + j • ((j₀ + 1) • J - A)).sheaf, ⊤) := by
    rw [hdiv]
    exact hfinJ _
  have hinj : Function.Injective (cartierSectionProductLinear (K := K) (j • A)
      (j • ((j₀ + 1) • J - A)) (cartierSectionPower _ τ j)) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    rw [LinearMap.mem_ker] at hs
    by_contra hs0
    exact cartierSectionProduct_ne_zero _ _ s _ hs0 (cartierSectionPower_ne_zero _ τ hτ j) hs
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [hdiv] at h

/-- For all sufficiently large degrees, a small degree q supplies a uniform positive fraction of
all sections, with C q/j ≤ 1/(2b), and the complementary degree is globally generated. -/
theorem cartierIsAmpleProj_exists_section_fraction {n : ℕ}
    (hdim : topologicalKrullDim Y = n) (hn : 1 ≤ n) {A : CartierDivisor Y}
    (hA : CartierIsAmpleProj K A) {C : ℕ} (hC : 1 ≤ C) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ᶠ j : ℕ in atTop, ∃ a q : ℕ,
      j = a + q ∧ 1 ≤ q ∧ ((C * q : ℕ) : ℝ) / j ≤ 1 / (2 * b) ∧
      CartierIsGloballyGenerated (a • A) ∧
      κ * (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) ≤
        Module.finrank K Γ((q • A).sheaf, ⊤) := by
  obtain ⟨l, hl, N, e, he, hbase, g, hg, hggen, φ, hlA⟩ := id hA
  obtain ⟨M, hM, hupper⟩ := cartier_finrank_le_hyperplane_multiple e g hg hggen hbase hdim hn A
  obtain ⟨r₀, hr₀, hfin, hlim⟩ :=
    projectiveHyperplane_hilbert_leading_integral e g hg hggen hbase hdim hn
  obtain ⟨j₀, hgen⟩ := cartierIsAmpleProj_eventually_globallyGenerated hA
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hl)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hC)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  let θ : ℝ := min (1 / (2 * l)) (1 / (2 * C * l * b))
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθl : (l : ℝ) * θ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 2 * l by positivity)).mp (min_le_left _ _ : θ ≤ _)
    linarith
  have hθclb : (C : ℝ) * l * θ * (2 * b) ≤ 1 := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 2 * C * l * b by positivity)).mp
      (min_le_right _ _ : θ ≤ _)
    nlinarith [h]
  have hθ1 : θ ≤ 1 := by
    have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hθM : θ / M ≤ 1 := (div_le_one hMpos).mpr (hθ1.trans (by exact_mod_cast hM))
  have hℓ : (0 : ℝ) < r₀ / n.factorial := by
    have : (0 : ℝ) < r₀ := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr₀)
    positivity
  have hratio := tendsto_ratio_floor_mul_of_tendsto_div_pow hℓ hlim hθ hM
  have hκ : 0 < (θ / M) ^ n / 2 := by positivity
  refine ⟨(θ / M) ^ n / 2, hκ, ?_, ?_⟩
  · have h : (θ / M) ^ n ≤ 1 := pow_le_one₀ (div_pos hθ hMpos).le hθM
    linarith
  have hev1 := hratio.eventually (lt_mem_nhds (half_lt_self (pow_pos (div_pos hθ hMpos) n)))
  have hev2 : ∀ᶠ j : ℕ in atTop, 1 ≤ ⌊θ * j⌋₊ :=
    (tendsto_nat_floor_mul_atTop θ hθ).eventually (eventually_ge_atTop 1)
  filter_upwards [hev1, hev2, eventually_ge_atTop (2 * j₀ + 1)] with j hratioj hr hj
  let r := ⌊θ * (j : ℝ)⌋₊
  let q := l * r
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hfloor : (r : ℝ) ≤ θ * j := Nat.floor_le (by positivity)
  have hqhalf : (q : ℝ) ≤ (j : ℝ) / 2 := by
    calc (q : ℝ) = (l : ℝ) * r := by simp only [q, Nat.cast_mul]
      _ ≤ (l : ℝ) * (θ * j) := mul_le_mul_of_nonneg_left hfloor hlpos.le
      _ = ((l : ℝ) * θ) * j := by ring
      _ ≤ (1 / 2 : ℝ) * j := mul_le_mul_of_nonneg_right hθl (Nat.cast_nonneg j)
      _ = (j : ℝ) / 2 := by ring
  have hq2 : 2 * q ≤ j := by exact_mod_cast (by linarith : 2 * (q : ℝ) ≤ j)
  have hcq : ((C * q : ℕ) : ℝ) / j ≤ 1 / (2 * b) := by
    rw [div_le_div_iff₀ hjpos (by positivity)]
    push_cast
    calc (C : ℝ) * q * (2 * b) = (C : ℝ) * l * r * (2 * b) := by simp only [q, Nat.cast_mul]; ring
      _ ≤ (C : ℝ) * l * (θ * j) * (2 * b) := by gcongr
      _ = ((C : ℝ) * l * θ * (2 * b)) * j := by ring
      _ ≤ 1 * j := mul_le_mul_of_nonneg_right hθclb (Nat.cast_nonneg j)
  refine ⟨j - q, q, (Nat.sub_add_cancel (by omega)).symm,
    (by simpa using Nat.mul_le_mul hl hr), hcq, hgen _ (by omega), ?_⟩
  have hdenpos : (0 : ℝ) < Module.finrank K
      Γ(((M * j) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    rcases (Nat.cast_nonneg (α := ℝ) (Module.finrank K
      Γ(((M * j) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))).lt_or_eq with hp | hz
    · exact hp
    · rw [← hz, div_zero] at hratioj
      linarith
  have hdimq := finrank_nsmul_eq_of_nsmul_eq (K := K) hlA r
  have hdimq' : Module.finrank K Γ((r • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) =
      Module.finrank K Γ((q • A).sheaf, ⊤) := by
    rwa [show r * l = q from Nat.mul_comm r l] at hdimq
  calc (θ / M) ^ n / 2 * (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) ≤
      (θ / M) ^ n / 2 * (Module.finrank K
        Γ(((M * j) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hupper j) hκ.le
    _ ≤ (Module.finrank K Γ((r • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) :=
      ((lt_div_iff₀ hdenpos).mp hratioj).le
    _ = _ := by exact_mod_cast hdimq'

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HomogeneousPrimeGrowth
public import MixedFujita.ProjectiveHilbertAsymptotics

/-!
Degree and Hilbert asymptotics of an actual integral closed subscheme of polynomial projective
space, without smoothness. A chain of irreducible closed subsets of length d gives a chain of
homogeneous primes, and the Hilbert function grows by one degree at each strict step, so the
degree-D image of the coordinate ring is at least c D^d. A relation among the parameters would
bound it by C (D+1)^(d-1), so the parameters are algebraically independent; the conductor, the
finiteness of the section spaces and the leading Hilbert coefficient follow as in the smooth
case. The leading coefficient r is the degree of the subvariety; this is the intersection number
J^d · W used in the hypotheses of S-NF, now available for singular W.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Asymptotics
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Chain

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]

omit [IsIntegral Y] [IsClosedImmersion e] in
theorem projective_asHomogeneousIdeal_le_of_specializes {a b : Y} (h : a ⤳ b) :
    (e a).asHomogeneousIdeal ≤ (e b).asHomogeneousIdeal := by
  have h' : e a ⤳ e b := h.map e.base.hom.continuous
  have hmem : e a ∈ ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin n) K)
      ((e a).asHomogeneousIdeal : Set (MvPolynomial (Fin n) K)) :=
    (ProjectiveSpectrum.mem_zeroLocus _ _ _).mpr subset_rfl
  have hb := h'.mem_closed (ProjectiveSpectrum.isClosed_zeroLocus _ _) hmem
  exact (ProjectiveSpectrum.mem_zeroLocus _ _ _).mp hb

/-- Growth of the Hilbert function of the coordinate ring along a chain of irreducible closed
subsets. -/
theorem projective_formImage_growth [QuasiSober Y] {d : ℕ}
    (hdim : (d : WithBot ℕ∞) ≤ topologicalKrullDim Y) :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D, D₀ ≤ D → c * (D : ℝ) ^ d ≤
      Module.finrank K (linearSystemFormImage
        (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal) D) := by
  obtain ⟨l, hl⟩ := (Order.le_krullDim_iff (α := IrreducibleCloseds Y)).mp hdim
  let z : Fin (l.length + 1) → Y := fun i => (l i).isIrreducible.genericPoint
  have hz : ∀ i, IsGenericPoint (z i) (l i : Set Y) := fun i =>
    (l i).isIrreducible.isGenericPoint_genericPoint (l i).isClosed
  let Q : Fin (l.length + 1) → Ideal (MvPolynomial (Fin n) K) := fun i =>
    (e (z i)).asHomogeneousIdeal.toIdeal
  have hQprime : ∀ i, (Q i).IsPrime := fun i => (e (z i)).isPrime
  have hstep : ∀ i : Fin l.length, Q i.succ < Q i.castSucc := by
    intro i
    have hlt : l.toFun i.castSucc < l.toFun i.succ := l.step i
    have hspec : z i.succ ⤳ z i.castSucc := by
      rw [specializes_iff_mem_closure, (hz i.succ).def]
      exact hlt.le (hz i.castSucc).mem
    have hle := projective_asHomogeneousIdeal_le_of_specializes e hspec
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hpt : e (z i.succ) = e (z i.castSucc) :=
      ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective heq)
    have hz' := (IsClosedImmersion.isClosedEmbedding e).injective hpt
    apply hlt.ne
    apply SetLike.coe_injective
    rw [← (hz i.castSucc).def, ← (hz i.succ).def, hz']
  have hbase : ∀ D, 1 ≤ Module.finrank K (linearSystemFormImage (P := Q 0) D) := by
    intro D
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e (z 0))
    have hX : (X k : MvPolynomial (Fin n) K) ∉ Q 0 := hk
    have hXD : (X k ^ D : MvPolynomial (Fin n) K) ∉ Q 0 := fun h =>
      hX ((hQprime 0).mem_of_pow_mem D h)
    have hmem : Ideal.Quotient.mk (Q 0) (X k ^ D) ∈ linearSystemFormImage (P := Q 0) D :=
      ⟨X k ^ D, isHomogeneous_X_pow k D, rfl⟩
    have hne : Ideal.Quotient.mk (Q 0) (X k ^ D) ≠ 0 := fun h =>
      hXD (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨_, hmem⟩, fun h => hne (congrArg Subtype.val h)⟩
  have hgrow : ∀ m (hm : m ≤ l.length), ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ D, D₀ ≤ D →
      c * (D : ℝ) ^ m ≤ Module.finrank K (linearSystemFormImage (P := Q ⟨m, by omega⟩) D) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, one_pos, 0, fun D _ => ?_⟩
      have := hbase D
      simp only [pow_zero, one_mul, Nat.one_le_cast]
      exact_mod_cast this
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hlt := hstep ⟨m, by omega⟩
      have hQm : (Q ⟨m, by omega⟩).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K) :=
        (e (z ⟨m, by omega⟩)).asHomogeneousIdeal.isHomogeneous
      have hQtop : Q ⟨m, by omega⟩ ≠ ⊤ := (hQprime _).ne_top
      obtain ⟨ε, hε, f, hf, hfQ, hfP⟩ := exists_homogeneous_mem_not_mem hQm hlt hQtop
      have := hQprime ⟨m + 1, by omega⟩
      have hrec : ∀ D, Module.finrank K (linearSystemFormImage (P := Q ⟨m, by omega⟩) (D + ε)) +
          Module.finrank K (linearSystemFormImage (P := Q ⟨m + 1, by omega⟩) D) ≤
            Module.finrank K (linearSystemFormImage (P := Q ⟨m + 1, by omega⟩) (D + ε)) :=
        fun D => linearSystemFormImage_finrank_step hlt.le hf hfQ hfP D
      exact growth_step hε hrec hprev
  obtain ⟨c, hc, D₀, hD₀⟩ := hgrow l.length le_rfl
  refine ⟨c, hc, D₀, fun D hD => ?_⟩
  have hle : (e (genericPoint Y)).asHomogeneousIdeal.toIdeal ≤ Q ⟨l.length, by omega⟩ :=
    projective_asHomogeneousIdeal_le_of_specializes e (genericPoint_specializes _)
  have hanti := linearSystemFormImage_finrank_antitone hle D
  have h1 := hD₀ D hD
  calc c * (D : ℝ) ^ d = c * (D : ℝ) ^ l.length := by rw [hl]
    _ ≤ _ := h1
    _ ≤ _ := by exact_mod_cast hanti

variable [QuasiSober Y]

/-- No nonzero homogeneous relation among the parameters, without smoothness. -/
theorem projective_linearSystem_relation_not_mem_integral {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (y : Fin (d + 1) → MvPolynomial (Fin n) K) (hy : ∀ i, (y i).IsHomogeneous 1) {t : ℕ}
    (hnull : ∀ α : Fin n →₀ ℕ, α.degree = t →
      monomial α (1 : K) ∈ linearSystemFiltration
        ((e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y (d + 1) t)
    {Φ : MvPolynomial (Fin (d + 1)) K} {δ : ℕ} (hΦ : Φ.IsHomogeneous δ) (hΦ0 : Φ ≠ 0) :
    aeval y Φ ∉ (e (genericPoint Y)).asHomogeneousIdeal := by
  intro hΦP
  obtain ⟨C, hC⟩ := linearSystemQuotientDim_le_of_relation
    (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal) y hy hd hnull hΦ hΦ0 hΦP
  obtain ⟨c, hc, D₀, hD₀⟩ := projective_formImage_growth e (d := d) hn.ge
  set N : ℕ := ⌈(C : ℝ) * 2 ^ (d - 1) / c⌉₊ with hNdef
  set D : ℕ := D₀ + N + 1 with hDdef
  have h1 := hD₀ D (by omega)
  have h2 := hC D
  rw [linearSystemQuotientDim_eq_finrank_formImage y D] at h2
  have h2' : (Module.finrank K (linearSystemFormImage
      (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal) D) : ℝ) ≤
        C * ((D : ℝ) + 1) ^ (d - 1) := by exact_mod_cast h2
  have hDpos : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hpow : ((D : ℝ) + 1) ^ (d - 1) ≤ 2 ^ (d - 1) * (D : ℝ) ^ (d - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hsplit : (D : ℝ) ^ d = D * (D : ℝ) ^ (d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hd]
  have hDd : 0 < (D : ℝ) ^ (d - 1) := by positivity
  have hC0 : (0 : ℝ) ≤ C := by positivity
  have h3 : c * D * (D : ℝ) ^ (d - 1) ≤ C * 2 ^ (d - 1) * (D : ℝ) ^ (d - 1) := by
    have := h1.trans (h2'.trans (mul_le_mul_of_nonneg_left hpow hC0))
    rw [hsplit] at this
    linarith
  have h4 : c * D ≤ C * 2 ^ (d - 1) := le_of_mul_le_mul_right h3 hDd
  have h5 : (C : ℝ) * 2 ^ (d - 1) / c < D := by
    have hceil := Nat.le_ceil ((C : ℝ) * 2 ^ (d - 1) / c)
    rw [← hNdef] at hceil
    have : (N : ℝ) + 1 ≤ D := by exact_mod_cast (show N + 1 ≤ D by omega)
    linarith
  rw [div_lt_iff₀ hc] at h5
  linarith

end Chain

variable {K : Type u} [Field K] [Infinite K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- One conductor form for all actual sections, without smoothness. -/
theorem projectiveSection_exists_conductor_integral
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d)
    (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ∃ (δ : MvPolynomial (Fin n) K) (k₀ : ℕ) (hδ : δ.IsHomogeneous k₀),
      δ ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
      ∀ (D : ℕ) (s : Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        IsProjectiveFormRatio e g hg hggen j₀ (k₀ + D)
          (projectiveFormRatio e g hg hggen j₀ k₀ δ hδ *
            cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s) := by
  have := polynomialProjectiveToBase_isProper n K
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨y, hy0, hyh, -, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  obtain ⟨B, δR, k₀, hδR, hδR0, hBind, -, hspan⟩ :=
    linearSystem_exists_commonDenominator (P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal)
      y hyh ht
  have hδ : (aeval y δR).IsHomogeneous k₀ := by
    have h := hδR.aeval y hyh
    rwa [one_mul] at h
  refine ⟨aeval y δR, k₀, hδ,
    projective_linearSystem_relation_not_mem_integral e hn hd y hyh ht hδR hδR0, fun D s => ?_⟩
  set r := cartierSectionRational (D • projectiveHyperplaneCartier e g hg hggen) s
  obtain ⟨N, hN⟩ := projectiveSection_form_mul_isFormRatio e g hg hggen he j₀ D s
  set i₁ : Fin (d + 1) := ⟨1, by omega⟩
  have hy0N : (y 0 ^ N).IsHomogeneous N := by simpa using (hyh 0).pow N
  have hy1N : (y i₁ ^ N).IsHomogeneous N := by simpa using (hyh i₁).pow N
  obtain ⟨a₀, ha₀, hr₀⟩ := hN N le_rfl (y 0 ^ N) hy0N
  obtain ⟨a₁, ha₁, hr₁⟩ := hN N le_rfl (y i₁ ^ N) hy1N
  have hs₀ := hspan (N + D) a₀ ha₀
  have hs₁ := hspan (N + D) a₁ ha₁
  rw [show N + D + k₀ = N + (D + k₀) by omega] at hs₀ hs₁
  -- The two sides agree as rational functions.
  have hcross : y i₁ ^ N * (aeval y δR * a₀) - y 0 ^ N * (aeval y δR * a₁) ∈
      (e (genericPoint Y)).asHomogeneousIdeal.toIdeal := by
    have hL := projectiveFormRatio_mul_three e g hg hggen j₀ hy1N hδ ha₀
    have hR := projectiveFormRatio_mul_three e g hg hggen j₀ hy0N hδ ha₁
    apply projectiveFormRatio_sub_mem_of_eq e g hg hggen j₀ (N + (k₀ + (N + D)))
      (hy1N.mul (hδ.mul ha₀)) (hy0N.mul (hδ.mul ha₁))
    rw [hL, hR, ← hr₀, ← hr₁]
    ring
  obtain ⟨G, hG, hGP⟩ := linearSystem_intersection y hyh hd hBind hs₀ hs₁ hcross
  have hG' : G.IsHomogeneous (k₀ + D) := by rwa [Nat.add_comm k₀ D]
  refine ⟨G, hG', ?_⟩
  have hL : projectiveFormRatio e g hg hggen j₀ (k₀ + (N + D)) (aeval y δR * a₀) (hδ.mul ha₀) =
      projectiveFormRatio e g hg hggen j₀ k₀ (aeval y δR) hδ *
        (projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N * r) := by
    rw [projectiveFormRatio_mul e g hg hggen j₀ k₀ (N + D) _ _ hδ ha₀, ← hr₀]
  have hY : (y 0 ^ N * G).IsHomogeneous (k₀ + (N + D)) := by
    have h := hy0N.mul hG'
    rwa [show N + (k₀ + D) = k₀ + (N + D) by omega] at h
  have hR : projectiveFormRatio e g hg hggen j₀ (k₀ + (N + D)) (y 0 ^ N * G) hY =
      projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N *
        projectiveFormRatio e g hg hggen j₀ (k₀ + D) G hG' := by
    rw [projectiveFormRatio_congr_poly e g hg hggen j₀ (show k₀ + (N + D) = N + (k₀ + D) by omega)
      rfl hY (hy0N.mul hG'), projectiveFormRatio_mul e g hg hggen j₀ N (k₀ + D) _ _ hy0N hG']
  have heq := projectiveFormRatio_eq_of_sub_mem e g hg hggen j₀ (k₀ + (N + D)) (hδ.mul ha₀) hY hGP
  rw [hL, hR] at heq
  have hne : projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N ≠ 0 := by
    intro h0
    have hmem := (projectiveFormRatio_eq_zero_iff e g hg hggen j₀ N _ hy0N).mp h0
    rw [hy0] at hmem
    exact hggen ((e (genericPoint Y)).isPrime.mem_of_pow_mem N hmem)
  have hzero : projectiveFormRatio e g hg hggen j₀ N (y 0 ^ N) hy0N *
      (projectiveFormRatio e g hg hggen j₀ k₀ (aeval y δR) hδ * r -
        projectiveFormRatio e g hg hggen j₀ (k₀ + D) G hG') = 0 := by
    linear_combination heq
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hne)

/-- The actual sections of D·J of an actual integral closed subscheme are finite-dimensional. -/
theorem projectiveHyperplaneSections_finiteDimensional_integral
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) (D : ℕ) :
    FiniteDimensional K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨δ, k₀, hδ, hδP, hcond⟩ :=
    projectiveSection_exists_conductor_integral e g hg hggen he hn hd j₀
  let f := ((cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀ D
    (projectiveFormSection e g hg hggen j₀ k₀ δ hδ))).codRestrict
      (projectiveFormSectionSpace e g hg hggen j₀ he (k₀ + D))
      (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ hcond D)
  have hf : Function.Injective f := by
    intro s t hst
    exact cartierNsmulProduct_injective _ k₀ D _
      (projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ hδP) (congrArg Subtype.val hst)
  exact Module.Finite.of_injective f hf

/-- The leading Hilbert coefficient of the hyperplane class of an actual integral closed subscheme,
without smoothness. -/
theorem projectiveHyperplane_hilbert_leading_integral
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∃ _ : ∀ D : ℕ, FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ d)
        atTop (nhds ((r : ℝ) / d.factorial)) := by
  have := polynomialProjectiveToBase_isProper n K
  have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    infer_instance
  have := polynomialProjective_closedImmersion_noetherianSpace e he
  obtain ⟨k', hk'⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k', ⟨⟨genericPoint Y, hk'⟩⟩⟩
  obtain ⟨y, hy0, hyh, -, hnz⟩ := projective_exists_linearSystem e hn.le g hg hggen
  obtain ⟨t, ht⟩ := projective_linearSystem_monomials_mem e y hyh hnz
  set P := (e (genericPoint Y)).asHomogeneousIdeal.toIdeal with hP
  have hPprime : P.IsPrime := (e (genericPoint Y)).isPrime
  obtain ⟨B, δR, k₀, hδR, hδR0, hBind, hBlow, hspan⟩ :=
    linearSystem_exists_commonDenominator (P := P) y hyh ht
  have hδP : aeval y δR ∉ P :=
    projective_linearSystem_relation_not_mem_integral e hn hd y hyh ht hδR hδR0
  have hδ : (aeval y δR).IsHomogeneous k₀ := by
    have h := hδR.aeval y hyh
    rwa [one_mul] at h
  obtain ⟨δ', k₀', hδ', hδ'P, hcond⟩ :=
    projectiveSection_exists_conductor_integral e g hg hggen he hn hd j₀
  have hfin := projectiveHyperplaneSections_finiteDimensional_integral e g hg hggen he hn hd
  -- dimensions of the form images
  have hdimV : ∀ D, Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) =
      Module.finrank K (linearSystemFormImage (P := P) D) := by
    intro D
    rw [projectiveFormSectionSpace_finrank, ← linearSystemQuotientDim_eq_finrank_formImage y D]
    unfold linearSystemQuotientDim
    rw [linearSystemFiltration_zero]
  -- sections between the form images
  have hlowΓ : ∀ D, Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he D) ≤
      Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
    fun D => Submodule.finrank_le _
  have hupΓ : ∀ D, Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
      Module.finrank K (projectiveFormSectionSpace e g hg hggen j₀ he (k₀' + D)) := by
    intro D
    let f := ((cartierNsmulProductLinear (K := K) (projectiveHyperplaneCartier e g hg hggen) k₀' D
      (projectiveFormSection e g hg hggen j₀ k₀' δ' hδ'))).codRestrict
        (projectiveFormSectionSpace e g hg hggen j₀ he (k₀' + D))
        (projectiveSection_conductor_mul_mem e g hg hggen he j₀ hδ' hcond D)
    refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
    intro s s' hss
    exact cartierNsmulProduct_injective _ k₀' D _
      (projectiveFormSection_ne_zero_of_not_mem e g hg hggen j₀ hδ' hδ'P) (congrArg Subtype.val hss)
  -- the free-part bounds
  have hlow : ∀ m, B.card * (m + d).choose d ≤
      Module.finrank K (linearSystemFormImage (P := P) (m + t)) := by
    intro m
    refine le_trans ?_ (linearSystem_freePart_le y hyh hBind (m + t))
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_le_sum fun b hb => ?_
    have hbt : b.degree < t := hBlow b hb
    rw [one_mul, ite_eq_left (show b.degree ≤ m + t by omega)]
    exact Nat.choose_le_choose d (by omega)
  have hup : ∀ D, Module.finrank K (linearSystemFormImage (P := P) D) ≤
      B.card * (D + k₀ + d).choose d := by
    intro D
    refine (linearSystem_formImage_le_freePart y hδP hspan D).trans ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [one_mul]
    split_ifs
    · exact Nat.choose_le_choose d (by omega)
    · exact Nat.zero_le _
  refine ⟨B.card, ?_, hfin, ?_⟩
  · -- r ≥ 1: otherwise the form images vanish, against the growth along a chain
    rcases Nat.eq_zero_or_pos B.card with hB0 | hpos
    swap
    · exact hpos
    exfalso
    have hgrowth := projective_formImage_growth e (d := d) hn.ge
    rw [← hP] at hgrowth
    obtain ⟨c, hc, D₀, hD₀⟩ := hgrowth
    have h1 := hD₀ (D₀ + 1) (by omega)
    have h2 := hup (D₀ + 1)
    rw [hB0, zero_mul] at h2
    have h3 : Module.finrank K (linearSystemFormImage (P := P) (D₀ + 1)) = 0 := by omega
    rw [h3, Nat.cast_zero] at h1
    have h4 : (0 : ℝ) < c * ((D₀ + 1 : ℕ) : ℝ) ^ d := by positivity
    linarith
  · apply tendsto_div_pow_of_choose_bounds (t := t) (c := t + k₀' + k₀)
      (h := fun D => Module.finrank K Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    · intro m
      exact (hlow m).trans ((hdimV (m + t)).symm.le.trans (hlowΓ (m + t)))
    · intro m
      refine (hupΓ (m + t)).trans ?_
      rw [hdimV]
      refine (hup (k₀' + (m + t))).trans ?_
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose d (by omega))

end MixedFujita

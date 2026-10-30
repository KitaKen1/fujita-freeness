module
public import MixedFujita.AmpleIitakaExistence

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower
variable {K : Type u} [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The existing ample Hilbert upper bound only needs an infinite base field. -/
theorem cartierIsAmpleProj_finrank_polynomial_upper_of_infinite {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n) {D : CartierDivisor X}
    (hD : CartierIsAmpleProj K D) :
    ∃ C : ℝ, ∀ j : ℕ, (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      C * ((j : ℝ) + 1) ^ n := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_veryAmple hD
  obtain ⟨j₁, hj₁⟩ := cartierIsAmpleProj_eventually_globallyGenerated hD
  let M := j₀ + j₁ + 1
  obtain ⟨Nv, e, he, hbase, g, hg, hggen, f, hMD⟩ := hj₀ M (by dsimp [M]; omega)
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (hj₁ (M - 1) (by dsimp [M]; omega))
  obtain ⟨-, -, hfinJ, -⟩ :=
    projectiveHyperplane_hilbert_leading_integral e g hg hggen hbase hdim hn
  obtain ⟨C, hC⟩ := projectiveHyperplane_exists_finrank_le_mul_pow e g hg hggen hbase hdim hn
  refine ⟨C, fun j => ?_⟩
  have hjM : j • D + j • ((M - 1) • D) = j • (M • D) := by
    rw [← nsmul_add, ← succ_nsmul', Nat.sub_add_cancel (show 1 ≤ M by dsimp [M]; omega)]
  have hdiv : j • D + j • ((M - 1) • D) =
      j • projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor X (f ^ j) := by
    rw [hjM, hMD, nsmul_add, principalCartierDivisor_power]
  have := hfinJ j
  have hfinT : FiniteDimensional K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) := by
    rw [hdiv]
    exact Module.Finite.equiv (cartierPrincipalShiftEquiv (K := K) _ _).symm
  have hle := finrank_le_of_eq_add_of_section (K := K) (j • D) (j • ((M - 1) • D)) _ rfl
    (cartierSectionPower _ t j) (cartierSectionPower_ne_zero _ t ht j) hfinT
  have heq : Module.finrank K Γ((j • D + j • ((M - 1) • D)).sheaf, ⊤) =
      Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    rw [hdiv, finrank_add_principal]
  have hleR : (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    exact_mod_cast hle.trans heq.le
  exact hleR.trans (hC j)

/-- A fixed correction and arbitrary Cartier direction have finite sections on
the same positive-dimensional projective base; neither divisor is assumed positive. -/
theorem cartier_affineMultiples_finiteDimensional_of_projective {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (D F : CartierDivisor X) : ∀ j : ℕ, FiniteDimensional K Γ((j • D + F).sheaf, ⊤) := by
  obtain ⟨H, hH⟩ := hProj
  exact fun j => cartier_finiteDimensional_sections_of_ample hdim hn hH (j • D + F)

/-- The whole fixed-correction sequence has one polynomial upper bound of degree
the base dimension, over any infinite field and without positivity of D or F. -/
theorem cartier_affineMultiples_finrank_polynomial_upper_of_projective {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (D F : CartierDivisor X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, (Module.finrank K Γ((j • D + F).sheaf, ⊤) : ℝ) ≤
      C * ((j : ℝ) + 1) ^ n := by
  obtain ⟨H, hH⟩ := hProj
  obtain ⟨N, hN⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (-D)
  obtain ⟨M, hM⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (-F)
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hN N le_rfl)
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hM M le_rfl)
  obtain ⟨c, hc⟩ := cartierIsAmpleProj_finrank_polynomial_upper_of_infinite hdim hn hH
  refine ⟨max c 0 * (((N + M : ℕ) : ℝ) + 1) ^ n, by positivity, fun j => ?_⟩
  let G := j • (-D + N • H) + (-F + M • H)
  let σ : Γ(G.sheaf, ⊤) := cartierSectionProduct _ _ (cartierSectionPower _ s j) t
  have hσ : σ ≠ 0 := cartierSectionProduct_ne_zero _ _ _ _
    (cartierSectionPower_ne_zero _ s hs j) ht
  have hsum : j • D + F + G = (j * N + M) • H := by
    dsimp [G]
    rw [nsmul_add, smul_neg, smul_smul, add_nsmul]
    abel
  have hfin := cartierIsAmpleProj_finiteDimensional_nsmul hdim hn hH (j * N + M)
  have hle := finrank_le_of_eq_add_of_section (K := K) (j • D + F) G _ hsum.symm σ hσ hfin
  have hleR : (Module.finrank K Γ((j • D + F).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ(((j * N + M) • H).sheaf, ⊤) := by exact_mod_cast hle
  have hindex : (((j * N + M : ℕ) : ℝ) + 1) ≤
      (((N + M : ℕ) : ℝ) + 1) * ((j : ℝ) + 1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
      (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  calc
    _ ≤ (Module.finrank K Γ(((j * N + M) • H).sheaf, ⊤) : ℝ) := hleR
    _ ≤ c * ((((j * N + M : ℕ) : ℝ)) + 1) ^ n := hc _
    _ ≤ max c 0 * ((((j * N + M : ℕ) : ℝ)) + 1) ^ n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max c 0 * ((((N + M : ℕ) : ℝ) + 1) * ((j : ℝ) + 1)) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hindex n) (le_max_right _ _)
    _ = _ := by rw [mul_pow]; ring

end MixedFujita

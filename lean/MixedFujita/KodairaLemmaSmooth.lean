/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KodairaLemmaPieces
public import MixedFujita.ProjectiveAmpleMinimizerData
public import MixedFujita.ProjectivePullbackFixedClass
public import MixedFujita.CartierGloballyGeneratedBoundaryPerturbation
public import MixedFujita.TangentCoordinateChain
public import MixedFujita.AmpleEffectiveComparison
public import MixedFujita.CoprimeAmpleGlobalGeneration
public import MixedFujita.SNCWeightDiscrepancyInterval
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.CartierSectionPrimeDecomposition

/-!
Kodaira's lemma on a smooth projective variety (step 17).

Let T be a smooth integral Noetherian scheme over an algebraically closed field of characteristic
zero, with a closed immersion e into projective space, hyperplane class J₀ = div g, and dimension
n ≥ 1. For a big Cartier divisor B there are m ≥ 1 and a nonzero section of m B − J₀
(`exists_section_nsmul_sub_projectiveHyperplane_of_isBig`). The proof is the counting argument:

* a J₀ − B is globally generated for some a ≥ 1; take a nonzero section σ₀;
* Bertini gives a section s of J₀ whose zero divisor is reduced, with prime components η_i, and
  avoids the finitely many components of the zero divisor of σ₀, so σ₀ does not vanish at η_i;
* h⁰(m B) ≤ h⁰(m B − J₀) + Σ_i (restricted dimension of m B at η_i)
  (`finrank_le_finrank_sub_add_sum_cartierRestrictedDim`, Hartogs on the normal T);
* multiplication by σ₀^m bounds the restricted dimension of m B at η_i by that of (m a) J₀, which
  is at most C_i (m a + 1)^(n − 1)
  (`projectiveHyperplane_exists_cartierRestrictedDim_le_of_coheight_eq_one`: a coordinate not
  vanishing at η_i, the principal shift, the dimension of the closure of η_i and Lemma 4's Hilbert
  limit, or the residue field at a closed point);
* B is big: h⁰(m B) ≥ c m^n for infinitely many m, so h⁰(m B − J₀) > 0 for one of them.
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

section Shift

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- The restricted dimension does not change under a principal shift of the divisor. -/
theorem cartierRestrictedDim_add_principal (D : CartierDivisor X) (g : X.functionFieldˣ)
    (η : X) :
    cartierRestrictedDim K (D + principalCartierDivisor X g) η = cartierRestrictedDim K D η := by
  have hmap : (cartierSectionsVanishingAt K (D + principalCartierDivisor X g) η).map
      ((cartierPrincipalShiftEquiv (K := K) D g : _ ≃ₗ[K] _) : _ →ₗ[K] _) =
      cartierSectionsVanishingAt K D η := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (mem_cartierSectionsVanishingAt_principalShift D g η s).mp hs
    · intro ht
      refine ⟨(cartierPrincipalShiftEquiv (K := K) D g).symm t,
        (mem_cartierSectionsVanishingAt_principalShift D g η _).mpr ?_,
        (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply t⟩
      have h1 : cartierPrincipalShiftLinear (K := K) D g
          ((cartierPrincipalShiftEquiv (K := K) D g).symm t) = t :=
        (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply t
      rw [h1]
      exact ht
  exact (Submodule.Quotient.equiv _ _ (cartierPrincipalShiftEquiv (K := K) D g) hmap).finrank_eq

/-- A section not vanishing at η has powers not vanishing at η. -/
theorem cartierSectionPower_notMem_vanishingAt (D : CartierDivisor X) (η : X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ∉ cartierSectionsVanishingAt K D η) (k : ℕ) :
    cartierSectionPower D s k ∉ cartierSectionsVanishingAt K (k • D) η := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt η
  rw [mem_cartierSectionsVanishingAt_iff (k • D) η (f ^ k) (cartierLocalEquation_pow D η f hf k),
    cartierSectionPower_localCoefficient D η f hf s k]
  rw [mem_cartierSectionsVanishingAt_iff D η f hf] at hs
  exact fun h => hs
    ((IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk η)).isPrime.mem_of_pow_mem k h)

end Shift

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] {N : ℕ} {T : Scheme.{u}} [IsIntegral T]
  [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  (e : T ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint T)).asHomogeneousIdeal)

/-- At a codimension-one point η of a smooth closed subvariety of dimension n of projective space,
the sections of q J₀ restricted at η have dimension at most C (q + 1)^(n − 1). -/
theorem projectiveHyperplane_exists_cartierRestrictedDim_le_of_coheight_eq_one
    (he : e ≫ polynomialProjectiveToBase N K = T ↘ Spec (CommRingCat.of K)) {n : ℕ}
    (hdim : topologicalKrullDim T = n) (η : T) (hη : Order.coheight η = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, (cartierRestrictedDim K
      (q • projectiveHyperplaneCartier e g hg hggen) η : ℝ) ≤ C * ((q : ℝ) + 1) ^ (n - 1) := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart N K (e η)
  have hkgen : (MvPolynomial.X k : MvPolynomial (Fin N) K) ∉
      (e (genericPoint T)).asHomogeneousIdeal := by
    have hsp : genericPoint T ⤳ η := (genericPoint_spec T).specializes (Set.mem_univ η)
    exact (hsp.map e.continuous).mem_open (Proj.basicOpen _ _).isOpen hk
  have hXk : (MvPolynomial.X k : MvPolynomial (Fin N) K).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X K k
  have hne : Nonempty (projectivePullbackCoordinateOpen e k) := ⟨⟨η, hk⟩⟩
  have hshift := projectivePullbackHomogeneousCartier_eq_principalShift e ⟨k, hne⟩ 1 g hg
    (MvPolynomial.X k) hXk Nat.one_pos hggen hkgen
  have hq : ∀ q : ℕ, cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) η =
      cartierRestrictedDim K
        (q • projectiveHyperplaneCartier e (MvPolynomial.X k) hXk hkgen) η := by
    intro q
    rw [show q • projectiveHyperplaneCartier e g hg hggen =
        q • projectiveHyperplaneCartier e (MvPolynomial.X k) hXk hkgen +
          principalCartierDivisor T (projectivePullbackHomogeneousRatio e ⟨k, hne⟩ 1 g hg
            (MvPolynomial.X k) hXk Nat.one_pos hggen hkgen ^ q) by
      rw [principalCartierDivisor_power, ← nsmul_add]
      exact congrArg (q • ·) hshift]
    exact cartierRestrictedDim_add_principal _ _ _
  have hn1 : 1 ≤ n := by
    have := TauCeti.coheight_le_topologicalKrullDim η
    rw [hη, hdim] at this
    exact_mod_cast this
  obtain ⟨-, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading_integral e (MvPolynomial.X k) hXk
    hkgen he hdim hn1
  obtain ⟨d, hdn, hdclos⟩ := exists_topologicalKrullDim_closure_eq_of_coheight_eq_one hdim hη
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hclosed : IsClosed ({η} : Set T) := by
      rw [← closure_subset_iff_isClosed]
      intro y hy
      by_contra hyη
      have hsp : η ⤳ y := specializes_iff_mem_closure.mpr hy
      have hne' : η ≠ y := fun h => hyη (Set.mem_singleton_iff.mpr h.symm)
      have h1 := le_topologicalKrullDim_closure_of_generization_chain 1 ![y, η]
        (fun i => by fin_cases i; simpa using hsp)
        (fun i => by fin_cases i; simpa using hne')
      have hlast : (![y, η] : Fin 2 → T) (Fin.last 1) = η := rfl
      rw [hlast, hdclos] at h1
      exact absurd h1 (by norm_num)
    refine ⟨1, zero_le_one, fun q => ?_⟩
    have h1 := cartierRestrictedDim_le_one_of_isClosed (K := K)
      (q • projectiveHyperplaneCartier e g hg hggen) η hclosed
    have hq1 : (1 : ℝ) ≤ ((q : ℝ) + 1) ^ (n - 1) :=
      one_le_pow₀ (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)])
    calc (cartierRestrictedDim K (q • projectiveHyperplaneCartier e g hg hggen) η : ℝ) ≤ 1 := by
          exact_mod_cast h1
      _ ≤ 1 * ((q : ℝ) + 1) ^ (n - 1) := by rw [one_mul]; exact hq1
  · obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have hgW : (MvPolynomial.X k : MvPolynomial (Fin N) K) ∉
        ((pointClosureι η ≫ e) (genericPoint (pointClosureScheme η))).asHomogeneousIdeal := by
      rw [Scheme.Hom.comp_apply, pointClosureι_genericPoint]
      exact hk
    obtain ⟨C, hC⟩ := projectiveHyperplane_exists_cartierRestrictedDim_le_mul_pow e
      (MvPolynomial.X k) hXk hkgen he η hdclos hgW
    have hC0 : 0 ≤ C := by
      have h0 := hC 0
      have hnn : (0 : ℝ) ≤ (cartierRestrictedDim K
          ((0 : ℕ) • projectiveHyperplaneCartier e (MvPolynomial.X k) hXk hkgen) η : ℝ) :=
        Nat.cast_nonneg _
      simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at h0
      linarith
    refine ⟨C, hC0, fun q => ?_⟩
    rw [hq q]
    have hq1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    calc _ ≤ C * ((q : ℝ) + 1) ^ (d' + 1) := hC q
      _ ≤ C * ((q : ℝ) + 1) ^ (n - 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq1 (by omega)) hC0

end Hyperplane

section Smooth

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N : ℕ} {T : Scheme.{u}}
  [IsIntegral T] [IsNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [Smooth (T ↘ Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  (e : T ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint T)).asHomogeneousIdeal)

/-- Kodaira's lemma on a smooth projective variety: for a big Cartier divisor B some m B − J₀ with
m ≥ 1 has a nonzero section, J₀ the hyperplane class. -/
theorem exists_section_nsmul_sub_projectiveHyperplane_of_isBig
    (he : e ≫ polynomialProjectiveToBase N K = T ↘ Spec (CommRingCat.of K)) {n : ℕ}
    (hdim : topologicalKrullDim T = n) (hn : 1 ≤ n) {r : ℕ} (ξ : Fin r → T)
    (hξ : IsSNCFamily K n ξ) (B : CartierDivisor T) (hB : CartierIsBig K B) :
    ∃ (m : ℕ) (_ : 1 ≤ m)
      (s : Γ((m • B - projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)), s ≠ 0 := by
  classical
  set J₀ := projectiveHyperplaneCartier e g hg hggen with hJ₀
  have hJ₀amp : CartierIsAmpleProj K J₀ := projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  have hJ₀va : CartierIsVeryAmpleProj K J₀ :=
    ⟨N, e, inferInstance, he, g, hg, hggen, 1, by rw [principalCartierDivisor_one, add_zero]⟩
  have hJ₀gg := cartierIsVeryAmpleProj_isGloballyGenerated hJ₀va
  have hnorm : ∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := K) x
  obtain ⟨-, -, hfinJ, -⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdim hn
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hJ₀amp (-B)
  set a := j₀ + 1 with ha
  set E₀ := -B + a • J₀ with hE₀
  obtain ⟨σ₀, hσ₀⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hj₀ a (by omega))
  set Z : Set T := (fun z : CodimensionOnePoint T => (z : T)) ''
    ↑((cartierSectionZeroDivisor E₀ σ₀ hσ₀).toWeilDivisor.support) with hZdef
  have hZ : Z.Finite := (Finset.finite_toSet _).image _
  obtain ⟨s, hs, q, η, -, -, hcoh, hcover, -, hcoeff, havoid⟩ :=
    cartierIsGloballyGenerated_exists_reduced_prime_snc_avoiding J₀ hJ₀gg ξ hξ Z hZ
  set η' : Fin q → CodimensionOnePoint T := fun i => ⟨η i, hcoh i⟩ with hη'
  have hcoef₁ : ∀ i, cartierCoefficient (cartierSectionZeroDivisor J₀ s hs) (η' i : T) ≤ 1 := by
    intro i
    rw [hcoeff (η' i)]
    split_ifs <;> norm_num
  have hcoef₀ : ∀ z : CodimensionOnePoint T, z ∉ Set.range η' →
      cartierCoefficient (cartierSectionZeroDivisor J₀ s hs) (z : T) ≤ 0 := by
    intro z hz
    rw [hcoeff z]
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      exact absurd ⟨i, Subtype.ext hi⟩ hz
    · exact le_refl 0
  have hσ₀η : ∀ i, σ₀ ∉ cartierSectionsVanishingAt K E₀ (η' i : T) := by
    intro i hvan
    have h1 : 1 ≤ T.ord (cartierSectionRational E₀ σ₀) (η' i : T) +
        cartierCoefficient E₀ (η' i : T) :=
      one_le_ord_add_coefficient_of_mem_vanishingAt hnorm E₀ (η' i) σ₀ hσ₀ hvan
    have hZc : cartierCoefficient (cartierSectionZeroDivisor E₀ σ₀ hσ₀) (η' i : T) =
        cartierCoefficient E₀ (η' i : T) + T.ord (cartierSectionRational E₀ σ₀) (η' i : T) := by
      rw [cartierSectionZeroDivisor, cartierCoefficient_add, cartierCoefficient_principal,
        cartierSectionUnit_val]
    have hmemZ : (η' i : T) ∈ Z := by
      refine ⟨η' i, ?_, rfl⟩
      rw [Finset.mem_coe, WeilDivisor.mem_support_iff,
        cartier_toWeilDivisor_coeff_eq_cartierCoefficient]
      omega
    exact havoid _ hmemZ (by rw [hcover]; exact Set.mem_iUnion.mpr ⟨i, subset_closure rfl⟩)
  have hC : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ q' : ℕ,
      (cartierRestrictedDim K (q' • J₀) (η' i : T) : ℝ) ≤ C * ((q' : ℝ) + 1) ^ (n - 1) :=
    fun i => projectiveHyperplane_exists_cartierRestrictedDim_le_of_coheight_eq_one e g hg hggen
      he hdim (η' i : T) (η' i).2
  choose C hC0 hCb using hC
  obtain ⟨d, hd, c, hc, hfreq⟩ := hB
  have hdn : d = n := by
    have h := hd.symm.trans hdim
    exact_mod_cast h
  rw [hdn] at hfreq
  set C' : ℝ := (∑ i, C i) * (2 * (a : ℝ)) ^ (n - 1) with hC'
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (C' / c)
  obtain ⟨m, hmfr, hmM⟩ := (hfreq.and_eventually (eventually_ge_atTop (M₀ + 1))).exists
  have hdivm : m • B + m • E₀ = (m * a) • J₀ := by
    rw [hE₀]
    module
  have hfinma : FiniteDimensional K Γ((m • B + m • E₀).sheaf, ⊤) := by
    rw [hdivm]; exact hfinJ _
  have hfinB : FiniteDimensional K Γ((m • B).sheaf, ⊤) :=
    finiteDimensional_of_section_mul (m • B) (m • E₀) (cartierSectionPower E₀ σ₀ m)
      (cartierSectionPower_ne_zero E₀ σ₀ hσ₀ m)
  obtain ⟨t', ht'⟩ : ∃ t', m * a = t' + 1 :=
    ⟨m * a - 1, (Nat.sub_add_cancel (Nat.mul_pos (by omega) (by omega))).symm⟩
  have hdivm' : m • B - J₀ + m • E₀ = t' • J₀ := by
    rw [show m • B - J₀ + m • E₀ = (m • B + m • E₀) - J₀ by abel, hdivm, ht', add_nsmul,
      one_nsmul]
    abel
  have hfinBJ' : FiniteDimensional K Γ((m • B - J₀ + m • E₀).sheaf, ⊤) := by
    rw [hdivm']; exact hfinJ _
  have hfinBJ : FiniteDimensional K Γ((m • B - J₀).sheaf, ⊤) :=
    finiteDimensional_of_section_mul (m • B - J₀) (m • E₀) (cartierSectionPower E₀ σ₀ m)
      (cartierSectionPower_ne_zero E₀ σ₀ hσ₀ m)
  have hcount := finrank_le_finrank_sub_add_sum_cartierRestrictedDim (K := K) hnorm (m • B) J₀ s hs
    η'
    hcoef₁ hcoef₀
  have hrd : ∀ i, cartierRestrictedDim K (m • B) (η' i : T) ≤
      cartierRestrictedDim K ((m * a) • J₀) (η' i : T) := by
    intro i
    have h := cartierRestrictedDim_le_add_of_not_mem K (m • B) (m • E₀) (η' i : T)
      (cartierSectionPower E₀ σ₀ m) (cartierSectionPower_notMem_vanishingAt E₀ _ σ₀ (hσ₀η i) m)
    rwa [hdivm] at h
  have hm1 : 1 ≤ m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hsum : (∑ i, (cartierRestrictedDim K (m • B) (η' i : T) : ℝ)) ≤
      C' * (m : ℝ) ^ (n - 1) := by
    rw [hC', Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (cartierRestrictedDim K (m • B) (η' i : T) : ℝ) ≤
        cartierRestrictedDim K ((m * a) • J₀) (η' i : T) := by exact_mod_cast hrd i
    have h3 : ((m * a : ℕ) : ℝ) + 1 ≤ 2 * (a : ℝ) * m := by
      push_cast
      nlinarith
    have h4 : (((m * a : ℕ) : ℝ) + 1) ^ (n - 1) ≤ (2 * (a : ℝ) * m) ^ (n - 1) :=
      pow_le_pow_left₀ (by positivity) h3 _
    calc (cartierRestrictedDim K (m • B) (η' i : T) : ℝ)
        ≤ C i * (((m * a : ℕ) : ℝ) + 1) ^ (n - 1) := h1.trans (hCb i (m * a))
      _ ≤ C i * (2 * (a : ℝ) * m) ^ (n - 1) := mul_le_mul_of_nonneg_left h4 (hC0 i)
      _ = C i * (2 * (a : ℝ)) ^ (n - 1) * (m : ℝ) ^ (n - 1) := by rw [mul_pow]; ring
  have hcast : (Module.finrank K Γ((m • B).sheaf, ⊤) : ℝ) ≤
      Module.finrank K Γ((m • B - J₀).sheaf, ⊤) +
        ∑ i, (cartierRestrictedDim K (m • B) (η' i : T) : ℝ) := by
    exact_mod_cast hcount
  have hmM' : C' / c < m := lt_of_lt_of_le hM₀ (by exact_mod_cast (show M₀ ≤ m by omega))
  have hcm : C' < c * m := by
    rw [div_lt_iff₀ hc] at hmM'
    linarith
  have hmpow : (0 : ℝ) < (m : ℝ) ^ (n - 1) := pow_pos (by linarith) _
  have hmn : (m : ℝ) ^ n = m * (m : ℝ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlt : C' * (m : ℝ) ^ (n - 1) < c * (m : ℝ) ^ n := by
    rw [hmn, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hcm hmpow
  have hreal : (0 : ℝ) < Module.finrank K Γ((m • B - J₀).sheaf, ⊤) := by linarith
  have hpos : 0 < Module.finrank K Γ((m • B - J₀).sheaf, ⊤) := by exact_mod_cast hreal
  obtain ⟨s', hs'⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact ⟨m, hm1, s', hs'⟩

end Smooth

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationGeneration
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.CartierSectionNonvanishingOpen
public import MixedFujita.KltPairs
public import MixedFujita.AmpleEffectiveComparison
public import MixedFujita.CartierNefPullback

/-!
Section 6 of the manuscript on a klt pair (steps 12 and 15): from the data of the minimizer on a
simple normal crossing model of the pair and Kawamata–Viehweg vanishing as a hypothesis, the
Cartier divisor P is generated at a closed point.

Let (Y, B) be a klt pair on a normal variety Y, given by D = d(K_Y + B) with effective boundary,
and P a Cartier divisor with d P − D ample. Let s_1, …, s_N be nonzero sections of j(d P − D)
and π : X → Y a proper birational morphism from a smooth proper X with a simple normal crossing
family supporting the crepant boundary of X and the pullbacks of the zero divisors of the s_i.
The hypotheses of the statement of section 6 on X follow from the data on Y:

* the crepant boundary of X has coefficients smaller than d (klt) and is nonnegative at the prime
  divisors which are not exceptional over Y (effective boundary);
* A_X = π*(d P − D) is big, the sections of its multiples are finite-dimensional, and the
  multiples of m₀ A_X are globally generated when those of m₀ (d P − D) are;
* the pullbacks of the zero divisors are effective and linearly equivalent to j A_X.

Hence the data of the minimizer over a closed point x of Y give a global section of P with unit
local coefficient at x; a Cartier divisor generated at all closed points of a quasi-compact
scheme is globally generated.

The statement is proved for a decomposition d P − D = L + N with sections of multiples of L, from
a vanishing hypothesis for divisors "nef and big plus a multiple of the pullback of N". For N = 0
this is the Kawamata–Viehweg statement (the case of K-NF); for N nef on a scheme with an ample
divisor it is the sum form (the case of S-NF, where the pair is a smooth variety with zero
boundary and P = K_X + A + N). On a scheme with an ample divisor the sections of every Cartier
divisor are finite-dimensional.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

section Ample

variable {K : Type u} [Field K] [Infinite K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The sections of every multiple of an ample divisor are finite-dimensional. -/
theorem cartierIsAmpleProj_finiteDimensional_nsmul {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {A : CartierDivisor Y} (hA : CartierIsAmpleProj K A) (D : ℕ) :
    FiniteDimensional K Γ((D • A).sheaf, ⊤) := by
  obtain ⟨m, hm, v, e, _, he, g, hg, hggen, f, hmA⟩ := hA
  by_cases h0 : ∃ σ : Γ((D • A).sheaf, ⊤), σ ≠ 0
  · obtain ⟨σ, hσ⟩ := h0
    have hJ : FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
      projectiveHyperplaneSections_finiteDimensional_integral e g hg hggen he hn hd D
    have hN : FiniteDimensional K
        Γ((D • projectiveHyperplaneCartier e g hg hggen +
          principalCartierDivisor Y (f ^ D)).sheaf, ⊤) :=
      (cartierPrincipalShiftEquiv (K := K) _ (f ^ D)).symm.finiteDimensional
    have hdiv : D • projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y (f ^ D) =
        D • A + (m - 1) • (D • A) := by
      rw [principalCartierDivisor_power, ← nsmul_add, ← hmA]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, nsmul_left_comm, succ_nsmul']
    exact finiteDimensional_of_eq_add_of_section (K := K) (D • A) ((m - 1) • (D • A)) _ hdiv
      (cartierSectionPower (D • A) σ (m - 1)) (cartierSectionPower_ne_zero (D • A) σ hσ (m - 1))
      hN
  · have hall : ∀ σ : Γ((D • A).sheaf, ⊤), σ = 0 := fun σ => by
      by_contra h
      exact h0 ⟨σ, h⟩
    have : Subsingleton Γ((D • A).sheaf, ⊤) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact Module.Finite.of_finite

/-- On an integral scheme of dimension at least one over an infinite field with an ample divisor,
the sections of every Cartier divisor are finite-dimensional: the divisor is dominated, up to
linear equivalence, by a multiple of the ample divisor. -/
theorem cartier_finiteDimensional_sections_of_ample {d : ℕ} (hn : topologicalKrullDim Y = d)
    (hd : 1 ≤ d) {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) (D : CartierDivisor Y) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_effective_comparison hH D
  obtain ⟨f, hf⟩ := hj₀ j₀ le_rfl
  obtain ⟨t, ht⟩ := exists_section_ne_zero_of_isEffective _ hf
  have hJ := cartierIsAmpleProj_finiteDimensional_nsmul hn hd hH j₀
  have hN : FiniteDimensional K Γ((j₀ • H + principalCartierDivisor Y f).sheaf, ⊤) :=
    (cartierPrincipalShiftEquiv (K := K) (j₀ • H) f).symm.finiteDimensional
  exact finiteDimensional_of_eq_add_of_section (K := K) D
    (j₀ • H - D + principalCartierDivisor Y f) _ (by abel) t ht hN

end Ample

section Generation

variable {Y : Scheme.{u}} [IsIntegral Y]

/-- A rational function in the sections of P whose product with a local equation at x is a unit
of the local ring gives a section with unit local coefficient at x. -/
theorem isUnit_cartierLocalCoefficient_sectionMk (P : CartierDivisor Y) (x : Y)
    (g : Y.functionField) (hg : (rationalFunctionsEquiv (X := Y) ⊤).symm g ∈ P.sections ⊤)
    (f : Y.functionFieldˣ) (hf : P.IsLocalEquationAt x f) (u : (Y.presheaf.stalk x)ˣ)
    (hu : algebraMap (Y.presheaf.stalk x) Y.functionField u = f * g) :
    IsUnit (cartierLocalCoefficient P x f hf (CartierDivisor.sectionMk _ hg)) := by
  have h := cartierLocalCoefficient_image P x f hf (CartierDivisor.sectionMk _ hg)
  rw [cartierSectionRational_sectionMk P g hg, ← hu] at h
  rw [IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField h]
  exact u.isUnit

/-- On a quasi-compact scheme a Cartier divisor generated by global sections at every closed
point is globally generated. -/
theorem cartierIsGloballyGenerated_of_forall_isClosed [CompactSpace Y] (P : CartierDivisor Y)
    (h : ∀ x : Y, IsClosed ({x} : Set Y) →
      ∃ (f : Y.functionFieldˣ) (hf : P.IsLocalEquationAt x f) (t : Γ(P.sheaf, ⊤)),
        IsUnit (cartierLocalCoefficient P x f hf t)) :
    CartierIsGloballyGenerated P := by
  intro x
  obtain ⟨x₀, hx₀, hx₀c⟩ := (isClosed_closure (s := ({x} : Set Y))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  obtain ⟨f, hf, t, ht⟩ := h x₀ hx₀c
  refine ⟨t, ?_⟩
  have hmem₀ : x₀ ∈ cartierSectionNonvanishingOpen P t :=
    (mem_cartierSectionNonvanishingOpen P t x₀).mpr ⟨f, hf, ht⟩
  have hmem : x ∈ cartierSectionNonvanishingOpen P t := by
    by_contra hxn
    have hsub : closure ({x} : Set Y) ⊆ ((cartierSectionNonvanishingOpen P t : Set Y))ᶜ :=
      closure_minimal (Set.singleton_subset_iff.mpr hxn)
        (cartierSectionNonvanishingOpen P t).isOpen.isClosed_compl
    exact hsub hx₀ hmem₀
  exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient P t x _ _).mp hmem

end Generation

section Pair

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- At a prime divisor z of the smooth model X with bijective stalk map over its image, the
crepant boundary has the coefficient of the boundary of the pair on Y at the image:
(coefficient of D) − d · ord(f_Y g_c) for an étale chart c of Y at the image. -/
theorem crepantBoundaryCartier_coefficient_of_stalkMap_bijective (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y) (cX : EtaleChart K X n)
    (z : CodimensionOnePoint X) (hz : Order.coheight (π (z : X)) = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk (π (z : X)))]
    [IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
    (hb : Function.Bijective (π.stalkMap (z : X))) (c : EtaleChart K Y n)
    (hc : π (z : X) ∈ c.U) :
    cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) =
      cartierCoefficient D (π (z : X)) - (d : ℤ) *
        Y.ord ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField)
          (π (z : X)) := by
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K X n, (z : X) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸
      Opens.mem_top (z : X))
  have hJ0 : chartRelativeJacobianDet π cY cX ≠ 0 :=
    (isUnit_chartRelativeJacobianDet_of_bijective π hπ cY cX).ne_zero
  have hJ1 : chartRelativeJacobianDet π c c' ≠ 0 :=
    (isUnit_chartRelativeJacobianDet_of_bijective π hπ c c').ne_zero
  have hJ : (dominantFunctionFieldMap π).hom (etaleChartCanonicalEquation cY c : Y.functionField) *
      chartRelativeJacobianDet π c c' =
      chartRelativeJacobianDet π cY cX * (etaleChartCanonicalEquation cX c' : X.functionField) :=
    chartRelativeJacobianDet_change π cY c cX c'
  have hloc := (canonicalDivisor_isLocalEquationAt cX etaleCharts_cover c' hc').mul
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor (z : X)
      (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom fY *
        (isUnit_chartRelativeJacobianDet_of_bijective π hπ cY cX).unit))
  have hval : ((etaleChartCanonicalEquation cX c' *
      (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom fY *
        (isUnit_chartRelativeJacobianDet_of_bijective π hπ cY cX).unit) : X.functionFieldˣ) :
        X.functionField) =
      (dominantFunctionFieldMap π).hom
        ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField) *
        chartRelativeJacobianDet π c c' := by
    rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, Units.val_mul, map_mul]
    change (etaleChartCanonicalEquation cX c' : X.functionField) *
        ((dominantFunctionFieldMap π).hom (fY : Y.functionField) *
          chartRelativeJacobianDet π cY cX) = _
    linear_combination (-((dominantFunctionFieldMap π).hom (fY : Y.functionField))) * hJ
  have hφ0 : (dominantFunctionFieldMap π).hom
      ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  have hform : cartierCoefficient (pullbackFormDivisor π hπ cY fY cX etaleCharts_cover) (z : X) =
      Y.ord ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField)
        (π (z : X)) := by
    unfold pullbackFormDivisor
    rw [cartierCoefficient_eq_ord hloc, hval, X.ord_mul hφ0 hJ1,
      scheme_ord_pullback_of_stalkMap_bijective π z hz hb,
      chartRelativeJacobianDet_ord_zero_of_stalkMap_bijective π z hb c hc c' hc', add_zero]
  unfold crepantBoundaryCartier
  rw [cartierCoefficient_sub, cartierCoefficient_nsmul,
    cartierCoefficient_pullback_of_stalkMap_bijective π z hz hb D, hform]

end Pair

section Klt

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- Section 6 on a klt pair, with the vanishing as a hypothesis. Let (Y, B) be a klt pair with
effective boundary on the normal Y, D = d(K_Y + B), and P a Cartier divisor with d P − D = L + N,
where L is big with finite-dimensional sections of its multiples and the multiples of m₀ L are
globally generated. Let s_i be nonzero sections of j L with m₀ dividing j, and π : X → Y a smooth
proper simple normal crossing model whose family supports the crepant boundary and the pullbacks
of the zero divisors of the s_i. Then the data of the minimizer on X over the closed point x of Y
give a global section of P with unit local coefficient at x, provided H¹(T, O(Q)) = 0 on smooth
proper models ρ : T → X whenever m (Q − K_T) − Σ a_k E_k = D₁ + m' ρ*π*N with a_k < m and D₁ nef
and big. -/
theorem klt_exists_section_generating_of_minimizer_data_of_vanishing
    (hnormY : ∀ v : Y, IsIntegrallyClosed (Y.presheaf.stalk v))
    (hcov : CodimOneChartCovered n K Y)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D) (hklt : LogPairIsKlt cY fY d D)
    (P L N : CartierDivisor Y) (hLN : d • P - D = L + N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • L))
    (hLbig : CartierIsBig K L) (hLfin : ∀ k : ℕ, FiniteDimensional K Γ((k • L).sheaf, ⊤))
    (x : Y) (hx : IsClosed ({x} : Set Y))
    (j : ℕ) (hjm₀ : m₀ ∣ j) {Ns : ℕ} (s : Fin Ns → Γ((j • L).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0)
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (z : X) = 0)
    (y : X) (hy : π y = x) {c q : Fin Ns → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
      q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set Y), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
        q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
        q p → p ∈ π ⁻¹' ({x} : Set Y))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1)
    (hvan : ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T]
      [T.Over (Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
      [IsProper (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
      [ρ.IsOver (Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r' : ℕ) (ξT : Fin r' → T),
      Function.Injective ξT → (∀ k, Order.coheight (ξT k) = 1) → IsSNCFamily K n ξT →
      ∀ E : Fin r' → CartierDivisor T,
        (∀ (k : Fin r') (z : CodimensionOnePoint T),
          cartierCoefficient (E k) (z : T) = if (z : T) = ξT k then 1 else 0) →
      ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r' → ℕ, (∀ k, a k < m) →
      ∀ (D₁ : CartierDivisor T) (m' : ℕ),
        m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k =
          D₁ + m' • cartierPullback ρ (cartierPullback π N) →
        CartierIsNef K D₁ → CartierIsBig K D₁ →
        Subsingleton (Scheme.Modules.Cohomology Q.sheaf 1)) :
    ∃ (f : Y.functionFieldˣ) (hf : P.IsLocalEquationAt x f) (t : Γ(P.sheaf, ⊤)),
      IsUnit (cartierLocalCoefficient P x f hf t) := by
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z) := fun z =>
    smooth_stalk_isIntegrallyClosed (K := K) z
  have hπ' : Function.Bijective (dominantFunctionFieldMap π).hom := hπ
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  have hdim : topologicalKrullDim X = topologicalKrullDim Y :=
    (etaleChart_topologicalKrullDim cX).trans hdimY.symm
  -- the boundary of X
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D hklt cX ⟨ξ k, hξ k⟩
  have hBexc : ∀ z : CodimensionOnePoint X, Order.coheight (π (z : X)) = 1 →
      0 ≤ cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (z : X) := by
    intro z hz
    have hbij := stalkMap_bijective_of_birational_over_normal_prime hnormY π hπ' (z : X) hz
    let := hnormY (π (z : X))
    have : IsDiscreteValuationRing (Y.presheaf.stalk (π (z : X))) :=
      normal_codimensionOne_stalk_DVR (⟨π (z : X), hz⟩ : CodimensionOnePoint Y)
    have : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
      smoothOverField_codimensionOne_stalk_DVR (K := K) z
    obtain ⟨c', hc'⟩ := hcov (π (z : X)) hz
    rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective π hπ cY fY d D cX z hz hbij c'
      hc']
    have h := heff c' (π (z : X)) hc' hz
    linarith
  -- the decomposition on X and the zero divisors
  have hLNX : d • cartierPullback π P -
      (d • (smoothCanonicalDivisor cX +
        principalCartierDivisor X (crepantPullbackFormUnit π hπ cY fY cX)) +
        crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) =
      cartierPullback π L + cartierPullback π N := by
    rw [crepantBoundaryCartier_smooth_recombine, ← cartierPullback_nsmul, ← cartierPullback_sub,
      hLN, cartierPullback_add]
  have hDlin : ∀ i, ∃ h : X.functionFieldˣ,
      cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)) =
        j • cartierPullback π L + principalCartierDivisor X h := fun i =>
    ⟨_, by
      unfold cartierSectionZeroDivisor
      rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal]⟩
  have hDeff : ∀ i, (cartierPullback π
      (cartierSectionZeroDivisor (j • L) (s i) (hs i))).IsEffective := fun i =>
    cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective _ (s i) (hs i))
  -- positivity of the pullback of L
  have hLggX : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • cartierPullback π L) :=
    fun k => by
      rw [← cartierPullback_nsmul]
      exact cartierIsGloballyGenerated_cartierPullback π _ (hLgg k)
  have hLbigX : CartierIsBig K (cartierPullback π L) :=
    cartierIsBig_cartierPullback hnormY hnormX π hπ hdim hLbig
  have hLfinX : ∀ k : ℕ, FiniteDimensional K Γ((k • cartierPullback π L).sheaf, ⊤) := fun k => by
    rw [← cartierPullback_nsmul]
    exact finiteDimensional_sections_cartierPullback hnormY π hπ _ (hLfin k)
  obtain ⟨g, f, u, hg, hf, hu⟩ := exists_section_generating_of_minimizer_data_of_vanishing hnormY
    π hπ' P x hx ξ hinj hξ hsnc cX (crepantPullbackFormUnit π hπ cY fY cX) d hd
    (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) hBsupp hb hBexc
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
    hDeff hDsupp (cartierPullback π L) (cartierPullback π N) hLNX j hDlin m₀ hm₀ hjm₀ hLggX hLbigX
    hLfinX y hy hc hcq hqy hpolyΦ hcentre hbudget hvan
  exact ⟨f, hf, CartierDivisor.sectionMk _ hg,
    isUnit_cartierLocalCoefficient_sectionMk P x g hg f hf u hu⟩

/-- Section 6 on a klt pair, with Kawamata–Viehweg vanishing as a hypothesis. Let (Y, B) be a klt
pair with effective boundary on the normal Y, D = d(K_Y + B), and P a Cartier divisor with
d P − D ample and the multiples of m₀ (d P − D) globally generated. Let s_i be nonzero sections of
j (d P − D) with m₀ dividing j, and π : X → Y a smooth proper simple normal crossing model whose
family supports the crepant boundary and the pullbacks of the zero divisors of the s_i. Then the
data of the minimizer on X over the closed point x of Y give a global section of P with unit
local coefficient at x. -/
theorem klt_exists_section_generating_of_minimizer_data
    (hKV : KawamataViehwegVanishingSNC K n) (hn : 1 ≤ n)
    (hnormY : ∀ v : Y, IsIntegrallyClosed (Y.presheaf.stalk v))
    (hcov : CodimOneChartCovered n K Y)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D) (hklt : LogPairIsKlt cY fY d D)
    (P : CartierDivisor Y) (hA : CartierIsAmpleProj K (d • P - D))
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀)
    (hAgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • (d • P - D)))
    (x : Y) (hx : IsClosed ({x} : Set Y))
    (j : ℕ) (hjm₀ : m₀ ∣ j) {Ns : ℕ} (s : Fin Ns → Γ((j • (d • P - D)).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0)
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • (d • P - D)) (s i) (hs i))) (z : X) = 0)
    (y : X) (hy : π y = x) {c q : Fin Ns → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (j • (d • P - D)) (s i) (hs i)))
      q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set Y), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • (d • P - D)) (s i) (hs i)))
        q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • (d • P - D)) (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • (d • P - D)) (s i) (hs i)))
        q p → p ∈ π ⁻¹' ({x} : Set Y))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ (f : Y.functionFieldˣ) (hf : P.IsLocalEquationAt x f) (t : Γ(P.sheaf, ⊤)),
      IsUnit (cartierLocalCoefficient P x f hf t) := by
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  refine klt_exists_section_generating_of_minimizer_data_of_vanishing hnormY hcov cY fY d hd D heff
    hklt P (d • P - D) 0 (add_zero _).symm m₀ hm₀ hAgg (cartierIsAmpleProj_isBig hdimY hn hA)
    (cartierIsAmpleProj_finiteDimensional_nsmul hdimY hn hA) x hx j hjm₀ s hs π hπ cX ξ hinj hξ hsnc hBsupp hDsupp y hy hc hcq hqy hpolyΦ hcentre hbudget ?_
  intro T _ _ _ _ _ ρ _ _ cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁ m' hdec hnef hbig
  rw [cartierPullback_zero, cartierPullback_zero, smul_zero, add_zero] at hdec
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha (by rw [hdec]; exact hnef)
    (by rw [hdec]; exact hbig)

/-- Section 6 on a klt pair with a nef summand, with the sum form of Kawamata–Viehweg vanishing as
a hypothesis: d P − D = L + N with N nef, L big and the multiples of m₀ L globally generated, on a
scheme Y with an ample divisor H; the sections s_i are sections of j L. -/
theorem klt_exists_section_generating_of_minimizer_data_nef
    (hKV : KawamataViehwegVanishingSNCSum K n) (hn : 1 ≤ n)
    (hnormY : ∀ v : Y, IsIntegrallyClosed (Y.presheaf.stalk v))
    (hcov : CodimOneChartCovered n K Y)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D) (hklt : LogPairIsKlt cY fY d D)
    (P L N : CartierDivisor Y) (hLN : d • P - D = L + N)
    {H : CartierDivisor Y} (hH : CartierIsAmpleProj K H) (hN : CartierIsNef K N)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • L))
    (hLbig : CartierIsBig K L)
    (x : Y) (hx : IsClosed ({x} : Set Y))
    (j : ℕ) (hjm₀ : m₀ ∣ j) {Ns : ℕ} (s : Fin Ns → Γ((j • L).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0)
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (z : X) = 0)
    (y : X) (hy : π y = x) {c q : Fin Ns → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqy : InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
      q y)
    (hpolyΦ : ∀ p ∈ π ⁻¹' ({x} : Set Y), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
        q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
        q p → p ∈ π ⁻¹' ({x} : Set Y))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ (f : Y.functionFieldˣ) (hf : P.IsLocalEquationAt x f) (t : Γ(P.sheaf, ⊤)),
      IsUnit (cartierLocalCoefficient P x f hf t) := by
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  refine klt_exists_section_generating_of_minimizer_data_of_vanishing hnormY hcov cY fY d hd D heff
    hklt P L N hLN m₀ hm₀ hLgg hLbig
    (fun k => cartier_finiteDimensional_sections_of_ample hdimY hn hH (k • L)) x hx j hjm₀ s hs π hπ cX ξ hinj hξ hsnc hBsupp hDsupp y hy hc hcq hqy hpolyΦ hcentre hbudget ?_
  intro T _ _ _ _ _ ρ _ _ cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁ m' hdec hnef hbig
  have hNT : CartierIsNef K (cartierPullback ρ (cartierPullback π N)) := by
    rw [← cartierPullback_comp π ρ N]
    exact cartierIsNef_cartierPullback_of_ample hH hN (ρ ≫ π)
  exact hKV T cT r' ξT hinjT hξT hsncT E hEc Q m hm a ha D₁
    (m' • cartierPullback ρ (cartierPullback π N)) hdec hnef hbig (cartierIsNef_nsmul hNT m')

end Klt

end MixedFujita

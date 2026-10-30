/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBertini
public import MixedFujita.SmoothQuotientJacobian
public import MixedFujita.CartierSectionNonvanishingOpen
public import MixedFujita.EtaleChartDimension

/-!
A general member of a base-point-free linear system together with a simple normal crossing family
is simple normal crossing (step 8). The zero locus Z(s) of a global section s of a Cartier
divisor D is the closed set where its local coefficient is not a unit; on a chart with an
equation of D it is the zero locus of the coefficient g of s. A general member, outside the zeros
of one nonzero polynomial in the coefficients, cuts every coordinate stratum B_S of every chart of
a finite simple normal crossing atlas in a smooth scheme, and its coefficient avoids the finitely
many associated primes of B_S (one nonzero linear form for each, since the coefficients of the
system generate the unit ideal of B_S), so it is a non-zero-divisor on B_S. At a point x of Z(s),
let S be the coordinates of the members of the family through x; by the converse Jacobian
criterion some derivative ∂g/∂y_j with j outside S does not vanish at x. Replacing the coordinate
y_j by g and shrinking away from the members not through x gives an étale chart on which the
members through x and Z(s) are distinct coordinate hyperplanes; away from Z(s) a chart of the
family shrinks away from Z(s). Hence the family together with Z(s) is simple normal crossing.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- A family ξ together with a set Z is in simple normal crossing position on the chart c: ξ
through σ, and Z meets the chart in the zero locus of a further coordinate τ, or not at all. -/
def IsSNCChartWith (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (Z : Set X) (τ : Option (Fin n)) : Prop :=
  IsSNCChart c ξ σ ∧ (∀ i b, σ i = some b → τ ≠ some b) ∧
    Z ∩ c.U = τ.elim ∅
      (fun b => X.zeroLocus ({c.coords (MvPolynomial.X b)} : Set Γ(X, c.U)) ∩ c.U)

variable (K n) in
/-- The family ξ together with Z is simple normal crossing: every point lies in an étale chart on
which they are in simple normal crossing position. -/
def IsSNCFamilyWith {r : ℕ} (ξ : Fin r → X) (Z : Set X) : Prop :=
  ∀ x : X, ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (τ : Option (Fin n)),
    x ∈ c.U ∧ IsSNCChartWith c ξ σ Z τ

/-- Restriction to a basic open does not change the basic opens of functions at its points. -/
theorem mem_basicOpen_sectionBasicOpenRestrict {U : X.Opens} (f y : Γ(X, U)) {z : X}
    (hz : z ∈ X.basicOpen f) :
    z ∈ X.basicOpen (sectionBasicOpenRestrict (K := K) f y) ↔ z ∈ X.basicOpen y := by
  change z ∈ X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le f)).op y) ↔ _
  rw [Scheme.basicOpen_res]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- Shrinking a simple normal crossing chart around x away from a closed set not containing x. -/
theorem exists_snc_chart_avoiding {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σ) {x : X} (hx : x ∈ c.U) {C : Set X}
    (hC : IsClosed C) (hxC : x ∉ C) :
    ∃ c' : EtaleChart K X n, x ∈ c'.U ∧ (c'.U : Set X) ∩ C = ∅ ∧ IsSNCChart c' ξ σ := by
  obtain ⟨h, hle, hxh⟩ := c.isAffine.exists_basicOpen_le (V := ⟨Cᶜ, hC.isOpen_compl⟩) ⟨x, hxC⟩ hx
  refine ⟨etaleChartBasicOpen c h ⟨⟨x, hxh⟩⟩, hxh, ?_, isSNCChart_basicOpen hc h _⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hzC
  exact (hle hz) hzC

end Charts

section Sections

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

omit [X.Over (Spec (CommRingCat.of K))] in
/-- The zero locus of a global section of D: the points where its local coefficient is not a
unit. -/
noncomputable def cartierSectionZeroLocus (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) : Set X :=
  ((cartierSectionNonvanishingOpen D s : X.Opens) : Set X)ᶜ

omit [X.Over (Spec (CommRingCat.of K))] in
theorem isClosed_cartierSectionZeroLocus (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    IsClosed (cartierSectionZeroLocus D s) :=
  (cartierSectionNonvanishingOpen D s).isOpen.isClosed_compl

/-- On an open with an equation of D, the zero locus is cut by the coefficient. -/
theorem cartierSectionZeroLocus_inter (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionZeroLocus D s ∩ U =
      X.zeroLocus ({cartierGlobalOpenCoefficient (K := K) D U f hf s} : Set Γ(X, U)) ∩ U := by
  ext x
  simp only [Set.mem_inter_iff, cartierSectionZeroLocus, Set.mem_compl_iff, SetLike.mem_coe,
    Scheme.zeroLocus_singleton]
  constructor
  · rintro ⟨hx, hxU⟩
    refine ⟨fun hb => hx ?_, hxU⟩
    rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxU),
      ← cartierGlobalOpenCoefficient_germ (K := K) D U f hf x hxU]
    exact (X.mem_basicOpen _ x hxU).mp hb
  · rintro ⟨hx, hxU⟩
    refine ⟨fun hn => hx ?_, hxU⟩
    rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxU),
      ← cartierGlobalOpenCoefficient_germ (K := K) D U f hf x hxU] at hn
    exact (X.mem_basicOpen _ x hxU).mpr hn

omit [IsIntegral X] in
/-- The converse Jacobian criterion on a chart: at a point of {g = 0} on the coordinate stratum
of S, where g cuts a smooth scheme and is a non-zero-divisor, some derivative ∂g/∂y_j with j
outside S does not vanish. -/
theorem exists_coordinateDerivation_mem_basicOpen
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (S : Set (Fin n))
    (g : Γ(X, c.U))
    (hsm : Algebra.Smooth K ((Γ(X, c.U) ⧸ etaleChartStratumIdeal c S) ⧸
      Ideal.span {(Ideal.Quotient.mk (etaleChartStratumIdeal c S) g)}))
    (hreg : ∀ y : Γ(X, c.U) ⧸ etaleChartStratumIdeal c S,
      y * Ideal.Quotient.mk (etaleChartStratumIdeal c S) g = 0 → y = 0)
    (x : X) (hx : x ∈ c.U) (hS : ∀ a ∈ S, x ∉ X.basicOpen (c.coords (MvPolynomial.X a)))
    (hg : x ∉ X.basicOpen g) :
    ∃ j ∉ S, x ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j g) := by
  classical
  let I := etaleChartStratumIdeal c S
  let mx : Ideal Γ(X, c.U) :=
    Ideal.comap (X.presheaf.germ c.U x hx).hom (IsLocalRing.maximalIdeal _)
  have hmx : mx.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ b : Γ(X, c.U), b ∈ mx ↔ x ∉ X.basicOpen b := by
    intro b
    rw [X.mem_basicOpen _ x hx]
    exact IsLocalRing.mem_maximalIdeal _
  have hI : I ≤ mx := by
    change etaleChartStratumIdeal c S ≤ mx
    rw [etaleChartStratumIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact (hmem _).mpr (hS a ha)
  have hm : (mx.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hstr := etaleChart_stratum_smooth c S
  have hFS : Algebra.FormallySmooth K (Γ(X, c.U) ⧸ I) := inferInstance
  have hFS' : Algebra.FormallySmooth K ((Γ(X, c.U) ⧸ I) ⧸
      Ideal.span {(Ideal.Quotient.mk I g)}) := inferInstance
  -- the differential of g on the stratum
  have hDB : KaehlerDifferential.D K Γ(X, c.U) g = ∑ j, etaleCoordinateDerivation c.coords
      c.formallyEtale j g • KaehlerDifferential.D K Γ(X, c.U) (c.coords (MvPolynomial.X j)) := by
    conv_lhs => rw [← (etaleCoordinateBasis c.coords c.formallyEtale).sum_repr
      (KaehlerDifferential.D K Γ(X, c.U) g)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [etaleCoordinateBasis_apply, etaleCoordinateDerivation_apply]
  have hDQ : KaehlerDifferential.D K (Γ(X, c.U) ⧸ I) (Ideal.Quotient.mk I g) =
      ∑ j : {j // j ∉ S}, Ideal.Quotient.mk I
        (etaleCoordinateDerivation c.coords c.formallyEtale j g) •
          KaehlerDifferential.D K (Γ(X, c.U) ⧸ I)
            (Ideal.Quotient.mk I (c.coords (MvPolynomial.X j))) := by
    have h1 := congrArg (KaehlerDifferential.map K K Γ(X, c.U) (Γ(X, c.U) ⧸ I)) hDB
    rw [KaehlerDifferential.map_D, map_sum] at h1
    change _ = ∑ j, _ at h1
    rw [show (algebraMap Γ(X, c.U) (Γ(X, c.U) ⧸ I) g) = Ideal.Quotient.mk I g from rfl] at h1
    rw [h1, ← Fintype.sum_subtype_add_sum_subtype (fun j => j ∉ S)]
    have hzero : ∑ j : {j // ¬ (j ∉ S)}, KaehlerDifferential.map K K Γ(X, c.U) (Γ(X, c.U) ⧸ I)
        (etaleCoordinateDerivation c.coords c.formallyEtale j g •
          KaehlerDifferential.D K Γ(X, c.U) (c.coords (MvPolynomial.X j))) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      have hjI : c.coords (MvPolynomial.X j.1) ∈ I := by
        change _ ∈ etaleChartStratumIdeal c S
        rw [etaleChartStratumIdeal_eq_span]
        exact Ideal.subset_span ⟨j.1, not_not.mp j.2, rfl⟩
      rw [map_smul, KaehlerDifferential.map_D]
      change _ • KaehlerDifferential.D K (Γ(X, c.U) ⧸ I)
        (Ideal.Quotient.mk I (c.coords (MvPolynomial.X j.1))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hjI, map_zero, smul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, KaehlerDifferential.map_D]
    exact (algebraMap_smul (Γ(X, c.U) ⧸ I) _ _).symm
  obtain ⟨⟨j, hjS⟩, hj⟩ := exists_coeff_notMem_of_formallySmooth_quotient
    (Ideal.Quotient.mk I g) hreg hFS' (mx.map (Ideal.Quotient.mk I))
    (Ideal.mem_map_of_mem _ ((hmem g).mpr hg)) _ _ hDQ
  refine ⟨j, hjS, ?_⟩
  by_contra hnot
  exact hj (Ideal.mem_map_of_mem _ ((hmem _).mpr hnot))

/-- A general member of a base-point-free system cuts every coordinate stratum of every chart of
a finite family in a smooth scheme, with coefficient a non-zero-divisor on the stratum. -/
theorem cartierSections_general_transverse_regular [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (D : CartierDivisor X) {ι : Type*}
    [Fintype ι] (s : ι → Γ(D.sheaf, ⊤)) (hs : CartierSectionsBasePointFree D s) {κ : Type*}
    [Fintype κ] (c : κ → EtaleChart K X n) (f : κ → X.functionFieldˣ)
    (hf : ∀ k, rationalUnitClass X (c k).U (Additive.ofMul (f k)) = D |_ (c k).U) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      ∀ k, CartierSectionTransverseOn D (c k) (f k) (hf k) (∑ i, t i • s i) ∧
        ∀ (S : Set (Fin n)) (y : Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S),
          y * Ideal.Quotient.mk (etaleChartStratumIdeal (c k) S)
            (cartierGlobalOpenCoefficient (K := K) D (c k).U (f k) (hf k) (∑ i, t i • s i)) = 0 →
              y = 0 := by
  classical
  obtain ⟨p₀, hp₀, htrans⟩ := cartierSections_general_transverse D s hs c f hf
  have hlin : ∀ (k : κ) (S : Set (Fin n)), ∃ q : MvPolynomial ι K, q ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t q ≠ 0 →
        ∀ P ∈ associatedPrimes (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S)
            (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S),
          Ideal.Quotient.mk (etaleChartStratumIdeal (c k) S)
            (cartierGlobalOpenCoefficient (K := K) D (c k).U (f k) (hf k) (∑ i, t i • s i)) ∉ P := by
    intro k S
    let I := etaleChartStratumIdeal (c k) S
    have : Algebra.FiniteType K Γ(X, (c k).U) := sectionsBaseOpen_finiteType (c k).isAffine
    have : Algebra.FiniteType K (Γ(X, (c k).U) ⧸ I) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I)
        Ideal.Quotient.mk_surjective
    have : IsNoetherianRing (Γ(X, (c k).U) ⧸ I) := Algebra.FiniteType.isNoetherianRing K _
    have hfin := associatedPrimes.finite (Γ(X, (c k).U) ⧸ I) (Γ(X, (c k).U) ⧸ I)
    -- the composite K-linear map Γ(D) → stratum
    let coeffS : Γ(D.sheaf, ⊤) →ₗ[K] Γ(X, (c k).U) ⧸ I :=
      (Ideal.Quotient.mkₐ K I).toLinearMap ∘ₗ
        cartierGlobalOpenCoefficient (K := K) D (c k).U (f k) (hf k)
    have hspan : Ideal.span (Set.range fun i => coeffS (s i)) = ⊤ :=
      span_range_stratum_eq_top (c k) S _
        (span_range_cartierGlobalOpenCoefficient_eq_top D (c k).isAffine (f k) (hf k) s hs)
    have hP : ∀ P ∈ associatedPrimes (Γ(X, (c k).U) ⧸ I) (Γ(X, (c k).U) ⧸ I),
        ∃ ℓ : MvPolynomial ι K, ℓ ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t ℓ ≠ 0 →
          coeffS (∑ i, t i • s i) ∉ P := by
      intro P hPA
      have hPprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hPA).isPrime
      let φ : (ι → K) →ₗ[K] (Γ(X, (c k).U) ⧸ I) ⧸ P :=
        ((Ideal.Quotient.mkₐ K P).toLinearMap ∘ₗ coeffS) ∘ₗ Fintype.linearCombination K s
      have hφt : ∀ t, φ t = Ideal.Quotient.mk P (coeffS (∑ i, t i • s i)) := fun t => rfl
      have hφ : φ ≠ 0 := by
        intro h0
        apply hPprime.ne_top
        rw [eq_top_iff, ← hspan, Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        have hi := LinearMap.congr_fun h0 (Pi.single i 1)
        rw [LinearMap.zero_apply, LinearMap.comp_apply, Fintype.linearCombination_apply_single,
          one_smul] at hi
        exact Ideal.Quotient.eq_zero_iff_mem.mp hi
      obtain ⟨ℓ, hℓ, hℓφ⟩ := exists_mvPolynomial_ne_zero_of_linearMap_ne_zero φ hφ
      exact ⟨ℓ, hℓ, fun t ht hmem => hℓφ t ht (by
        rw [hφt]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem)⟩
    choose ℓ hℓ hℓP using hP
    let ℓ' : Ideal (Γ(X, (c k).U) ⧸ I) → MvPolynomial ι K := fun P =>
      if h : P ∈ associatedPrimes (Γ(X, (c k).U) ⧸ I) (Γ(X, (c k).U) ⧸ I) then ℓ P h else 1
    refine ⟨∏ P ∈ hfin.toFinset, ℓ' P, ?_, fun t ht P hP => ?_⟩
    · refine Finset.prod_ne_zero_iff.mpr fun P hP => ?_
      have hP' := hfin.mem_toFinset.mp hP
      simp only [ℓ', dif_pos hP']
      exact hℓ P hP'
    · have hP' : P ∈ hfin.toFinset := hfin.mem_toFinset.mpr hP
      rw [map_prod] at ht
      have h1 := (Finset.prod_ne_zero_iff.mp ht) P hP'
      have hℓ' : ℓ' P = ℓ P hP := dif_pos hP
      rw [hℓ'] at h1
      exact hℓP P hP t h1
  choose q hq hqP using hlin
  refine ⟨p₀ * ∏ k, ∏ S, q k S, ?_, fun t ht k => ⟨?_, fun S y hy => ?_⟩⟩
  · exact mul_ne_zero hp₀ (Finset.prod_ne_zero_iff.mpr fun k _ =>
      Finset.prod_ne_zero_iff.mpr fun S _ => hq k S)
  · rw [map_mul] at ht
    exact htrans t (left_ne_zero_of_mul ht) k
  · rw [map_mul, map_prod] at ht
    have h1 := (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul ht)) k (Finset.mem_univ k)
    rw [map_prod] at h1
    have h2 := (Finset.prod_ne_zero_iff.mp h1) S (Finset.mem_univ S)
    have : Algebra.FiniteType K Γ(X, (c k).U) := sectionsBaseOpen_finiteType (c k).isAffine
    have : Algebra.FiniteType K (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S) :=
      Algebra.FiniteType.of_surjective
        (Ideal.Quotient.mkₐ K (etaleChartStratumIdeal (c k) S)) Ideal.Quotient.mk_surjective
    have : IsNoetherianRing (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S) :=
      Algebra.FiniteType.isNoetherianRing K _
    exact mul_eq_zero_of_notMem_associatedPrimes (hqP k S t h2) y hy

/-- At a point of the zero locus in a chart of the atlas, the family and the zero locus are in
simple normal crossing position on a smaller chart. -/
theorem exists_sncChartWith_of_mem_zeroLocus
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (hf : rationalUnitClass X c.U (Additive.ofMul f) = D |_ c.U)
    {r : ℕ} {ξ : Fin r → X} {σ : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σ)
    (s : Γ(D.sheaf, ⊤)) (htr : CartierSectionTransverseOn D c f hf s)
    (hreg : ∀ (S : Set (Fin n)) (y : Γ(X, c.U) ⧸ etaleChartStratumIdeal c S),
      y * Ideal.Quotient.mk (etaleChartStratumIdeal c S)
        (cartierGlobalOpenCoefficient (K := K) D c.U f hf s) = 0 → y = 0)
    {x : X} (hx : x ∈ c.U) (hxZ : x ∈ cartierSectionZeroLocus D s) :
    ∃ (c'' : EtaleChart K X n) (σ'' : Fin r → Option (Fin n)) (τ : Option (Fin n)),
      x ∈ c''.U ∧ IsSNCChartWith c'' ξ σ'' (cartierSectionZeroLocus D s) τ := by
  classical
  set g := cartierGlobalOpenCoefficient (K := K) D c.U f hf s with hgdef
  let S : Set (Fin n) := {a | ∃ i, σ i = some a ∧ x ∈ closure ({ξ i} : Set X)}
  -- the members through x have coordinates in S, which vanish at x
  have hmemS : ∀ i a, σ i = some a → ∀ z ∈ c.U,
      (z ∈ closure ({ξ i} : Set X) ↔ z ∉ X.basicOpen (c.coords (MvPolynomial.X a))) := by
    intro i a hia z hz
    have h := hc.2 i
    rw [hia] at h
    change closure ({ξ i} : Set X) ∩ c.U =
      X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U at h
    rw [Scheme.zeroLocus_singleton] at h
    constructor
    · intro hzi
      have hm : z ∈ closure ({ξ i} : Set X) ∩ c.U := ⟨hzi, hz⟩
      rw [h] at hm
      exact hm.1
    · intro hzb
      have hm : z ∈ ((X.basicOpen (c.coords (MvPolynomial.X a)) : Set X))ᶜ ∩ c.U := ⟨hzb, hz⟩
      rw [← h] at hm
      exact hm.1
  have hnone : ∀ i, σ i = none → ∀ z ∈ c.U, z ∉ closure ({ξ i} : Set X) := by
    intro i hi z hz hzi
    have h := hc.2 i
    rw [hi] at h
    change closure ({ξ i} : Set X) ∩ c.U = ∅ at h
    have hm : z ∈ closure ({ξ i} : Set X) ∩ c.U := ⟨hzi, hz⟩
    rw [h] at hm
    exact hm
  have hS : ∀ a ∈ S, x ∉ X.basicOpen (c.coords (MvPolynomial.X a)) := by
    rintro a ⟨i, hia, hxi⟩
    exact (hmemS i a hia x hx).mp hxi
  have hZg : ∀ z ∈ c.U, (z ∈ cartierSectionZeroLocus D s ↔ z ∉ X.basicOpen g) := by
    intro z hz
    have h := cartierSectionZeroLocus_inter (K := K) D c.U f hf s
    rw [Scheme.zeroLocus_singleton, ← hgdef] at h
    constructor
    · intro hzZ
      have hm : z ∈ cartierSectionZeroLocus D s ∩ c.U := ⟨hzZ, hz⟩
      rw [h] at hm
      exact hm.1
    · intro hzb
      have hm : z ∈ ((X.basicOpen g : Set X))ᶜ ∩ c.U := ⟨hzb, hz⟩
      rw [← h] at hm
      exact hm.1
  have hgx : x ∉ X.basicOpen g := (hZg x hx).mp hxZ
  obtain ⟨j, hjS, hxj⟩ :=
    exists_coordinateDerivation_mem_basicOpen c S g (htr S) (hreg S) x hx hS hgx
  let c' := etaleChartReplace c j g ⟨⟨x, hxj⟩⟩
  -- the members not through x
  let C : Set X := ⋃ i ∈ {i | x ∉ closure ({ξ i} : Set X)}, closure ({ξ i} : Set X)
  have hC : IsClosed C :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun i _ => isClosed_closure
  have hxC : x ∉ C := by
    simp only [C, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro i hi hxi
    exact hi hxi
  obtain ⟨h, hle, hxh⟩ :=
    c'.isAffine.exists_basicOpen_le (V := ⟨Cᶜ, hC.isOpen_compl⟩) ⟨x, hxC⟩ hxj
  let c'' := etaleChartBasicOpen c' h ⟨⟨x, hxh⟩⟩
  have hU'' : ∀ z ∈ c''.U, z ∈ c'.U ∧ z ∈ c.U ∧ z ∉ C := fun z hz =>
    ⟨X.basicOpen_le h hz, X.basicOpen_le _ (X.basicOpen_le h hz), hle hz⟩
  -- coordinates of c'' at its points
  have hcoord_ne : ∀ a, a ≠ j → ∀ z ∈ c''.U,
      (z ∈ X.basicOpen (c''.coords (MvPolynomial.X a)) ↔
        z ∈ X.basicOpen (c.coords (MvPolynomial.X a))) := by
    intro a haj z hz
    change z ∈ X.basicOpen (sectionBasicOpenRestrict (K := K) h
      (c'.coords (MvPolynomial.X a))) ↔ _
    rw [mem_basicOpen_sectionBasicOpenRestrict h _ hz,
      etaleChartReplace_coords_ne c j g _ haj,
      mem_basicOpen_sectionBasicOpenRestrict _ _ (hU'' z hz).1]
  have hcoord_self : ∀ z ∈ c''.U,
      (z ∈ X.basicOpen (c''.coords (MvPolynomial.X j)) ↔ z ∈ X.basicOpen g) := by
    intro z hz
    change z ∈ X.basicOpen (sectionBasicOpenRestrict (K := K) h
      (c'.coords (MvPolynomial.X j))) ↔ _
    rw [mem_basicOpen_sectionBasicOpenRestrict h _ hz, etaleChartReplace_coords_self,
      mem_basicOpen_sectionBasicOpenRestrict _ _ (hU'' z hz).1]
  have hσS : ∀ i a, (if x ∈ closure ({ξ i} : Set X) then σ i else none) = some a →
      σ i = some a ∧ a ∈ S := by
    intro i a hia
    by_cases hxi : x ∈ closure ({ξ i} : Set X)
    · rw [if_pos hxi] at hia
      exact ⟨hia, i, hia, hxi⟩
    · rw [if_neg hxi] at hia
      exact absurd hia (by simp)
  refine ⟨c'', fun i => if x ∈ closure ({ξ i} : Set X) then σ i else none, some j, hxh,
    ⟨⟨fun i i' a hi hi' => hc.1 i i' a (hσS i a hi).1 (hσS i' a hi').1, fun i => ?_⟩,
      fun i b hib => ?_, ?_⟩⟩
  · -- the members of the family
    by_cases hxi : x ∈ closure ({ξ i} : Set X)
    · have hσi : ∃ a, σ i = some a := by
        cases hσ : σ i with
        | none => exact absurd hxi (hnone i hσ x hx)
        | some a => exact ⟨a, rfl⟩
      obtain ⟨a, hia⟩ := hσi
      have haj : a ≠ j := fun haj => hjS (haj ▸ ⟨i, hia, hxi⟩)
      simp only [if_pos hxi, hia]
      change closure ({ξ i} : Set X) ∩ c''.U =
        X.zeroLocus ({c''.coords (MvPolynomial.X a)} : Set Γ(X, c''.U)) ∩ c''.U
      rw [Scheme.zeroLocus_singleton]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨hzi, hz⟩
        exact ⟨(hcoord_ne a haj z hz).not.mpr ((hmemS i a hia z (hU'' z hz).2.1).mp hzi), hz⟩
      · rintro ⟨hzb, hz⟩
        exact ⟨(hmemS i a hia z (hU'' z hz).2.1).mpr ((hcoord_ne a haj z hz).not.mp hzb), hz⟩
    · simp only [if_neg hxi]
      change closure ({ξ i} : Set X) ∩ c''.U = ∅
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hzi hz
      exact (hU'' z hz).2.2 (Set.mem_biUnion (x := i) hxi hzi)
  · -- the coordinate of the zero locus is not one of the family
    intro hjb
    have hjb' : j = b := Option.some_injective _ hjb
    exact hjS (hjb' ▸ (hσS i b hib).2)
  · -- the zero locus
    change cartierSectionZeroLocus D s ∩ c''.U =
      X.zeroLocus ({c''.coords (MvPolynomial.X j)} : Set Γ(X, c''.U)) ∩ c''.U
    rw [Scheme.zeroLocus_singleton]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hzZ, hz⟩
      exact ⟨(hcoord_self z hz).not.mpr ((hZg z (hU'' z hz).2.1).mp hzZ), hz⟩
    · rintro ⟨hzb, hz⟩
      exact ⟨(hZg z (hU'' z hz).2.1).mpr ((hcoord_self z hz).not.mp hzb), hz⟩

/-- Bertini with simple normal crossings: on a quasi-compact scheme with a simple normal crossing
family, in characteristic zero, for sections of D without common zeros there is a nonzero
polynomial p in the coefficients, with points where it does not vanish, such that for every
member Σ t_i s_i with p(t) ≠ 0 the family together with its zero locus is simple normal
crossing. -/
theorem cartierSections_general_sncFamilyWith_zeroLocus [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {r : ℕ} (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        IsSNCFamilyWith K n ξ (cartierSectionZeroLocus D (∑ i, t i • s i)) := by
  obtain ⟨T, c, σ, f, hf, hcover, hsnc⟩ := exists_finite_snc_atlas D ξ hξ
  obtain ⟨p, hp, hgen⟩ := cartierSections_general_transverse_regular D s hs c f hf
  refine ⟨p, hp, ?_, fun t ht x => ?_⟩
  · by_contra h
    push Not at h
    apply hp
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    exact h t
  · by_cases hxZ : x ∈ cartierSectionZeroLocus D (∑ i, t i • s i)
    · obtain ⟨k, hxk⟩ := hcover x
      exact exists_sncChartWith_of_mem_zeroLocus D (c k) (f k) (hf k) (hsnc k) _
        (hgen t ht k).1 (hgen t ht k).2 hxk hxZ
    · obtain ⟨c₀, σ₀, hx₀, hc₀⟩ := hξ x
      obtain ⟨c', hxc', hdisj, hc'⟩ := exists_snc_chart_avoiding hc₀ hx₀
        (isClosed_cartierSectionZeroLocus D _) hxZ
      refine ⟨c', σ₀, none, hxc', hc', fun i b _ => by simp, ?_⟩
      change cartierSectionZeroLocus D (∑ i, t i • s i) ∩ c'.U = ∅
      rw [Set.inter_comm]
      exact hdisj

end Sections

end MixedFujita

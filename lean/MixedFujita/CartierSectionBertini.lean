/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartStrataBertini
public import MixedFujita.CartierOpenCoefficient
public import MixedFujita.JacobianCriterionCharts

/-!
Bertini for sections of Cartier divisors and simple normal crossings (step 8). On an open U where
a Cartier divisor D has an equation f, the global sections of D have coefficients in the functions
on U, K-linear and with the local coefficients as germs; the zero scheme of a section on U is cut
by its coefficient. Sections without common zeros have coefficients generating the unit ideal on
every affine U (the basic opens of the coefficients cover U). Étale charts restrict to basic opens.
A finite family of prime divisors (points ξ_i) is in simple normal crossing position on an étale
chart if the closure of each ξ_i meets the chart in the zero locus of one coordinate, or not at
all, with distinct coordinates for distinct members, and it is a simple normal crossing family if
every point has such a chart. On a quasi-compact scheme finitely many such charts, on each of which
D has an equation, cover the scheme, and in characteristic zero a general member of a family of
sections without common zeros, outside the zeros of one nonzero polynomial in the coefficients,
meets every coordinate stratum of every chart of the atlas in a smooth scheme: its zero scheme is
smooth and transverse to the simple normal crossing family.
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

/-- The restriction of an étale chart to a nonempty basic open. -/
noncomputable def etaleChartBasicOpen (c : EtaleChart K X n) (g : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen g)) : EtaleChart K X n where
  U := X.basicOpen g
  isAffine := c.isAffine.basicOpen g
  nonempty := hne
  coords := (sectionBasicOpenRestrict (K := K) g).comp c.coords
  formallyEtale := formallyEtale_comp _ (sectionBasicOpenRestrict_formallyEtale (K := K) c.isAffine g)
    _ c.formallyEtale

/-- A finite family of prime divisors, given by points ξ_i, is in simple normal crossing position
on the étale chart c through σ: the closure of ξ_i meets the chart in the zero locus of the
coordinate σ_i, or not at all when σ_i = none, and distinct members have distinct coordinates. -/
def IsSNCChart (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin n)) :
    Prop :=
  (∀ i j a, σ i = some a → σ j = some a → i = j) ∧
    ∀ i, closure ({ξ i} : Set X) ∩ c.U = (σ i).elim ∅
      (fun a => X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U)

variable (K n) in
/-- Simple normal crossings: every point lies in an étale chart with n coordinates on which the
family is in simple normal crossing position. -/
def IsSNCFamily {r : ℕ} (ξ : Fin r → X) : Prop :=
  ∀ x : X, ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)), x ∈ c.U ∧ IsSNCChart c ξ σ

/-- Simple normal crossing position survives restriction to a basic open. -/
theorem isSNCChart_basicOpen {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (h : IsSNCChart c ξ σ) (g : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen g)) : IsSNCChart (etaleChartBasicOpen c g hne) ξ σ := by
  refine ⟨h.1, fun i => ?_⟩
  have hle : ((X.basicOpen g : X.Opens) : Set X) ⊆ c.U := X.basicOpen_le g
  have hi := h.2 i
  change closure ({ξ i} : Set X) ∩ X.basicOpen g = (σ i).elim ∅ (fun a => X.zeroLocus
    ({sectionBasicOpenRestrict (K := K) g (c.coords (MvPolynomial.X a))} :
      Set Γ(X, X.basicOpen g)) ∩ X.basicOpen g)
  have hsub : closure ({ξ i} : Set X) ∩ X.basicOpen g =
      (closure ({ξ i} : Set X) ∩ c.U) ∩ X.basicOpen g := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle]
  rw [hsub, hi]
  cases σ i with
  | none => simp
  | some a =>
    simp only [Option.elim_some]
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle, Scheme.zeroLocus_singleton,
      Scheme.zeroLocus_singleton]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hx, hg⟩
      refine ⟨fun hx' => hx ?_, hg⟩
      change x ∈ X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le g)).op
        (c.coords (MvPolynomial.X a))) at hx'
      rw [Scheme.basicOpen_res] at hx'
      exact hx'.2
    · rintro ⟨hx, hg⟩
      refine ⟨fun hx' => hx ?_, hg⟩
      change x ∈ X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le g)).op
        (c.coords (MvPolynomial.X a)))
      rw [Scheme.basicOpen_res]
      exact ⟨hg, hx'⟩

end Charts

section Sections

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- The coefficients on an open U of the global sections of D, for an equation f of D on U, as a
K-linear map to the functions on U. -/
noncomputable def cartierGlobalOpenCoefficient (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    Γ(D.sheaf, ⊤) →ₗ[K] Γ(X, U) where
  toFun s := cartierOpenCoefficient D U f hf U le_rfl
    (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' k s := by
    rw [Scheme.Modules.base_smul_globalSections, Scheme.Modules.map_smul D.sheaf
      (homOfLE le_top : U ⟶ ⊤), map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
    congr 1
    change _ = ((X.baseRingToStructurePresheaf K).app (op U)).hom k
    rw [Scheme.baseRingToStructurePresheaf_app]
    rfl

/-- The germs of the coefficients are the local coefficients. -/
theorem cartierGlobalOpenCoefficient_germ (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) (x : X)
    (hx : x ∈ U) (s : Γ(D.sheaf, ⊤)) :
    X.presheaf.germ U x hx (cartierGlobalOpenCoefficient (K := K) D U f hf s) =
      cartierLocalCoefficient D x f
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) s :=
  cartierOpenCoefficient_germ_global D U f hf x hx s

omit [X.Over (Spec (CommRingCat.of K))] in
/-- A unit local coefficient stays a unit under a change of local equation. -/
theorem isUnit_cartierLocalCoefficient_iff (D : CartierDivisor X) (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) (s : Γ(D.sheaf, ⊤)) :
    IsUnit (cartierLocalCoefficient D x f hf s) ↔ IsUnit (cartierLocalCoefficient D x g hg s) := by
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x f g hf hg
  rw [hv s]
  exact Units.isUnit_units_mul v _

/-- A family of global sections of D without common zeros: at every point some section has a unit
local coefficient (for the chosen local equation, equivalently for every one). -/
def CartierSectionsBasePointFree (D : CartierDivisor X) {ι : Type*} (s : ι → Γ(D.sheaf, ⊤)) :
    Prop :=
  ∀ x : X, ∃ i, IsUnit (cartierLocalCoefficient D x (Classical.choose (D.exists_isLocalEquationAt x))
    (Classical.choose_spec (D.exists_isLocalEquationAt x)) (s i))

/-- On an affine open, the coefficients of sections without common zeros generate the unit
ideal. -/
theorem span_range_cartierGlobalOpenCoefficient_eq_top (D : CartierDivisor X) {U : X.Opens}
    [Nonempty U] (hU : IsAffineOpen U) (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) {ι : Type*}
    (s : ι → Γ(D.sheaf, ⊤)) (hs : CartierSectionsBasePointFree D s) :
    Ideal.span (Set.range fun i => cartierGlobalOpenCoefficient (K := K) D U f hf (s i)) = ⊤ := by
  rw [← hU.iSup_basicOpen_eq_self_iff]
  apply le_antisymm
  · exact iSup_le fun g => X.basicOpen_le g.1
  · intro x hx
    obtain ⟨i, hi⟩ := hs x
    have hi' := (isUnit_cartierLocalCoefficient_iff D x _ f _
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) (s i)).mp hi
    rw [← cartierGlobalOpenCoefficient_germ (K := K) D U f hf x hx] at hi'
    have hmem : x ∈ X.basicOpen (cartierGlobalOpenCoefficient (K := K) D U f hf (s i)) :=
      (X.mem_basicOpen _ x hx).mpr hi'
    exact Opens.mem_iSup.mpr ⟨⟨_, i, rfl⟩, hmem⟩

/-- The coefficient of a linear combination is the specialized section of the coefficients. -/
theorem cartierGlobalOpenCoefficient_sum_smul (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) {ι : Type*}
    [Fintype ι] (s : ι → Γ(D.sheaf, ⊤)) (t : ι → K) :
    cartierGlobalOpenCoefficient (K := K) D U f hf (∑ i, t i • s i) =
      OAI.MaximalSeshadri.LinearBertini.specializedSection
        (fun i => cartierGlobalOpenCoefficient (K := K) D U f hf (s i)) t := by
  rw [map_sum, OAI.MaximalSeshadri.LinearBertini.specializedSection]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Algebra.smul_def]

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] in
theorem specializedSection_quotient_mk {R : Type*} [CommRing R] [Algebra K R] (I : Ideal R)
    {ι : Type*} [Fintype ι] (v : ι → R) (t : ι → K) :
    OAI.MaximalSeshadri.LinearBertini.specializedSection (fun i => Ideal.Quotient.mk I (v i)) t =
      Ideal.Quotient.mk I (OAI.MaximalSeshadri.LinearBertini.specializedSection v t) := by
  simp only [OAI.MaximalSeshadri.LinearBertini.specializedSection, map_sum, map_mul,
    Ideal.Quotient.mk_algebraMap]

/-- The section s of D meets every coordinate stratum of the chart c transversally: for an
equation f of D on the chart, every coordinate stratum cut by the coefficient of s is smooth over
K. The empty stratum says that the zero scheme of s on the chart is smooth. -/
def CartierSectionTransverseOn (D : CartierDivisor X) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (hf : rationalUnitClass X c.U (Additive.ofMul f) = D |_ c.U)
    (s : Γ(D.sheaf, ⊤)) : Prop :=
  ∀ S : Set (Fin n), Algebra.Smooth K ((Γ(X, c.U) ⧸ etaleChartStratumIdeal c S) ⧸
    Ideal.span {(Ideal.Quotient.mk (etaleChartStratumIdeal c S)
      (cartierGlobalOpenCoefficient (K := K) D c.U f hf s))})

/-- Bertini for sections on finitely many charts: in characteristic zero, for sections without
common zeros, there is a nonzero polynomial p in the coefficients such that every member Σ t_i s_i
with p(t) ≠ 0 meets every coordinate stratum of every chart transversally. -/
theorem cartierSections_general_transverse [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (D : CartierDivisor X) {ι : Type*}
    [Fintype ι] (s : ι → Γ(D.sheaf, ⊤)) (hs : CartierSectionsBasePointFree D s) {κ : Type*}
    [Fintype κ] (c : κ → EtaleChart K X n) (f : κ → X.functionFieldˣ)
    (hf : ∀ k, rationalUnitClass X (c k).U (Additive.ofMul (f k)) = D |_ (c k).U) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      ∀ k, CartierSectionTransverseOn D (c k) (f k) (hf k) (∑ i, t i • s i) := by
  classical
  have hpoly : ∀ (k : κ) (S : Set (Fin n)), ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        Algebra.Smooth K ((Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S) ⧸ Ideal.span
          ({(OAI.MaximalSeshadri.LinearBertini.specializedSection
            (fun i => Ideal.Quotient.mk (etaleChartStratumIdeal (c k) S)
              (cartierGlobalOpenCoefficient (K := K) D (c k).U (f k) (hf k) (s i))) t)} :
            Set (Γ(X, (c k).U) ⧸ etaleChartStratumIdeal (c k) S))) := by
    intro k S
    have := etaleChart_stratum_smooth (c k) S
    exact OAI.MaximalSeshadri.LinearBertini.affine_bertini _
      (span_range_stratum_eq_top (c k) S _
        (span_range_cartierGlobalOpenCoefficient_eq_top D (c k).isAffine (f k) (hf k) s hs))
  choose p hp hsmooth using hpoly
  refine ⟨∏ k, ∏ S, p k S, ?_, fun t ht k S => ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      Finset.prod_ne_zero_iff.mpr fun S _ => hp k S
  · have hkS : MvPolynomial.aeval t (p k S) ≠ 0 := by
      rw [map_prod] at ht
      have h1 := (Finset.prod_ne_zero_iff.mp ht) k (Finset.mem_univ k)
      rw [map_prod] at h1
      exact (Finset.prod_ne_zero_iff.mp h1) S (Finset.mem_univ S)
    have h := hsmooth k S t hkS
    rw [specializedSection_quotient_mk, ← cartierGlobalOpenCoefficient_sum_smul] at h
    exact h

/-- On a quasi-compact scheme with a simple normal crossing family, finitely many charts in simple
normal crossing position, on each of which D has an equation, cover the scheme. -/
theorem exists_finite_snc_atlas [CompactSpace X] (D : CartierDivisor X) {r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) :
    ∃ (T : Finset X) (c : T → EtaleChart K X n) (σ : T → Fin r → Option (Fin n))
      (f : T → X.functionFieldˣ)
      (_ : ∀ k, rationalUnitClass X (c k).U (Additive.ofMul (f k)) = D |_ (c k).U),
      (∀ x, ∃ k, x ∈ (c k).U) ∧ ∀ k, IsSNCChart (c k) ξ (σ k) := by
  classical
  have hloc : ∀ x : X, ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n))
      (f : X.functionFieldˣ)
      (hf : rationalUnitClass X c.U (Additive.ofMul f) = D |_ c.U),
      x ∈ c.U ∧ IsSNCChart c ξ σ := by
    intro x
    obtain ⟨c, σ, hxc, hc⟩ := hξ x
    obtain ⟨f, hfx⟩ := D.exists_isLocalEquationAt x
    obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hfx
    obtain ⟨g, hgV, hxg⟩ := c.isAffine.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hxc
    have hne : Nonempty (X.basicOpen g) := ⟨⟨x, hxg⟩⟩
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    exact ⟨etaleChartBasicOpen c g hne, σ, f,
      CartierDivisor.rationalUnitClass_eq_of_le hgV hV, hxg, isSNCChart_basicOpen hc g hne⟩
  choose c σ f hf hx hsnc using hloc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => ((c x).U : Set X))
    (fun x => (c x).U.isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨T, fun k => c k, fun k => σ k, fun k => f k, fun k => hf k, fun x => ?_,
    fun k => hsnc k⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hxy⟩

/-- Bertini with simple normal crossings: on a quasi-compact scheme with a simple normal crossing
family, in characteristic zero, there are a finite atlas of charts in simple normal crossing
position with equations of D and a nonzero polynomial p in the coefficients such that for sections
without common zeros every member Σ t_i s_i with p(t) ≠ 0 has smooth zero scheme transverse to the
family on every chart of the atlas; over K such t exist. -/
theorem cartierSections_general_snc_transverse [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {r : ℕ} (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) :
    ∃ (T : Finset X) (c : T → EtaleChart K X n) (σ : T → Fin r → Option (Fin n))
      (f : T → X.functionFieldˣ)
      (hf : ∀ k, rationalUnitClass X (c k).U (Additive.ofMul (f k)) = D |_ (c k).U),
      (∀ x, ∃ k, x ∈ (c k).U) ∧ (∀ k, IsSNCChart (c k) ξ (σ k)) ∧
      ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
        ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
          ∀ k, CartierSectionTransverseOn D (c k) (f k) (hf k) (∑ i, t i • s i) := by
  obtain ⟨T, c, σ, f, hf, hcover, hsnc⟩ := exists_finite_snc_atlas D ξ hξ
  obtain ⟨p, hp, htrans⟩ := cartierSections_general_transverse D s hs c f hf
  refine ⟨T, c, σ, f, hf, hcover, hsnc, p, hp, ?_, htrans⟩
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro t
  rw [map_zero]
  exact h t

end Sections

end MixedFujita

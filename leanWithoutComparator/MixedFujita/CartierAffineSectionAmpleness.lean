/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionsAffineFiniteMap
public import MixedFujita.CartierSectionNonvanishingIsomorphisms
public import MixedFujita.FiniteProjectiveCartierAmpleness
public import MixedFujita.SteinAmpleLinearComparison
public import MixedFujita.ProjectiveChartSectionExtension

/-! 元Cartier amplenessとaffine非消滅正冪切断被覆の同値。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A finite affine nonvanishing cover by ACTUAL sections proves the
ORIGINAL projective-embedding Cartier ampleness predicate. -/
theorem cartierIsAmpleProj_of_finite_affine_section_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) {ι : Type u} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hne : ∀ i, s i ≠ 0) (hcover : (⨆ i, cartierSectionNonvanishingOpen D (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (cartierSectionNonvanishingOpen D (s i))) :
    CartierIsAmpleProj K D := by
  classical
  let v := Fintype.equivFin ι
  let t : Fin (Fintype.card ι) → Γ(D.sheaf, ⊤) := fun q => s (v.symm q)
  have ht (i : ι) : t (v i) = s i := by simp only [t, Equiv.symm_apply_apply]
  have htn : ∀ i, t (v i) ≠ 0 := fun i => by rw [ht]; exact hne i
  have htc : (⨆ i : ι, cartierSectionNonvanishingOpen D (t (v i))) = ⊤ := by
    simpa only [ht] using hcover
  have hta : ∀ q, IsAffineOpen (cartierSectionNonvanishingOpen D (t q)) := fun q => haff (v.symm q)
  let e := cartierSectionsMap K D t v htn htc
  let : IsFinite e := cartierSectionsMap_isFinite_of_affine_nonvanishing K D t v htn htc hta
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show genericPoint X ∈ ⨆ i, cartierSectionNonvanishingOpen D (s i) by
    rw [hcover]; exact Opens.mem_top _)
  have hg : MvPolynomial.X (v i) ∉ (e (genericPoint X)).asHomogeneousIdeal := by
    change genericPoint X ∈ e ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card ι)) K) (MvPolynomial.X (v i))
    rw [cartierSectionsMap_preimage, ht]
    exact hi
  rw [cartierSectionsMap_hyperplane D t v htn htc i hg]
  exact cartierIsAmpleProj_add_principal
    (projectiveHyperplaneCartier_isAmpleProj_of_finite e (MvPolynomial.X (v i))
      (MvPolynomial.isHomogeneous_X K (v i)) hg (cartierSectionsMap_over D t v htn htc)) _


/-- Pointwise affine nonvanishing opens of positive Cartier powers
suffice for the ORIGINAL projective ampleness predicate. Compactness and
the product of finitely many exponents supply the common power internally. -/
theorem cartierIsAmpleProj_of_affine_power_section_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X)
    (h : ∀ x : X, ∃ (m : ℕ), 0 < m ∧ ∃ s : Γ((m • D).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (m • D) s ∧
        IsAffineOpen (cartierSectionNonvanishingOpen (m • D) s)) :
    CartierIsAmpleProj K D := by
  classical
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  choose m hm s hs haff using h
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (cartierSectionNonvanishingOpen (m x • D) (s x) : Set X))
    (fun x => (cartierSectionNonvanishingOpen (m x • D) (s x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hs x⟩)
  let B := ∏ x ∈ T, m x
  have hB : 0 < B := Finset.prod_pos (fun x _ => hm x)
  have hdiv (i : T) : m i.val ∣ B := Finset.dvd_prod_of_mem m i.property
  choose q hq using hdiv
  have hqp (i : T) : 0 < q i := by
    have h := hq i
    by_contra hn
    have hzero : q i = 0 := by omega
    rw [hzero, Nat.mul_zero] at h
    omega
  have he (i : T) : q i • (m i.val • D) = B • D := by
    rw [smul_smul]
    congr 1
    exact (Nat.mul_comm _ _).trans (hq i).symm
  let t (i : T) : Γ((B • D).sheaf, ⊤) :=
    cartierSectionCast (he i) (cartierSectionPower (m i.val • D) (s i.val) (q i))
  have ht (i : T) : cartierSectionNonvanishingOpen (B • D) (t i) =
      cartierSectionNonvanishingOpen (m i.val • D) (s i.val) := by
    dsimp only [t]
    rw [cartierSectionNonvanishingOpen_cast, cartierSectionPower_nonvanishingOpen _ _ (hqp i)]
  have htn (i : T) : t i ≠ 0 := by
    apply (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp
    rw [ht]
    exact ⟨⟨i.val, hs i.val⟩⟩
  have htc : (⨆ i : T, cartierSectionNonvanishingOpen (B • D) (t i)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT (Set.mem_univ x))
    obtain ⟨hit, hix⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, by rwa [ht]⟩
  apply cartierIsAmpleProj_of_positive_nsmul hB
  exact cartierIsAmpleProj_of_finite_affine_section_cover K (B • D) t htn htc
    (fun i => by rw [ht]; exact haff i.val)


/-- Original projective ampleness supplies actual affine nonvanishing
power-section neighborhoods, with no cohomological inputs. -/
theorem cartierIsAmpleProj_affine_power_section_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X) (hD : CartierIsAmpleProj K D) :
    ∀ x : X, ∃ (m : ℕ), 0 < m ∧ ∃ s : Γ((m • D).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (m • D) s ∧
        IsAffineOpen (cartierSectionNonvanishingOpen (m • D) s) := by
  obtain ⟨m, hm, n, e, he, hbase, g, hg, hgen, f, hEq⟩ := hD
  let := he
  let H := projectiveHyperplaneCartier e g hg hgen
  let a : H.sheaf ≅ (m • D).sheaf :=
    (cartierSheafPrincipalShiftIso H f).symm ≪≫
      eqToIso (congrArg CartierDivisor.sheaf hEq.symm)
  obtain ⟨k₀, hk₀⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
  let i₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k₀, ⟨⟨genericPoint X, hk₀⟩⟩⟩
  intro x
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  let t := projectiveCoordinateCartierSection e g hg hgen i₀ k
  refine ⟨m, by omega, Scheme.Modules.Hom.app a.hom ⊤ t, ?_, ?_⟩
  · rw [cartierSectionNonvanishingOpen_iso, projectiveCoordinateCartierSection_nonvanishing]
    exact hk
  · rw [cartierSectionNonvanishingOpen_iso, projectiveCoordinateCartierSection_nonvanishing]
    exact (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K k) one_pos).preimage e


/-- The original Cartier ampleness predicate is equivalent to the usual
affine nonvanishing positive-power criterion on a proper integral scheme. -/
theorem cartierIsAmpleProj_iff_affine_power_section_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) :
    CartierIsAmpleProj K D ↔ ∀ x : X, ∃ (m : ℕ), 0 < m ∧ ∃ s : Γ((m • D).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (m • D) s ∧
        IsAffineOpen (cartierSectionNonvanishingOpen (m • D) s) :=
  ⟨cartierIsAmpleProj_affine_power_section_cover K D, cartierIsAmpleProj_of_affine_power_section_cover K D⟩

end MixedFujita

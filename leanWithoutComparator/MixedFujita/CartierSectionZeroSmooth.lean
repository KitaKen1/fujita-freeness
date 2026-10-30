/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the files LICENSE and vendor/OpenAI-math-LICENSE.
Authors: Kenta Kitamura, OpenAI
-/
module

public import MixedFujita.CartierSectionZeroIdeal

/-!
Smoothness of the actual global zero subscheme of a general Cartier section. The affine-cover
argument generalizes `OAI.MaximalSeshadri.SchemeBertini.smooth_subscheme_of_affine_quotients`
from universe zero to arbitrary universes; the pinned vendor source is left unchanged.
The coefficient-ideal identification then connects the existing affine Bertini theorem to the
actual scheme and its intrinsic SNC charts. Irreducibility and nonemptiness are not asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A universe-polymorphic affine-cover criterion, adapted from the OpenAI Bertini implementation. -/
theorem smooth_subscheme_of_affine_quotients {K : Type u} [Field K] {α : Type u}
    (X : Scheme.{u}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, Algebra K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g) (I : X.IdealSheafData)
    [∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j))] :
    Smooth (I.subschemeι ≫ g) := by
  have hOpen (j : α) : IsOpenImmersion (I.subschemeCover.f (U j)) :=
    I.subschemeCover.map_prop (U j)
  let C : I.subscheme.OpenCover := .mkOfCovers α
    (fun j => Spec (CommRingCat.of (Γ(X, (U j).1) ⧸ I.ideal (U j))))
    (fun j => I.subschemeCover.f (U j)) (by
      intro x
      obtain ⟨j, hj⟩ := hcover (I.subschemeι x)
      have hh : x ∈ (I.subschemeCover.f (U j)).opensRange := by
        rw [I.opensRange_subschemeCover_map]
        exact hj
      obtain ⟨y, hy⟩ := hh
      exact ⟨j, y, hy⟩) (by intro j; exact hOpen j)
  let : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) C
  change ∀ j : α, Smooth (I.subschemeCover.f (U j) ≫ (I.subschemeι ≫ g))
  intro j
  rw [← Category.assoc, I.subschemeCover_map_subschemeι]
  change Smooth (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal (U j))))) ≫
    (U j).2.isoSpec.inv) ≫ (U j).1.ι ≫ g)
  rw [Category.assoc]
  rw [(U j).2.isoSpec_inv_ι_assoc g, ← hOver, ← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth.{u})).mpr
  change RingHom.Smooth ((Ideal.Quotient.mk (I.ideal (U j))).comp
    (algebraMap K Γ(X, (U j).1)))
  exact RingHom.smooth_algebraMap.mpr inferInstance

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseOpenAlgebra

/-- The canonical algebra structure on an affine chart agrees with the actual base morphism. -/
theorem affineOpen_fromSpec_comp_over (U : X.affineOpens) :
    Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, U.1))) =
      U.2.fromSpec ≫ (X ↘ Spec (CommRingCat.of K)) := by
  change Spec.map ((X.baseRingToStructurePresheaf K).app (op U.1)) = _
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, Spec.map_comp]
  simpa only [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] using
    (IsAffineOpen.SpecMap_appLE_fromSpec (X ↘ Spec (CommRingCat.of K))
      (isAffineOpen_top _) U.2 le_top)

variable [IsIntegral X] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra

include K in
/-- The actual closed immersion has precisely the intrinsic zero locus as its image. -/
theorem cartierSectionZeroSchemeι_range (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    Set.range (cartierSectionZeroSchemeι D s hs) = cartierSectionZeroLocus D s := by
  change Set.range (cartierSectionZeroIdeal D s hs).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, cartierSectionZeroIdeal_support (K := K)]

/-- Smooth coefficient quotients on an affine atlas prove smoothness of the actual zero scheme. -/
theorem cartierSectionZeroScheme_smooth_of_affine_atlas (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) {α : Type u}
    (U : α → X.affineOpens) [∀ k, Nonempty (U k).1]
    (f : α → X.functionFieldˣ)
    (hf : ∀ k, rationalUnitClass X (U k).1 (Additive.ofMul (f k)) = D |_ (U k).1)
    (hcover : ∀ x : X, ∃ k, x ∈ (U k).1)
    (hsm : ∀ k, Algebra.Smooth K (Γ(X, (U k).1) ⧸ Ideal.span
      ({cartierGlobalOpenCoefficient (K := K) D (U k).1 (f k) (hf k) s} :
        Set Γ(X, (U k).1)))) :
    Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) := by
  have hQ (k : α) : Algebra.Smooth K (Γ(X, (U k).1) ⧸
      (cartierSectionZeroIdeal D s hs).ideal (U k)) := by
    rw [cartierSectionZeroIdeal_ideal_eq_span (K := K) D s hs (U k) (f k) (hf k)]
    exact hsm k
  let : ∀ k, Algebra.Smooth K (Γ(X, (U k).1) ⧸
      (cartierSectionZeroIdeal D s hs).ideal (U k)) := hQ
  exact smooth_subscheme_of_affine_quotients X (X ↘ Spec (CommRingCat.of K))
    U hcover (fun k => affineOpen_fromSpec_comp_over (K := K) (U k))
    (cartierSectionZeroIdeal D s hs)

/-- General nonzero members define actual smooth closed zero subschemes in SNC position. -/
theorem cartierSections_general_nonzero_smooth_snc [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {r : ℕ} (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∃ hst : (∑ i, t i • s i) ≠ 0,
          Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
            (X ↘ Spec (CommRingCat.of K))) ∧
          IsSNCFamilyWith K n ξ (Set.range (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst)) := by
  classical
  obtain ⟨T, c, σ, f, hf, hcover, _⟩ := exists_finite_snc_atlas D ξ hξ
  obtain ⟨p, hp, _, hsnc⟩ := cartierSections_general_nonzero_sncFamilyWith_zeroLocus D s hs ξ hξ
  let v (k : T) (i : ι) : Γ(X, (c k).U) :=
    cartierGlobalOpenCoefficient (K := K) D (c k).U (f k) (hf k) (s i)
  have hq : ∀ k : T, ∃ q : MvPolynomial ι K, q ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t q ≠ 0 →
        Algebra.Smooth K (Γ(X, (c k).U) ⧸ Ideal.span
          ({OAI.MaximalSeshadri.LinearBertini.specializedSection (v k) t} :
            Set Γ(X, (c k).U))) := fun k =>
    etaleChart_bertini_smooth_of_span_eq_top (c k) (v k)
      (span_range_cartierGlobalOpenCoefficient_eq_top (K := K) D (c k).isAffine
        (f k) (hf k) s hs)
  choose q hq0 hqsm using hq
  refine ⟨p * ∏ k, q k, mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr fun k _ => hq0 k),
    ?_, fun t ht => ?_⟩
  · by_contra h
    push Not at h
    apply mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr fun k _ => hq0 k)
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    exact h t
  · simp only [map_mul, map_prod, mul_ne_zero_iff] at ht
    obtain ⟨hst, hSNC⟩ := hsnc t ht.1
    refine ⟨hst, ?_, ?_⟩
    · apply cartierSectionZeroScheme_smooth_of_affine_atlas D _ hst
        (fun k : T => ⟨(c k).U, (c k).isAffine⟩) f hf hcover
      intro k
      rw [cartierGlobalOpenCoefficient_sum_smul]
      exact hqsm k t (Finset.prod_ne_zero_iff.mp ht.2 k (Finset.mem_univ k))
    · rw [cartierSectionZeroSchemeι_range (K := K)]
      exact hSNC

end MixedFujita

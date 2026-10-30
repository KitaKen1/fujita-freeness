/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.DiscrepancyPrimeComparison
public import MixedFujita.BirationalPrimeLifts
public import MixedFujita.CartierSectionBertini
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.PointClosureHyperplaneEquivalence
public import MixedFujita.ProperBirationalSections
public import MixedFujita.SteinCartierSectionEquiv
public import MixedFujita.CartierBigDefinition
public import MixedFujita.SmoothProperCurveSections

/-!
Restriction of simple normal crossing models along open immersions (step 9, the open part of a
compactified model).

Let `ι : T → T̄` be an open immersion of integral schemes over a field.
* A finite family `ξ̄` of codimension-one points of `T̄` in simple normal crossing position gives
  the subfamily of the members lying in `T`, again in simple normal crossing position
  (`exists_isSNCFamily_of_isOpenImmersion`): a chart of `T̄` through `ι(x)` is shrunk to a basic
  open inside the range of `ι` and pulled back; the closure in `T` of a member is the preimage of
  its closure, and zero loci of coordinates pull back to zero loci.
* Coefficients of pulled-back Cartier divisors and of crepant boundaries of composites with `ι` at
  codimension-one points of `T` are the coefficients at the image points
  (`cartierCoefficient_cartierPullback_of_isOpenImmersion`,
  `crepantBoundaryCartier_coefficient_comp_of_stalkMap_bijective`).
* For an effective Cartier divisor `D` and a dominant morphism `ρ`, `1` is a local equation of
  `ρ^*D` at `x` exactly when it is one of `D` at `ρ(x)`: the stalk map is local
  (`cartierPullback_isLocalEquationAt_one_iff`).
* Bigness passes to the pullback along a dominant morphism of the same dimension whenever the
  sections of the multiples of the pullback are finite-dimensional, since sections pull back
  injectively (`cartierIsBig_cartierPullback_of_finiteDimensional`); this applies to a
  non-normal target.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

section Crepant

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Crepant boundaries along equal morphisms agree. -/
theorem crepantBoundaryCartier_congr_hom {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
    [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    {ρ₁ ρ₂ : T ⟶ Y} (h : ρ₁ = ρ₂) [IsDominant ρ₁] [IsDominant ρ₂]
    [ρ₁.IsOver (Spec (CommRingCat.of K))] [ρ₂.IsOver (Spec (CommRingCat.of K))]
    (h₁ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ₁))
    (h₂ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ₂))
    (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    crepantBoundaryCartier ρ₁ h₁ c₀ f₀ d D c'₀ hT =
      crepantBoundaryCartier ρ₂ h₂ c₀ f₀ d D c'₀ hT := by
  subst h
  rfl

/-- At a codimension-one point with bijective stalk map, the crepant boundary of a composite has
the coefficient of the crepant boundary of the second map at the image point. -/
theorem crepantBoundaryCartier_coefficient_comp_of_stalkMap_bijective {X T U : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsIntegral U]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [U.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian T] [IsLocallyNoetherian U]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) (σ : U ⟶ T) [IsDominant ρ] [IsDominant σ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [σ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (hσρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ ≫ ρ)))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (c' : EtaleChart K T n) (c'' : EtaleChart K U n) (t : CodimensionOnePoint U)
    (hξ : Order.coheight (σ (t : U)) = 1) (hσt : Function.Bijective (σ.stalkMap (t : U))) :
    cartierCoefficient (crepantBoundaryCartier (σ ≫ ρ) hσρ c f d D c'' etaleCharts_cover)
        (t : U) =
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D c' etaleCharts_cover)
        (σ (t : U)) := by
  rw [crepantBoundaryCartier_eq_neg_discrepancy, crepantBoundaryCartier_eq_neg_discrepancy,
    cartierCoefficient_neg, cartierCoefficient_neg]
  congr 1
  exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective ρ σ hρ hσ c f d D c' c''
    t hξ hσt

end Crepant

section Coefficients

variable {K : Type u} [Field K] {n : ℕ} {T Tb : Scheme.{u}} [IsIntegral T] [IsIntegral Tb]
  [IsLocallyNoetherian T] [IsLocallyNoetherian Tb]
  [T.Over (Spec (CommRingCat.of K))] [Tb.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K))]
  (ι : T ⟶ Tb) [IsOpenImmersion ι] [IsDominant ι]

omit [IsIntegral T] [IsIntegral Tb] [IsLocallyNoetherian T] [IsLocallyNoetherian Tb]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Tb ↘ Spec (CommRingCat.of K))] [IsDominant ι] in
/-- An open immersion preserves the coheight of points. -/
theorem coheight_eq_of_isOpenImmersion (t : T) : Order.coheight (ι t) = Order.coheight t :=
  (coheight_eq_of_stalkMap_bijective ι t (ConcreteCategory.bijective_of_isIso _)).symm

include K n in
/-- The coefficient at a codimension-one point of the pullback along an open immersion of smooth
varieties is the coefficient at the image point. -/
theorem cartierCoefficient_cartierPullback_of_isOpenImmersion (B : CartierDivisor Tb)
    (t : CodimensionOnePoint T) :
    cartierCoefficient (cartierPullback ι B) (t : T) = cartierCoefficient B (ι (t : T)) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (Tb ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hξ : Order.coheight (ι (t : T)) = 1 :=
    (coheight_eq_of_isOpenImmersion ι (t : T)).trans t.2
  let ξ : CodimensionOnePoint Tb := ⟨ι (t : T), hξ⟩
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) ξ
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  exact cartierCoefficient_pullback_of_stalkMap_bijective ι t hξ
    (ConcreteCategory.bijective_of_isIso _) B

end Coefficients

section SNC

variable {K : Type u} [Field K] {n : ℕ} {T Tb : Scheme.{u}} [IsIntegral T] [IsIntegral Tb]
  [T.Over (Spec (CommRingCat.of K))] [Tb.Over (Spec (CommRingCat.of K))]
  (ι : T ⟶ Tb) [IsOpenImmersion ι] [IsDominant ι] [ι.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A chart in simple normal crossing position inside the range of an open immersion pulls back
to a chart in simple normal crossing position for a subfamily of the members in the source. -/
theorem isSNCChart_pullbackToOpenImmersion (c : EtaleChart K Tb n) (hc : c.U ≤ ι.opensRange)
    {rb r : ℕ} (ξb : Fin rb → Tb) (σ : Fin rb → Option (Fin n)) (h : IsSNCChart c ξb σ)
    (ξ : Fin r → T) (e : Fin r → Fin rb) (he : Function.Injective e)
    (hξ : ∀ i, ι (ξ i) = ξb (e i)) :
    IsSNCChart (etaleChartPullbackToOpenImmersion ι c hc) ξ (σ ∘ e) := by
  refine ⟨fun i j a hi hj => he (h.1 (e i) (e j) a hi hj), fun i => ?_⟩
  have hcl : closure ({ξ i} : Set T) = ι ⁻¹' closure ({ξb (e i)} : Set Tb) := by
    rw [ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hξ]
  have hU : ((etaleChartPullbackToOpenImmersion ι c hc).U : Set T) = ι ⁻¹' (c.U : Set Tb) := rfl
  rw [hU, hcl, ← Set.preimage_inter, h.2 (e i)]
  simp only [Function.comp_apply]
  cases σ (e i) with
  | none => simp
  | some a =>
    simp only [Option.elim_some]
    rw [Set.preimage_inter, Scheme.zeroLocus_singleton, Scheme.zeroLocus_singleton,
      Set.preimage_compl]
    congr 2
    exact congrArg (fun W : T.Opens => (W : Set T))
      (Scheme.preimage_basicOpen ι (c.coords (MvPolynomial.X a)))

/-- **Restriction of a simple normal crossing family to an open subscheme.** The members of a
family of codimension-one points in simple normal crossing position that lie in the range of an
open immersion form, in the source, a family of codimension-one points in simple normal crossing
position; every point of the source over a member is a member. -/
theorem exists_isSNCFamily_of_isOpenImmersion {rb : ℕ} (ξb : Fin rb → Tb)
    (hinj : Function.Injective ξb) (hcoh : ∀ i, Order.coheight (ξb i) = 1)
    (hsnc : IsSNCFamily K n ξb) :
    ∃ (r : ℕ) (ξ : Fin r → T), Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧
      IsSNCFamily K n ξ ∧ (∀ i, ι (ξ i) ∈ Set.range ξb) ∧
      ∀ t : T, ι t ∈ Set.range ξb → t ∈ Set.range ξ := by
  classical
  let S := {i : Fin rb // ξb i ∈ Set.range ι}
  let eS : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hpre : ∀ s : S, ∃ t : T, ι t = ξb s.1 := fun s => s.2
  choose pre hpre using hpre
  let ξ : Fin (Fintype.card S) → T := fun i => pre (eS i)
  have hιξ : ∀ i, ι (ξ i) = ξb (eS i).1 := fun i => hpre (eS i)
  have he : Function.Injective (fun i => (eS i).1) := fun i j h => eS.injective (Subtype.ext h)
  refine ⟨Fintype.card S, ξ, ?_, ?_, ?_, fun i => ⟨_, (hιξ i).symm⟩, ?_⟩
  · intro i j h
    apply he
    apply hinj
    rw [← hιξ, ← hιξ, h]
  · intro i
    rw [← coheight_eq_of_isOpenImmersion ι (ξ i), hιξ]
    exact hcoh _
  · intro x
    obtain ⟨c, σ, hx, hc⟩ := hsnc (ι x)
    obtain ⟨a, ha, hxa⟩ := c.isAffine.exists_basicOpen_le
      (V := ι.opensRange) ⟨ι x, ⟨x, rfl⟩⟩ hx
    have hc₁ := isSNCChart_basicOpen hc a ⟨⟨ι x, hxa⟩⟩
    exact ⟨etaleChartPullbackToOpenImmersion ι (etaleChartBasicOpen c a ⟨⟨ι x, hxa⟩⟩) ha,
      σ ∘ (fun i => (eS i).1), hxa,
      isSNCChart_pullbackToOpenImmersion ι _ ha ξb σ hc₁ ξ _ he hιξ⟩
  · rintro t ⟨i, hi⟩
    have hiS : ξb i ∈ Set.range ι := ⟨t, hi.symm⟩
    refine ⟨eS.symm ⟨i, hiS⟩, ?_⟩
    apply ι.isOpenEmbedding.injective
    rw [hιξ, Equiv.apply_symm_apply, hi]

end SNC

section LocalEquation

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

/-- For an effective Cartier divisor, `1` is a local equation of its pullback at a point exactly
when it is a local equation of the divisor at the image point: a regular local equation at the
image becomes a unit upstairs, hence is a unit since the stalk map is local. -/
theorem cartierPullback_isLocalEquationAt_one_iff {D : CartierDivisor X} (hD : D.IsEffective)
    (x : T) :
    (cartierPullback ρ D).IsLocalEquationAt x 1 ↔ D.IsLocalEquationAt (ρ x) 1 := by
  constructor
  · intro h1
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ x)
    obtain ⟨v, hv⟩ := (cartierPullback_isLocalEquationAt ρ D x hf).exists_unit_mul_eq h1
    obtain ⟨a, ha⟩ := (CartierDivisor.isEffective_iff_exists.mp hD (ρ x)).elim fun g hg =>
      (hg.1.mul_mem_range_iff hf 1).mp (by simpa using hg.2)
    rw [mul_one] at ha
    have hstalk : ρ.stalkMap x a = v := by
      apply IsFractionRing.injective (T.presheaf.stalk x) T.functionField
      rw [← dominantFunctionFieldMap_algebraMap, ha]
      rw [Units.val_one, mul_one, Units.coe_map] at hv
      exact hv.symm
    have hunit : IsUnit a :=
      (isUnit_map_iff (ρ.stalkMap x).hom a).mp (hstalk ▸ v.isUnit)
    refine isLocalEquationAt_stalkUnit_mul hf hunit.unit⁻¹ ?_
    rw [Units.val_one, ← ha, ← map_mul, IsUnit.val_inv_mul hunit, map_one]
  · intro h1
    simpa using cartierPullback_isLocalEquationAt ρ D x h1

end LocalEquation

section Big

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra functionFieldBaseScalarTower

/-- Bigness passes to the pullback along a dominant morphism of the same dimension when the
sections of the multiples of the pullback are finite-dimensional: sections pull back
injectively. No normality of the target is needed. -/
theorem cartierIsBig_cartierPullback_of_finiteDimensional (g : T ⟶ X) [IsDominant g]
    [g.IsOver (Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim T = topologicalKrullDim X) {D : CartierDivisor X}
    (hfin : ∀ m : ℕ, FiniteDimensional K Γ((m • cartierPullback g D).sheaf, ⊤))
    (hD : CartierIsBig K D) : CartierIsBig K (cartierPullback g D) := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  refine ⟨d, hdim.trans hd, c, hc, hfreq.mono fun m hm => hm.trans ?_⟩
  have hfm : FiniteDimensional K Γ((cartierPullback g (m • D)).sheaf, ⊤) := by
    rw [cartierPullback_nsmul]
    exact hfin m
  have hle := LinearMap.finrank_le_finrank_of_injective
    (cartierDominantPullbackLinear_injective g K (m • D))
  have heq : Module.finrank K Γ((cartierPullback g (m • D)).sheaf, ⊤) =
      Module.finrank K Γ((m • cartierPullback g D).sheaf, ⊤) := by
    rw [cartierPullback_nsmul]
  rw [← heq]
  exact_mod_cast hle

end Big

section Diagonal

variable {K : Type u} [Field K]

/-- A scheme separated over a field has affine diagonal over the terminal scheme. -/
theorem isAffineHom_diagonal_terminal_of_isSeparated (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))] :
    IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X)) := by
  haveI : IsSeparated (Limits.terminal.from X) := by
    rw [show Limits.terminal.from X =
      (X ↘ Spec (CommRingCat.of K)) ≫ Limits.terminal.from (Spec (CommRingCat.of K)) from
        Subsingleton.elim _ _]
    infer_instance
  infer_instance

end Diagonal

end MixedFujita

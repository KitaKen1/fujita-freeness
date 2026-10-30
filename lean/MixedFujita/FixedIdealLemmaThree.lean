/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LemmaThreeSlices
public import MixedFujita.IsolationExtractionPrime
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.DiscrepancyPrimeComparison
public import MixedFujita.CrepantDiscrepancyComposition
public import MixedFujita.RelativeCanonicalEffectivity
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.ToricChartModel
public import MixedFujita.EtaleChartDimension

/-!
Lemma 3 for a fixed family (step 9): on an affine open V of a smooth variety Y over an
algebraically closed field of characteristic zero, the closed points at which the threshold of
finitely many sections g_j of V is at most 1/M in the model form are the zero set of an ideal of
Γ(V) (`exists_ideal_modelThresholdBadAt_of_affine`).

On V as a scheme, a projective simple normal crossing model T principalizes the sum of the ideal
sheaves of the divisors of the nonzero g_j: the divisor G of this ideal on T has at every point the
least coefficient of the divisors of the g_j. A member ξ_s of the family is bad if
M (1 - b_s) ≤ G_s, for its crepant boundary coefficient b_s, and a bad member is a test prime of Y
through every point of the image of its closure. Conversely, the part over V of an arbitrary smooth
birational test model maps to V, and the orders o_s of the family along a prime e satisfy the
minimum formula Σ_s G_s o_s = min_j ord_e g_j and Σ_s (1 - b_s) o_s ≤ A(e); if e is bad, then
M Σ_s (1 - b_s) o_s ≤ Σ_s G_s o_s forces a bad member with o_s > 0 through the centre of e. So the
bad points are the image of the closures of the bad members, a closed set by properness, and its
vanishing ideal works. For the zero family every closed point is bad in positive dimension (a toric
extraction at the point) and no point is bad in dimension zero.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Congr

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

/-- The discrepancy divisor depends only on the morphism. -/
theorem logDiscrepancyDivisor_congr_hom {ρ ρ' : T ⟶ X} (h : ρ = ρ') [IsDominant ρ]
    [IsDominant ρ'] [ρ.IsOver (Spec (CommRingCat.of K))] [ρ'.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hρ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ'))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (D : CartierDivisor X)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    logDiscrepancyDivisor n ρ hρ c₀ f₀ r D c'₀ hT =
      logDiscrepancyDivisor n ρ' hρ' c₀ f₀ r D c'₀ hT := by
  subst h
  rfl

/-- The Cartier pullback depends only on the morphism. -/
theorem cartierPullback_congr_hom {ρ ρ' : T ⟶ X} (h : ρ = ρ') [IsDominant ρ] [IsDominant ρ']
    (D : CartierDivisor X) : cartierPullback ρ D = cartierPullback ρ' D := by
  subst h
  rfl

/-- The map of function fields over the base field depends only on the morphism. -/
theorem dominantFunctionFieldAlgHom_congr_hom {ρ ρ' : T ⟶ X} (h : ρ = ρ') [IsDominant ρ]
    [IsDominant ρ'] [ρ.IsOver (Spec (CommRingCat.of K))]
    [ρ'.IsOver (Spec (CommRingCat.of K))] :
    dominantFunctionFieldAlgHom (K := K) ρ = dominantFunctionFieldAlgHom (K := K) ρ' := by
  subst h
  rfl

end Congr

section FixedIdeal

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

omit [IsAlgClosed K] [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- With zero boundary on a smooth variety the discrepancy of every test prime is nonnegative:
the relative canonical divisor is effective. -/
theorem zeroBoundary_logDiscrepancy_coefficient_nonneg (cY : EtaleChart K Y n)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))] (σ : U ⟶ Y) [IsDominant σ]
    [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U n)
    (e : U) :
    0 ≤ cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU
        etaleCharts_cover) e := by
  rw [logDiscrepancyDivisor_boundary_zero σ hσ cY 1 1 cU, cartierCoefficient_nsmul]
  have h := cartierCoefficient_nonneg_of_isEffective _
    (birationalRelativeCanonicalDivisor_isEffective σ hσ cY etaleCharts_cover cU
      etaleCharts_cover) e
  simpa using h

omit [CharZero K] in
/-- In positive dimension every closed point is bad for the zero family: the exceptional prime of
a toric extraction at the point. -/
theorem modelThresholdBadAt_of_forall_eq_zero (hn : 1 ≤ n) (cY : EtaleChart K Y n) (y : Y)
    (hy : IsClosed ({y} : Set Y)) {J : Type*} (g : J → Y.functionField) (hg : ∀ j, g j = 0)
    (M : ℕ) :
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
      g M := by
  classical
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) y hy
  obtain ⟨c, hyc⟩ : ∃ c : EtaleChart K Y n, y ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top y)
  have hw : (fun _ : Fin n => 1) ≠ (0 : Fin n → ℕ) := fun h => by
    have h1 := congrFun h ⟨0, hn⟩
    simp at h1
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, -, -, -, -, he, -, hxe, -, -⟩ :=
    exists_toric_extraction_model (etaleChartCentered c (rationalAffineGermPoint y hyc β)) y
      hyc (fun _ => 1) hw (fun a _ => etaleChartCentered_germ_not_isUnit c y hyc β a)
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, ⟨e, he⟩, hxe, ?_,
    fun j hj => absurd (hg j) hj⟩
  have h0 := zeroBoundary_logDiscrepancy_coefficient_nonneg cY σ hσ cU e
  have h0' : (0 : ℝ) ≤ (cartierCoefficient (logDiscrepancyDivisor n σ hσ cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU
        etaleCharts_cover) e : ℝ) := by exact_mod_cast h0
  rw [Nat.cast_one, div_one]
  linarith

omit [IsAlgClosed K] [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
/-- In dimension zero no point is bad: a smooth test model of dimension zero has no prime
divisor. -/
theorem not_modelThresholdBadAt_of_eq_zero (hn : n = 0) (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) (y : Y) {J : Type*}
    (g : J → Y.functionField) (M : ℕ) : ¬ ModelThresholdBadAt cY fY d D₀ y g M := by
  rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, -, -, -⟩
  subst hn
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 0 _
  have : JacobsonSpace U := LocallyOfFiniteType.jacobsonSpace (U ↘ Spec (CommRingCat.of K))
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := closure ({(e : U)} : Set U))
    ⟨(e : U), subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hle : Order.coheight (e : U) ≤ Order.coheight z :=
    Order.coheight_anti (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hz))
  have hdim := ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    (U ↘ Spec (CommRingCat.of K)) (mem_closedPoints_iff.mp hzc)
  rw [ringKrullDim_stalk_eq_coheight, etaleChart_topologicalKrullDim cU] at hdim
  have hz0 : Order.coheight z = 0 := by exact_mod_cast hdim
  rw [e.property, hz0] at hle
  exact absurd hle (by norm_num)

/-- Lemma 3 for a fixed family on an affine open: the closed points of V at which the threshold
of the sections g_j is at most 1/M in the model form are the zero set of an ideal of Γ(V). -/
theorem exists_ideal_modelThresholdBadAt_of_affine (cY : EtaleChart K Y n) (V : Y.Opens)
    (hV : IsAffineOpen V) [Nonempty V] {J : Type} [Finite J] (g : J → Γ(Y, V)) (M : ℕ)
    (hM : 1 ≤ M) :
    ∃ I : Ideal Γ(Y, V), ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
      (ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
        (fun j => Y.germToFunctionField V (g j)) M ↔
        ∀ h ∈ I, h ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  set D₀ : CartierDivisor Y :=
    1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)) with hD₀
  set gY : J → Y.functionField := fun j => Y.germToFunctionField V (g j) with hgY
  -- the zero family
  by_cases hzero : ∀ j, gY j = 0
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · refine ⟨⊤, fun y hy _ => iff_of_false
        (not_modelThresholdBadAt_of_eq_zero hn cY _ _ _ y gY M)
        fun h => (hV.primeIdealOf ⟨y, hy⟩).isPrime.ne_top ?_⟩
      exact eq_top_iff.mpr fun a _ => h a Submodule.mem_top
    · refine ⟨⊥, fun y hy hyc => iff_of_true
        (modelThresholdBadAt_of_forall_eq_zero hn cY y hyc gY hzero M) fun h hh => ?_⟩
      rw [Ideal.mem_bot.mp hh]
      exact Ideal.zero_mem _
  push Not at hzero
  -- the nonzero members and their divisors
  let J' := {j : J // gY j ≠ 0}
  have : Nonempty J' := by
    obtain ⟨j, hj⟩ := hzero
    exact ⟨⟨j, hj⟩⟩
  -- V as a scheme over K
  have : IsAffine V.toScheme := hV
  let : V.toScheme.Over (Spec (CommRingCat.of K)) := ⟨V.ι ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have : V.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (V.ι ≫ (Y ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    infer_instance
  have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated (V.toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) V.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι
  obtain ⟨cX⟩ : Nonempty (EtaleChart K V.toScheme n) := by
    obtain ⟨z⟩ : Nonempty V.toScheme := inferInstance
    obtain ⟨c, -⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := V.toScheme) (n := n)).symm ▸ Opens.mem_top z)
    exact ⟨c⟩
  set fX : V.toScheme.functionFieldˣ := crepantPullbackFormUnit V.ι hι cY 1 cX with hfX
  set DX : CartierDivisor V.toScheme := cartierPullback V.ι D₀ with hDX
  let uY : J' → Y.functionFieldˣ := fun j => Units.mk0 (gY j.1) j.2
  let A : J' → CartierDivisor V.toScheme := fun j =>
    cartierPullback V.ι (principalCartierDivisor Y (uY j))
  have hA : ∀ j, (A j).IsEffective := by
    intro j
    have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    change (cartierPullback V.ι (principalCartierDivisor Y (uY j))).IsEffective
    rw [cartierPullback_principal, CartierDivisor.isEffective_principalCartierDivisor_iff]
    refine ⟨V.ι.appLE V ⊤ V.ι_preimage_self.ge (g j.1), ?_⟩
    rw [Units.coe_map]
    exact (dominantFunctionFieldMap_germ V.ι V ⊤ V.ι_preimage_self.ge (g j.1)).symm
  -- a principalizing simple normal crossing model of V
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, -, -, -, -, -, Gc, hGc, hGcI, hGc0, hmin, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n) cX fX 1 DX
      (Empty.elim : Empty → CartierDivisor V.toScheme) A hA
      (Empty.elim : Empty → V.toScheme.IdealSheafData) (fun j => j.elim)
  set crep : Fin r → ℤ := fun s =>
    cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX 1 DX cT etaleCharts_cover) (ξ s)
    with hcrep
  set G : Fin r → ℤ := fun s => cartierCoefficient Gc (ξ s) with hG
  set bad : Set (Fin r) := {s | (M : ℤ) * (1 - crep s) ≤ G s} with hbad
  set Z : Set V.toScheme := ⋃ s ∈ bad, ρ '' closure ({ξ s} : Set T) with hZdef
  have hZ : IsClosed Z := (Set.toFinite bad).isClosed_biUnion fun s _ =>
    (Scheme.Hom.isClosedMap ρ) _ isClosed_closure
  -- the vanishing ideal of the bad set
  have hZiff : ∀ w : V.toScheme, w ∈ Z ↔
      ∀ h ∈ (⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal),
        h ∈ (hV.primeIdealOf w).asIdeal := by
    intro w
    constructor
    · intro hw h hh
      exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hh w) hw
    · intro hw
      by_contra hwZ
      let W : Y.Opens := ⟨V.ι '' Zᶜ, V.ι.isOpenEmbedding.isOpenMap _ hZ.isOpen_compl⟩
      obtain ⟨f, hfle, hwf⟩ := hV.exists_basicOpen_le (V := W) ⟨V.ι w, ⟨w, hwZ, rfl⟩⟩ w.2
      have hf : f ∈ (⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal) := by
        refine (Submodule.mem_iInf _).mpr fun z => (Submodule.mem_iInf _).mpr fun hz => ?_
        by_contra hfz
        have hzf : z.1 ∈ Y.basicOpen f :=
          (mem_basicOpen_iff_notMem_primeIdealOf hV z.1 z.2 f).mpr hfz
        obtain ⟨z', hz'Z, hz'⟩ := hfle hzf
        have : z' = z := V.ι.isOpenEmbedding.injective hz'
        exact hz'Z (this ▸ hz)
      exact (mem_basicOpen_iff_notMem_primeIdealOf hV w.1 w.2 f).mp hwf (hw f hf)
  refine ⟨⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal, fun y hy _ => ?_⟩
  rw [← hZiff ⟨y, hy⟩]
  constructor
  · -- a bad test prime forces a bad member of the family through its centre
    rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hApos, hineq⟩
    set logY : ℤ := cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1
      D₀ cU etaleCharts_cover) (e : U) with hlogY
    have heV : σ (e : U) ∈ V := (specializes_iff_mem_closure.mpr hye).mem_open V.isOpen hy
    let U' : U.Opens := σ ⁻¹ᵁ V
    have : Nonempty U' := ⟨⟨(e : U), heV⟩⟩
    let : U'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U'.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
    have : U'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    have : IsDominant U'.ι :=
      ⟨U'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    have : SmoothOfRelativeDimension n (U'.toScheme ↘ Spec (CommRingCat.of K)) := by
      rw [← HomIsOver.comp_over (f := U'.ι) (S := Spec (CommRingCat.of K))]
      have h : SmoothOfRelativeDimension (0 + n) (U'.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
        inferInstance
      simpa only [Nat.zero_add] using h
    have : IsDominant (σ ∣_ V) := isDominant_morphismRestrict_integral σ V
    have hsq : (σ ∣_ V) ≫ V.ι = U'.ι ≫ σ := morphismRestrict_ι σ V
    have : (σ ∣_ V).IsOver (Spec (CommRingCat.of K)) := by
      constructor
      change (σ ∣_ V) ≫ V.ι ≫ (Y ↘ Spec (CommRingCat.of K)) =
        U'.ι ≫ (U ↘ Spec (CommRingCat.of K))
      rw [← Category.assoc, hsq, Category.assoc, HomIsOver.comp_over]
    have hU'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) U'.ι) :=
      dominantFunctionFieldMap_bijective_of_isOpenImmersion U'.ι
    have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ ∣_ V)) := by
      have h2 := dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι
      rw [← dominantFunctionFieldAlgHom_congr_hom hsq, dominantFunctionFieldAlgHom_comp,
        AlgHom.coe_comp] at h2
      exact (Function.Bijective.of_comp_iff _ hι).mp h2
    have hbij : Function.Bijective (U'.ι.stalkMap ⟨(e : U), heV⟩) :=
      ConcreteCategory.bijective_of_isIso _
    let e' : CodimensionOnePoint U'.toScheme :=
      ⟨⟨(e : U), heV⟩,
        (coheight_eq_of_stalkMap_bijective U'.ι ⟨(e : U), heV⟩ hbij).trans e.property⟩
    obtain ⟨cU'⟩ : Nonempty (EtaleChart K U'.toScheme n) := by
      obtain ⟨c, -⟩ := Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := U'.toScheme) (n := n)).symm ▸
          Opens.mem_top (e' : U'.toScheme))
      exact ⟨c⟩
    obtain ⟨o, t₀, ht₀, ho, hosupp, -, ⟨-, j₀, hj₀⟩, hdisc⟩ :=
      exists_snc_orders_at_test_prime ρ hρ cX fX 1 DX cT ξ hinj hcoh hsnc hsupp A hA Gc hGc hGc0
        hGcI (σ ∣_ V) hσ' cU' e'
    -- orders and discrepancies on the part of the test model over V
    have hord : ∀ k : J', cartierCoefficient (cartierPullback (σ ∣_ V) (A k))
        (e' : U'.toScheme) = U.ord ((dominantFunctionFieldMap σ).hom (gY k.1)) (e : U) := by
      intro k
      have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
      have : Smooth (U'.toScheme ↘ Spec (CommRingCat.of K)) :=
        SmoothOfRelativeDimension.smooth n _
      have := smoothOverField_codimensionOne_stalk_DVR (K := K)
        (⟨U'.ι (e' : U'.toScheme), e.property⟩ : CodimensionOnePoint U)
      have := smoothOverField_codimensionOne_stalk_DVR (K := K) e'
      change cartierCoefficient (cartierPullback (σ ∣_ V)
        (cartierPullback V.ι (principalCartierDivisor Y (uY k)))) _ = _
      rw [← cartierPullback_comp V.ι (σ ∣_ V), cartierPullback_congr_hom hsq,
        cartierPullback_comp σ U'.ι,
        cartierCoefficient_pullback_of_stalkMap_bijective U'.ι e' e.property hbij,
        cartierPullback_principal, cartierCoefficient_principal]
      rfl
    have hlog : cartierCoefficient (logDiscrepancyDivisor n (σ ∣_ V) hσ' cX fX 1 DX cU'
        etaleCharts_cover) (e' : U'.toScheme) = logY := by
      rw [hfX, hDX, ← logDiscrepancyDivisor_comp V.ι (σ ∣_ V) hι hσ' cY 1 1 D₀ cX cU'
        etaleCharts_cover, logDiscrepancyDivisor_congr_hom hsq _
        (dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι)]
      exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ U'.ι hσ hU'ι cY 1 1
        D₀ cU cU' e' e.property hbij
    -- the weighted inequality
    have hb := hineq j₀.1 j₀.2
    rw [← hord j₀, ← hj₀, Nat.cast_one, div_one] at hb
    rw [Nat.cast_one, div_one] at hApos
    have hbZ : (M : ℤ) * (1 + logY) ≤ ∑ s, G s * o s := by exact_mod_cast hb
    have hAZ : 0 < 1 + logY := by exact_mod_cast hApos
    rw [hlog] at hdisc
    have hdisc' : (1 : ℤ) * ∑ s, o s - ∑ s, crep s * o s ≤ 1 + logY := by exact_mod_cast hdisc
    have hsum : (M : ℤ) * ∑ s, (1 + -crep s) * o s ≤ ∑ s, G s * o s := by
      have h1 : ∑ s, (1 + -crep s) * o s = (1 : ℤ) * ∑ s, o s - ∑ s, crep s * o s := by
        rw [one_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h1]
      have hM0 : (0 : ℤ) ≤ M := by positivity
      exact (mul_le_mul_of_nonneg_left hdisc' hM0).trans hbZ
    have hpos : 0 < ∑ s, G s * o s := by
      have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
      nlinarith
    obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge ho hsum hpos
    have hsbad : s ∈ bad := by
      change (M : ℤ) * (1 - crep s) ≤ G s
      linarith [hs]
    -- the centre of e lies in the image of the closure of the bad member
    have hyc : (⟨y, hy⟩ : V.toScheme) ∈
        closure ({(σ ∣_ V) (e' : U'.toScheme)} : Set V.toScheme) := by
      have h1 : V.ι ((σ ∣_ V) (e' : U'.toScheme)) = σ (e : U) := by
        rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
        rfl
      apply (mem_closure_singleton_open_immersion_iff V.ι ((σ ∣_ V) (e' : U'.toScheme))
        ⟨y, hy⟩).mp
      rw [h1]
      exact hye
    rw [← ht₀] at hyc
    exact Set.mem_biUnion hsbad (closure_minimal
      (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem ρ (hosupp s hos.ne')))
      ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure) hyc)
  · -- a bad member through the point is a bad test prime of Y
    intro hw
    obtain ⟨s, hs, t, ht, hty⟩ := Set.mem_iUnion₂.mp hw
    have hσT := dominantFunctionFieldAlgHom_comp_bijective V.ι ρ hι hρ
    have hcomp : logDiscrepancyDivisor n (ρ ≫ V.ι) hσT cY (1 : Y.functionFieldˣ) 1 D₀ cT
        etaleCharts_cover = logDiscrepancyDivisor n ρ hρ cX fX 1 DX cT etaleCharts_cover :=
      logDiscrepancyDivisor_comp V.ι ρ hι hρ cY 1 1 D₀ cX cT etaleCharts_cover
    have hc : crep s = - cartierCoefficient (logDiscrepancyDivisor n ρ hρ cX fX 1 DX cT
        etaleCharts_cover) (ξ s) := by
      change cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX 1 DX cT etaleCharts_cover)
        (ξ s) = _
      rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    refine ⟨T, hTi, inferInstance, hTo, hTs, ρ ≫ V.ι, inferInstance, inferInstance, hσT, cT,
      ⟨ξ s, hcoh s⟩, ?_, ?_, ?_⟩
    · have h1 : ρ t ∈ closure ({ρ (ξ s)} : Set V.toScheme) :=
        map_mem_closure ρ.continuous ht fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          rfl
      have h2 := (mem_closure_singleton_open_immersion_iff V.ι (ρ (ξ s)) (ρ t)).mpr h1
      rw [hty] at h2
      rw [Scheme.Hom.comp_apply]
      exact h2
    · have h0 := zeroBoundary_logDiscrepancy_coefficient_nonneg cY (ρ ≫ V.ι) hσT cT (ξ s)
      have h0' : (0 : ℝ) ≤ ((cartierCoefficient (logDiscrepancyDivisor n (ρ ≫ V.ι) hσT cY
          (1 : Y.functionFieldˣ) 1 D₀ cT etaleCharts_cover) (ξ s) : ℤ) : ℝ) := by
        exact_mod_cast h0
      rw [Nat.cast_one, div_one]
      linarith
    · intro j hj
      have hordT : T.ord ((dominantFunctionFieldMap (ρ ≫ V.ι)).hom (gY j)) (ξ s) =
          cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := by
        change _ = cartierCoefficient (cartierPullback ρ
          (cartierPullback V.ι (principalCartierDivisor Y (uY ⟨j, hj⟩)))) (ξ s)
        rw [← cartierPullback_comp V.ι ρ, cartierPullback_principal, cartierCoefficient_principal]
        rfl
      have hmin1 := (hmin (ξ s)).1 ⟨j, hj⟩
      have hsZ : (M : ℤ) * (1 - crep s) ≤ G s := hs
      have hG1 : G s ≤ cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := hmin1
      have hfin : (M : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n (ρ ≫ V.ι) hσT cY
          (1 : Y.functionFieldˣ) 1 D₀ cT etaleCharts_cover) (ξ s)) ≤
          T.ord ((dominantFunctionFieldMap (ρ ≫ V.ι)).hom (gY j)) (ξ s) := by
        have hx : cartierCoefficient (logDiscrepancyDivisor n ρ hρ cX fX 1 DX cT
            etaleCharts_cover) (ξ s) = - crep s := by linarith [hc]
        rw [hcomp, hordT, hx]
        linarith
      rw [Nat.cast_one, div_one]
      exact_mod_cast hfin

end FixedIdeal

end MixedFujita

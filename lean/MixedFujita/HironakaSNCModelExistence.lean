/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCDictionary
public import MixedFujita.HironakaBlowUpModels
public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.CartierSectionPrimeDecomposition
public import MixedFujita.DiscrepancyPrimeComparison
public import Hironaka.Resolution.Algebraic.Hir64.MainTheoremI
public import Hironaka.Resolution.Algebraic.Hir64.ComponentwiseCorollaries
public import Hironaka.Scheme.IdealSheaf.Order.Specialization
public import Hironaka.Scheme.Snc.Dictionary
public import Hironaka.Scheme.BlowUpSequence.Projective
public import MixedFujita.BlowUpProjectiveEmbedding
public import MixedFujita.HironakaPrincipalizingRound
public import MixedFujita.EffectiveCartierCoefficientSupport

/-!
Existence of a proper simple normal crossing model (step 7). Let X be an integral scheme of finite
type and separated over a field K of characteristic zero, with an étale chart of n coordinates, a
rational top form and a Cartier divisor D (the data of a log pair with denominator d). Then there
are a scheme T, integral and smooth of relative dimension n over K, a proper birational morphism
ρ from T to X, and finitely many distinct codimension-one points of T forming a simple normal
crossing family on étale charts, outside of which the crepant boundary of the pair on T has
coefficient zero. This is the model assumed by the comparison of discrepancies on all smooth
models: with it, being klt on all proper smooth birational models is equivalent to finitely many
strict inequalities between the coefficients of the crepant boundary on one such model.

Proof. Hironaka's Main Theorem I gives one blow-up T₀ of X, with centre supported on the singular
locus, that is regular, hence smooth over K. The crepant boundary on T₀ is a Cartier divisor on an
integral Noetherian scheme: its coefficients vanish outside finitely many codimension-one points,
the union W₀ of whose closures is closed and nowhere dense. Hironaka's Corollary 3 gives a
succession of blow-ups T of T₀ with centres over W₀, regular, on which the reduced preimage of W₀
has only normal crossings; by the dictionary its generic points form a simple normal crossing
family of codimension-one points. A codimension-one point t of T outside this family does not lie
over W₀, so T → T₀ is an isomorphism on the stalks at t, its image has codimension one, and the
coefficient of the crepant boundary at t is the coefficient on T₀ at the image, which is zero.

The same model principalizes finitely many given ideal sheaves 𝔠_k of X whose supports do not
contain the generic point: the second round is run for the union of W₀ and the supports of the
inverse images of the 𝔠_k on T₀, and begins with the blow-ups of these inverse images. On T the
inverse image of each 𝔠_k is invertible, hence the ideal sheaf of an effective Cartier divisor,
whose prime components lie in the support of the inverse image and therefore belong to the
normal crossing family; and T dominates the blow-up of X along each 𝔠_k.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Topology

variable {T : Scheme.{u}} [IsIntegral T]

/-- The generic point of an integral scheme is maximal for generization. -/
theorem coheight_genericPoint_eq_zero : Order.coheight (genericPoint T) = 0 := by
  apply Order.coheight_eq_zero.mpr
  intro z _
  exact Scheme.le_iff_specializes.mpr ((genericPoint_spec T).specializes (Set.mem_univ z))

/-- The generic point of an integral scheme is not in the closure of a codimension-one point. -/
theorem genericPoint_notMem_closure_of_coheight_eq_one {x : T} (hx : Order.coheight x = 1) :
    genericPoint T ∉ closure ({x} : Set T) := by
  intro h
  have h1 : x ⤳ genericPoint T := specializes_iff_mem_closure.mpr h
  have h2 : genericPoint T ⤳ x := (genericPoint_spec T).specializes (Set.mem_univ x)
  have hxe : x = genericPoint T := (h1.antisymm h2).eq
  rw [hxe, coheight_genericPoint_eq_zero] at hx
  exact zero_ne_one hx

end Topology

section CartierSupport

variable {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]

/-- The closed support of a Cartier divisor on an integral Noetherian scheme: the union of the
closures of the finitely many codimension-one points at which its coefficient is nonzero. -/
noncomputable def cartierSupportCloseds (B : CartierDivisor T) : Closeds T :=
  ⟨⋃ x ∈ B.toWeilDivisor.support, closure ({(x : T)} : Set T),
    isClosed_biUnion_finset fun _ _ => isClosed_closure⟩

/-- The coefficient of a Cartier divisor vanishes at a codimension-one point outside its closed
support. -/
theorem cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds (B : CartierDivisor T)
    (x : T) (hx : Order.coheight x = 1) (h : x ∉ (cartierSupportCloseds B : Set T)) :
    cartierCoefficient B x = 0 := by
  have hns : (⟨x, hx⟩ : CodimensionOnePoint T) ∉ B.toWeilDivisor.support := by
    intro hmem
    have hx' : x ∈ ⋃ y ∈ B.toWeilDivisor.support, closure ({(y : T)} : Set T) :=
      Set.mem_iUnion₂.mpr ⟨⟨x, hx⟩, hmem, subset_closure rfl⟩
    exact h hx'
  have h0 : B.toWeilDivisor ⟨x, hx⟩ = 0 := Finsupp.notMem_support_iff.mp hns
  have hc : WeilDivisor.coeff B.toWeilDivisor ⟨x, hx⟩ = cartierCoefficient B x :=
    cartier_toWeilDivisor_coeff_eq_cartierCoefficient B ⟨x, hx⟩
  rw [← hc]
  exact h0

/-- The closed support of a Cartier divisor does not contain the generic point. -/
theorem genericPoint_notMem_cartierSupportCloseds (B : CartierDivisor T) :
    genericPoint T ∉ (cartierSupportCloseds B : Set T) := by
  intro h
  have h' : genericPoint T ∈ ⋃ y ∈ B.toWeilDivisor.support, closure ({(y : T)} : Set T) := h
  obtain ⟨x, -, hx⟩ := Set.mem_iUnion₂.mp h'
  exact genericPoint_notMem_closure_of_coheight_eq_one x.property hx

end CartierSupport

section Models

variable {K : Type u} [Field K] [PerfectField K] {n : ℕ}

/-- The last stage of a succession of blow-ups of an integral scheme locally of finite type over a
perfect field, with centres over a closed set not containing the generic point and regular last
stage, is smooth of relative dimension n over the field when the base has an étale chart with n
coordinates. -/
theorem blowUpSequence_smoothOfRelativeDimension_of_centers_over {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (S : Scheme.BlowUpSequence Y) (Z : Closeds Y)
    (hZ : ∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
      S.stageMap i.castSucc z ∈ (Z : Set Y))
    (hη : genericPoint Y ∉ (Z : Set Y)) (hreg : IsRegular S.last) (c : EtaleChart K Y n) :
    SmoothOfRelativeDimension n (S.composite ≫ (Y ↘ Spec (CommRingCat.of K))) := by
  have hY : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  have : IsIntegral S.last := blowUpSequence_isIntegral_last_of_centers_over S Z hZ hη
  have hprop : IsProper S.composite := S.isProper_composite
  let : S.last.Over (Spec (CommRingCat.of K)) :=
    ⟨S.composite ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (S.composite ≫ (Y ↘ Spec (CommRingCat.of K))))
  have : Smooth (S.last ↘ Spec (CommRingCat.of K)) := blowUpSequence_smooth_of_isRegular S hreg
  obtain ⟨t₀, ht₀⟩ := blowUpSequence_exists_last_over S Z hZ (genericPoint Y) hη
  have hc : genericPoint Y ∈ c.U := by
    obtain ⟨⟨y, hy⟩⟩ := c.nonempty
    exact ((genericPoint_spec Y).mem_open_set_iff c.U.isOpen).mpr ⟨y, Set.mem_univ y, hy⟩
  exact smoothOfRelativeDimension_of_isIso_stalkMap_of_etaleChart (T := S.last) S.composite c
    (S.composite ⁻¹ᵁ Z.compl)
    (fun t ht => blowUpSequence_isIso_stalkMap_of_centers_over S Z hZ t ht)
    t₀ (by change S.composite t₀ ∉ (Z : Set Y); rw [ht₀]; exact hη) (by rw [ht₀]; exact hc)

end Models

section Existence

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A projective simple normal crossing model of a log pair, finitely many further Cartier
divisors and finitely many ideal sheaves exists: a smooth T of relative dimension n with a
projective birational morphism to X and a simple normal crossing family of codimension-one points
outside of which the crepant boundary and the pullbacks of the further divisors have coefficient
zero. Every closed immersion of X into a projective space over the base field gives a closed
immersion of T into a projective space over the base field. The inverse image on T of each of the
ideal sheaves, whose supports do not contain the generic point, is invertible, so T dominates the
blow-up of X along it, and it is the ideal sheaf of an effective Cartier divisor; its support
contains no codimension-one point outside the family, so the coefficients of the divisor vanish
outside the family: the ideal sheaves are principalized with simple normal crossing support. -/
theorem exists_projective_snc_model_principalizing {ι κ : Type*} [Finite ι] [Finite κ]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (G : ι → CartierDivisor X) (𝔠 : κ → X.IdealSheafData)
    (h𝔠 : ∀ k, genericPoint X ∉ ((𝔠 k).support : Set X)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      (∀ (N : ℕ) (e : X ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
        e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K) →
        ∃ (M : ℕ) (e' : T ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
          e' ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K)) ∧
      (∀ (k : κ) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        (t : T) ∉ ((𝔠 k).comap ρ).support) ∧
      ∀ k : κ, ((𝔠 k).comap ρ).IsInvertible ∧
        (∃ g : T ⟶ (𝔠 k).blowUp, g ≫ (𝔠 k).blowUpπ = ρ) ∧
        ∃ (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
          effectiveCartierIdealSheaf Gc hGc = (𝔠 k).comap ρ ∧
          ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
            cartierCoefficient Gc (t : T) = 0 := by
  classical
  have hXN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  have hXcompact : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  have hXnoeth : IsNoetherian X :=
    { toIsLocallyNoetherian := hXN, toCompactSpace := hXcompact }
  -- Step 1: one blow-up of X with centre on the singular locus is regular
  let Xk : AlgScheme K :=
    MorphismProperty.Over.mk ⊤ (X ↘ Spec (CommRingCat.of K)) ⟨inferInstance, inferInstance⟩
  have hXi : IsIntegral Xk.left := ‹IsIntegral X›
  obtain ⟨D₀, hsupp, hreg₀⟩ : ∃ D₀ : X.IdealSheafData,
      (D₀.support : Set X) = X.singularLocus ∧ IsRegular D₀.blowUp :=
    exists_support_eq_singularLocus_isRegular_blowUp Xk
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Scheme.BlowUpSequence X,
      S₁ = Scheme.BlowUpSequence.cons X D₀ (Scheme.BlowUpSequence.nil D₀.blowUp) := ⟨_, rfl⟩
  have hZ₁ : ∀ (i : Fin S₁.length) (z : S₁.stage i.castSucc), z ∈ (S₁.center i).support →
      S₁.stageMap i.castSucc z ∈ (D₀.support : Set X) := by
    subst hS₁
    rintro ⟨_ | j, hj⟩ z hz
    · exact hz
    · exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  have hη₁ : genericPoint X ∉ (D₀.support : Set X) := by
    rw [hsupp]
    exact fun h => h Hironaka.Resolution.isRegularAt_genericPoint_of_isIntegral
  have hreg₁ : IsRegular S₁.last := by
    subst hS₁
    exact hreg₀
  have hT₀int : IsIntegral S₁.last :=
    blowUpSequence_isIntegral_last_of_centers_over S₁ D₀.support hZ₁ hη₁
  have hT₀N : IsLocallyNoetherian S₁.last := isLocallyNoetherian_stage S₁ (Fin.last S₁.length)
  have hπ₀dom : IsDominant S₁.composite :=
    blowUpSequence_isDominant_of_centers_over S₁ D₀.support hZ₁ hη₁
  have hπ₀prop : IsProper S₁.composite := S₁.isProper_composite
  let instT₀ : S₁.last.Over (Spec (CommRingCat.of K)) :=
    ⟨S₁.composite ≫ (X ↘ Spec (CommRingCat.of K))⟩
  have hπ₀over : S₁.composite.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hT₀sm : SmoothOfRelativeDimension n (S₁.last ↘ Spec (CommRingCat.of K)) :=
    blowUpSequence_smoothOfRelativeDimension_of_centers_over S₁ D₀.support hZ₁ hη₁ hreg₁ c
  have hρ₀ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) S₁.composite) :=
    dominantFunctionFieldMap_bijective_of_isIso_stalkMap S₁.composite
      (blowUpSequence_isIso_stalkMap_of_centers_over S₁ D₀.support hZ₁ (genericPoint S₁.last)
        (by rw [dominant_map_genericPoint]; exact hη₁))
  have hT₀ft : LocallyOfFiniteType (S₁.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (S₁.composite ≫ (X ↘ Spec (CommRingCat.of K))))
  have hT₀qc : QuasiCompact (S₁.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact (S₁.composite ≫ (X ↘ Spec (CommRingCat.of K))))
  have hT₀sep : IsSeparated (S₁.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (IsSeparated (S₁.composite ≫ (X ↘ Spec (CommRingCat.of K))))
  have hT₀c : CompactSpace S₁.last :=
    QuasiCompact.compactSpace_of_compactSpace (S₁.last ↘ Spec (CommRingCat.of K))
  have hT₀noeth : IsNoetherian S₁.last :=
    { toIsLocallyNoetherian := hT₀N, toCompactSpace := hT₀c }
  obtain ⟨cT₀⟩ : Nonempty (EtaleChart K S₁.last n) := by
    obtain ⟨w⟩ : Nonempty S₁.last := inferInstance
    exact ⟨Classical.choose (show ∃ e : EtaleChart K S₁.last n, w ∈ e.U from
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S₁.last) (n := n)).symm ▸
        Opens.mem_top w))⟩
  -- Step 2: the closed support of the crepant boundary on the first model
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Closeds S₁.last, (W₀ : Set S₁.last) =
      (cartierSupportCloseds (crepantBoundaryCartier S₁.composite hρ₀ c f d D cT₀
        etaleCharts_cover) : Set S₁.last) ∪
      ⋃ j, (cartierSupportCloseds (cartierPullback S₁.composite (G j)) : Set S₁.last) :=
    ⟨⟨_, (cartierSupportCloseds _).isClosed.union
      (isClosed_iUnion_of_finite fun j => (cartierSupportCloseds _).isClosed)⟩, rfl⟩
  have hW₀η : genericPoint S₁.last ∉ (W₀ : Set S₁.last) := by
    rw [hW₀]
    rintro (h | h)
    · exact genericPoint_notMem_cartierSupportCloseds _ h
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact genericPoint_notMem_cartierSupportCloseds _ hj
  -- the inverse images of the ideal sheaves on the first model, and the closed set of the round
  obtain ⟨𝔠₀, h𝔠₀⟩ : ∃ 𝔠₀ : κ → S₁.last.IdealSheafData,
      ∀ k, 𝔠₀ k = (𝔠 k).comap S₁.composite := ⟨_, fun _ => rfl⟩
  have h𝔠₀η : ∀ k, genericPoint S₁.last ∉ ((𝔠₀ k).support : Set S₁.last) := by
    intro k h
    apply h𝔠 k
    have h' : genericPoint S₁.last ∈ ((𝔠 k).comap S₁.composite).support := by
      rw [← h𝔠₀ k]
      exact h
    rw [Scheme.IdealSheafData.support_comap] at h'
    have h'' : S₁.composite (genericPoint S₁.last) ∈ ((𝔠 k).support : Set X) := h'
    rwa [dominant_map_genericPoint] at h''
  obtain ⟨Z, hZ⟩ : ∃ Z : Closeds S₁.last,
      (Z : Set S₁.last) = (W₀ : Set S₁.last) ∪ ⋃ k, ((𝔠₀ k).support : Set S₁.last) :=
    ⟨⟨_, W₀.isClosed.union (isClosed_iUnion_of_finite fun k => (𝔠₀ k).support.isClosed)⟩, rfl⟩
  have hZη : genericPoint S₁.last ∉ (Z : Set S₁.last) := by
    rw [hZ]
    rintro (h | h)
    · exact hW₀η h
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
      exact h𝔠₀η k hk
  have h𝔠₀Z : ∀ k, ((𝔠₀ k).support : Set S₁.last) ⊆ (Z : Set S₁.last) := by
    intro k
    rw [hZ]
    exact (Set.subset_iUnion (fun k => ((𝔠₀ k).support : Set S₁.last)) k).trans
      Set.subset_union_right
  have hsm₀ : Smooth (S₁.last ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth n _
  -- Step 3: principalization of the ideal sheaves and normal crossings of the preimage
  obtain ⟨S₂, hZ₂, hreg₂, hinv, E, hEsnc, hEsupp⟩ : ∃ S₂ : Scheme.BlowUpSequence S₁.last,
      (∀ (i : Fin S₂.length) (z : S₂.stage i.castSucc), z ∈ (S₂.center i).support →
        S₂.stageMap i.castSucc z ∈ (Z : Set S₁.last)) ∧
      IsRegular S₂.last ∧ (∀ k, ((𝔠₀ k).comap S₂.composite).IsInvertible) ∧
      ∃ E : S₂.last.IdealSheafData, E.IsSncBoundary ∧
        (E.support : Set S₂.last) = S₂.composite ⁻¹' (Z : Set S₁.last) :=
    @exists_blowUpSequence_isSncBoundary_isInvertible_comap_family K _ _ κ _ S₁.last hT₀int
      hreg₁ instT₀ hT₀ft hT₀qc hT₀sep Z hZη 𝔠₀ h𝔠₀Z
  have hTint : IsIntegral S₂.last :=
    blowUpSequence_isIntegral_last_of_centers_over S₂ Z hZ₂ hZη
  have hTN : IsLocallyNoetherian S₂.last := isLocallyNoetherian_stage S₂ (Fin.last S₂.length)
  have hπdom : IsDominant S₂.composite :=
    blowUpSequence_isDominant_of_centers_over S₂ Z hZ₂ hZη
  have hπprop : IsProper S₂.composite := S₂.isProper_composite
  let instT : S₂.last.Over (Spec (CommRingCat.of K)) :=
    ⟨S₂.composite ≫ (S₁.last ↘ Spec (CommRingCat.of K))⟩
  have hπover : S₂.composite.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hTsm : SmoothOfRelativeDimension n (S₂.last ↘ Spec (CommRingCat.of K)) :=
    blowUpSequence_smoothOfRelativeDimension_of_centers_over S₂ Z hZ₂ hZη hreg₂ cT₀
  have hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) S₂.composite) :=
    dominantFunctionFieldMap_bijective_of_isIso_stalkMap S₂.composite
      (blowUpSequence_isIso_stalkMap_of_centers_over S₂ Z hZ₂ (genericPoint S₂.last)
        (by rw [dominant_map_genericPoint]; exact hZη))
  have : QuasiCompact (S₂.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact (S₂.composite ≫ (S₁.last ↘ Spec (CommRingCat.of K))))
  have hTc : CompactSpace S₂.last :=
    QuasiCompact.compactSpace_of_compactSpace (S₂.last ↘ Spec (CommRingCat.of K))
  have hTnoeth : IsNoetherian S₂.last := { toIsLocallyNoetherian := hTN, toCompactSpace := hTc }
  obtain ⟨cT⟩ : Nonempty (EtaleChart K S₂.last n) := by
    obtain ⟨w⟩ : Nonempty S₂.last := inferInstance
    exact ⟨Classical.choose (show ∃ e : EtaleChart K S₂.last n, w ∈ e.U from
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S₂.last) (n := n)).symm ▸
        Opens.mem_top w))⟩
  -- the simple normal crossing family: the generic points of the reduced preimage of the
  -- closed set of the round
  have hfin : Finite E.support.genericPoints := inferInstance
  let e : Fin (Nat.card E.support.genericPoints) ≃ E.support.genericPoints :=
    (Finite.equivFin _).symm
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Fin (Nat.card E.support.genericPoints) → S₂.last,
      ξ = fun i => ((e i : E.support.genericPoints) : S₂.last) := ⟨_, rfl⟩
  have hξinj : Function.Injective ξ := by
    rw [hξdef]
    exact fun i j h => e.injective (Subtype.ext h)
  have hξmem : ∀ i, ξ i ∈ E.support.genericPoints := by
    rw [hξdef]
    exact fun i => (e i).2
  have hcoh : ∀ η ∈ E.support.genericPoints, Order.coheight η = 1 := fun η hη =>
    coheight_eq_one_of_mem_genericPoints_of_isSncBoundary E hEsnc hη
  -- a codimension-one point outside the family does not lie over the closed set of the round
  have hnotZ : ∀ t : CodimensionOnePoint S₂.last, (t : S₂.last) ∉ Set.range ξ →
      S₂.composite (t : S₂.last) ∉ (Z : Set S₁.last) := by
    intro t ht hmem
    have htE : (t : S₂.last) ∈ E.support := by
      have h : (t : S₂.last) ∈ (E.support : Set S₂.last) := by
        rw [hEsupp]
        exact hmem
      exact h
    obtain ⟨η, hη, hηt⟩ := Closeds.exists_mem_genericPoints_specializes E.support htE
    have heq : (⟨η, hcoh η hη⟩ : CodimensionOnePoint S₂.last) = t :=
      CodimensionOnePoint.eq_of_specializes (x := t) (y := ⟨η, hcoh η hη⟩) hηt
    apply ht
    refine ⟨e.symm ⟨η, hη⟩, ?_⟩
    rw [hξdef]
    change ((e (e.symm ⟨η, hη⟩) : E.support.genericPoints) : S₂.last) = (t : S₂.last)
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val heq
  have hnotW : ∀ t : CodimensionOnePoint S₂.last, (t : S₂.last) ∉ Set.range ξ →
      S₂.composite (t : S₂.last) ∉ (W₀ : Set S₁.last) := fun t ht h =>
    hnotZ t ht (by rw [hZ]; exact Or.inl h)
  -- hence the second model is an isomorphism on the stalks there
  have hstalk : ∀ t : CodimensionOnePoint S₂.last, (t : S₂.last) ∉ Set.range ξ →
      Function.Bijective (S₂.composite.stalkMap (t : S₂.last)) ∧
        Order.coheight (S₂.composite (t : S₂.last)) = 1 := by
    intro t ht
    have hiso : IsIso (S₂.composite.stalkMap (t : S₂.last)) :=
      blowUpSequence_isIso_stalkMap_of_centers_over S₂ Z hZ₂ (t : S₂.last) (hnotZ t ht)
    have hbij : Function.Bijective (S₂.composite.stalkMap (t : S₂.last)) :=
      ConcreteCategory.bijective_of_isIso _
    refine ⟨hbij, ?_⟩
    rw [← coheight_eq_of_stalkMap_bijective S₂.composite (t : S₂.last) hbij]
    exact t.property
  -- Both rounds are one finite succession of blow-ups of X, hence a single blow-up up to
  -- isomorphism. This retains projectivity without assuming a composition theorem for
  -- arbitrary projective morphisms over a non-affine base.
  have hρprojective : IsProjective (S₂.composite ≫ S₁.composite) := by
    subst hS₁
    simpa only [Scheme.BlowUpSequence.composite, Scheme.BlowUpSequence.last,
      Scheme.BlowUpSequence.length, Fin.last, Scheme.BlowUpSequence.stage,
      Scheme.BlowUpSequence.stageMap, Category.id_comp, Category.comp_id] using
      (Scheme.BlowUpSequence.cons X D₀ S₂).isProjective_composite
  refine ⟨S₂.last, hTint, instT, hTnoeth, hTsm, S₂.composite ≫ S₁.composite, inferInstance,
    inferInstance, inferInstance, hρprojective,
    dominantFunctionFieldAlgHom_comp_bijective S₁.composite S₂.composite hρ₀ hπ, cT,
    Nat.card E.support.genericPoints, ξ, hξinj, fun i => hcoh _ (hξmem i),
    isSNCFamily_of_isSncBoundary E hEsnc ξ hξinj hξmem, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hbij, hcoht⟩ := hstalk t ht
    have hcomp := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective S₁.composite
      S₂.composite hρ₀ hπ c f d D cT₀ cT t hcoht hbij
    have h0 := cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds
      (crepantBoundaryCartier S₁.composite hρ₀ c f d D cT₀ etaleCharts_cover)
      (S₂.composite (t : S₂.last)) hcoht
      (fun h => hnotW t ht (by rw [hW₀]; exact Or.inl h))
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, neg_eq_zero] at h0
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hcomp, h0, neg_zero]
  · intro j t ht
    obtain ⟨hbij, hcoht⟩ := hstalk t ht
    have : Smooth (S₂.last ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    have : Smooth (S₁.last ↘ Spec (CommRingCat.of K)) := hsm₀
    have := smoothOverField_codimensionOne_stalk_DVR (K := K)
      (⟨S₂.composite (t : S₂.last), hcoht⟩ : CodimensionOnePoint S₁.last)
    have := smoothOverField_codimensionOne_stalk_DVR (K := K) t
    rw [cartierPullback_comp S₁.composite S₂.composite (G j),
      cartierCoefficient_pullback_of_stalkMap_bijective S₂.composite t hcoht hbij]
    exact cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds _ _ hcoht
      (fun h => hnotW t ht (by rw [hW₀]; exact Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩)))
  · -- both rounds are one succession of blow-ups of X, whose last stage embeds with X
    intro N e he hebase
    exact blowUpSequence_two_step_exists_closedImmersion_of_eq e hebase D₀ S₁ hS₁ S₂
  · -- the invertible inverse image of each ideal sheaf is the ideal sheaf of an effective
    -- Cartier divisor, whose prime components lie over the support of the ideal sheaf
    have hTsep : IsSeparated (S₂.last ↘ Spec (CommRingCat.of K)) :=
      inferInstanceAs (IsSeparated (S₂.composite ≫ (S₁.last ↘ Spec (CommRingCat.of K))))
    have hcomap : ∀ k, (𝔠 k).comap (S₂.composite ≫ S₁.composite) =
        (𝔠₀ k).comap S₂.composite := by
      intro k
      rw [h𝔠₀ k, Scheme.IdealSheafData.comap_comp]
    have hoff : ∀ (k : κ) (t : CodimensionOnePoint S₂.last), (t : S₂.last) ∉ Set.range ξ →
        (t : S₂.last) ∉ ((𝔠₀ k).comap S₂.composite).support := by
      intro k t ht hmem
      rw [Scheme.IdealSheafData.support_comap] at hmem
      have h' : S₂.composite (t : S₂.last) ∈ ((𝔠₀ k).support : Set S₁.last) := hmem
      exact hnotZ t ht (by rw [hZ]; exact Or.inr (Set.mem_iUnion.mpr ⟨k, h'⟩))
    refine ⟨fun k t ht => ?_, fun k => ?_⟩
    · rw [hcomap k]
      exact hoff k t ht
    · have hinvk : ((𝔠 k).comap (S₂.composite ≫ S₁.composite)).IsInvertible := by
        rw [hcomap k]
        exact hinv k
      obtain ⟨Gc, hGc, hGcI, hGc0⟩ :=
        @exists_effectiveCartier_of_invertibleIdeal_coefficient_of_overField S₂.last hTint hTN K
          _ instT hTsep ((𝔠₀ k).comap S₂.composite) (hinv k)
      exact ⟨hinvk, (Scheme.IdealSheafData.blowUp.isBlowUp (𝔠 k)).exists_lift _ hinvk,
        Gc, hGc, hGcI.trans (hcomap k).symm, fun t ht => hGc0 (t : S₂.last) (hoff k t ht)⟩

/-- A projective simple normal crossing model of a log pair and finitely many further Cartier
divisors exists: a smooth T of relative dimension n with a projective birational morphism to X
and a simple normal crossing family of codimension-one points outside of which the crepant
boundary and the pullbacks of the further divisors have coefficient zero. Moreover every closed
immersion of X into a projective space over the base field gives a closed immersion of T into a
projective space over the base field. -/
theorem exists_projective_snc_model_with_embedding {ι : Type*} [Finite ι] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (G : ι → CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      ∀ (N : ℕ) (e : X ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
        e ≫ polynomialProjectiveToBase N K = X ↘ Spec (CommRingCat.of K) →
        ∃ (M : ℕ) (e' : T ⟶ polynomialProjectiveScheme M K), IsClosedImmersion e' ∧
          e' ≫ polynomialProjectiveToBase M K = T ↘ Spec (CommRingCat.of K) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, hemb, -⟩ := exists_projective_snc_model_principalizing c f d D G
      (fun k : PEmpty.{1} => k.elim) (fun k => k.elim)
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, hemb⟩

/-- A projective simple normal crossing model of a log pair and finitely many further Cartier
divisors exists: a smooth T of relative dimension n with a projective birational morphism to X
and a simple normal crossing family of codimension-one points outside of which the crepant
boundary and the pullbacks of the further divisors have coefficient zero. -/
theorem exists_projective_snc_model_with {ι : Type*} [Finite ι] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (G : ι → CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      ∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0 := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, -⟩ := exists_projective_snc_model_with_embedding c f d D G
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG⟩

/-- If X carries an ample Cartier divisor, the simple normal crossing model carries a very
ample Cartier divisor: the model is a closed subscheme of a projective space over the base
field. No ample divisor on the model is assumed. -/
theorem exists_projective_snc_model_with_ample {ι : Type*} [Finite ι] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (G : ι → CartierDivisor X)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      ∃ J : CartierDivisor T, CartierIsVeryAmpleProj K J := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, hemb⟩ := exists_projective_snc_model_with_embedding c f d D G
  obtain ⟨m, -, N, e, he, hbase, -⟩ := hH
  obtain ⟨M, e', he', hbase'⟩ := hemb N e he hbase
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp, hG,
    exists_cartierIsVeryAmpleProj_of_closedImmersion e' hbase'⟩

/-- The proper-model interface follows from the projective-model construction, retaining the
original interface for discrepancy descent and perturbations. -/
theorem exists_proper_snc_model_with {ι : Type*} [Finite ι] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (G : ι → CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      ∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0 := by
  obtain ⟨T, hT, hTover, hTN, hTsm, ρ, hdom, hover, hproper, hprojective, hρ,
    cT, r, ξ, hξ⟩ := exists_projective_snc_model_with c f d D G
  exact ⟨T, hT, hTover, hTN, hTsm, ρ, hdom, hover, hproper, hρ, cT, r, ξ, hξ⟩

/-- A projective simple normal crossing model of a log pair exists, with no extra Cartier
divisors prescribed. Projectivity here is relative to X, in the projective-bundle sense. -/
theorem exists_projective_snc_model (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0 := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, -⟩ :=
    exists_projective_snc_model_with c f d D (fun i : PEmpty.{1} => i.elim)
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩

/-- A proper simple normal crossing model of a log pair exists: a smooth T of relative dimension n
with a proper birational morphism to X and a simple normal crossing family of codimension-one
points outside of which the crepant boundary has coefficient zero. -/
theorem exists_proper_snc_model (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor X) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0 := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, -⟩ := exists_proper_snc_model_with c f d D (fun i : PEmpty.{1} => i.elim)
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp⟩

/-- A log pair is klt on all proper smooth birational models if and only if it has a proper simple
normal crossing model on which the finitely many coefficients of the crepant boundary are smaller
than the denominator; such a model always exists. -/
theorem logPairIsKlt_iff_exists_snc_model_coefficients (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) :
    LogPairIsKlt c f d D ↔
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (ξ i) < (d : ℤ) := by
  constructor
  · intro hklt
    obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp⟩ := exists_proper_snc_model c f d D
    exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp,
      (logPairIsKlt_iff_crepant_snc_coefficients ρ hρ c f d hd D cT ξ hinj hcoh hsnc
        hsupp).mp hklt⟩
  · rintro ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, hb⟩
    exact logPairIsKlt_of_crepant_snc_model ρ hρ c f d hd D cT ξ hinj hcoh hsnc hsupp hb

end Existence

end MixedFujita

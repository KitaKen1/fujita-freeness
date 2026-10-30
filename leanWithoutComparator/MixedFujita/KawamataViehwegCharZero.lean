/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreModelVanishing
public import MixedFujita.ModelCocycleVanishing
public import MixedFujita.FibreBoundaryPoints
public import MixedFujita.ModelAssemblyLemmas
public import MixedFujita.ClosureAmpleRelation
public import MixedFujita.AmpleRelationNormalization
public import MixedFujita.AmpleChartRelation
public import MixedFujita.GenericSmoothSpreading
public import MixedFujita.HigherAmpleKawamataViehweg
public import MixedFujita.ProjectiveKawamataViehwegOfAmple
public import MixedFujita.ProperKawamataViehwegReduction
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.SNCComponentCartier
public import MixedFujita.ActualCartierSerreVanishing
public import MixedFujita.CartierSectionDivisor
public import MixedFujita.ProjectiveClosureFibreIntegral
public import MixedFujita.ProjectiveClosureProperties

/-!
Kawamata–Viehweg vanishing in characteristic zero, and the mixed Fujita freeness theorem (step 10,
R4-7).

Let `T` be smooth and projective over an algebraically closed field `K` of characteristic zero,
with a simple normal crossing family `E_k`, and `Q` with `m (Q − K_T) − Σ_k a_k E_k` ample,
`0 ≤ a_k < m`. Then `Hʲ(T, 𝒪(Q)) = 0` for every `j ≥ 1`
(`kawamataViehwegVanishingSNCAmpleInDegree_of_charZero`):
* on `T`: the ample relation in a closed embedding, an atlas of simple normal crossing charts basic
  in the standard charts on which `Q` has one local equation (check 534), the normalization of the
  relation and of `Q` at the first chart (checks 541, 542), the cocycle of `Q`, and the ratios of the
  boundary coordinates (check 547);
* a finitely generated subring `B` over which the closure is a model of `T` with integral fibres,
  smooth, and covered by the basic opens of the atlas (checks 508, 510, 517, 523, 532), and a
  larger subring `A`, smooth over `ℤ` (check 505), over which the étale coordinates, the cocycle and
  the units of the relations spread (checks 535, 536);
* a closed point of `Spec A` avoiding finitely many nonzero elements (check 557): a finite residue
  field `κ` of characteristic `p > n` (check 501) with a lift `A → W₂(κ)` (check 519);
* on the closed fibre: the charts (checks 522, 526), the boundary points of codimension one in
  simple normal crossing position (check 556) with their divisors, the relation (checks 545, 546),
  and Kawamata–Viehweg vanishing from the Deligne–Illusie lift data (checks 551–554);
* the transfer to `T` (checks 553, 555) and the principal shift back to `Q`.
With checks 467–475 this gives Kawamata–Viehweg vanishing in the projective, proper and sum forms
(`kawamataViehwegVanishingSNCProjective_of_charZero`, `kawamataViehwegVanishingSNC_of_charZero`,
`kawamataViehwegVanishingSNCSum_of_charZero`) and the mixed Fujita freeness theorem F1
(`mixedFujitaFreeness_proved`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra structureSectionsAlgebra sectionsRingModule
  Classical.propDecidable

universe u

/-- Finitely many finitely generated subalgebras lie in a finitely generated one. -/
theorem exists_fg_upperBound {K : Type u} [Field K] {ι : Type*} [Fintype ι]
    (A₀ : ι → Subalgebra ℤ K) (h : ∀ i, (A₀ i).FG) :
    ∃ B : Subalgebra ℤ K, B.FG ∧ ∀ i, A₀ i ≤ B := by
  classical
  refine ⟨Finset.univ.sup A₀, ?_, fun i => Finset.le_sup (Finset.mem_univ i)⟩
  have : ∀ t : Finset ι, (t.sup A₀).FG := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using Subalgebra.fg_bot
    | insert i t _ ih =>
      rw [Finset.sup_insert]
      exact (h i).sup ih
  exact this _

/-- The functions on an affine open of a scheme locally of finite presentation over `A` are a
finitely presented `A`-algebra. -/
theorem finitePresentation_sections_of_locallyOfFinitePresentation {A : Type u} [CommRing A]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))]
    [LocallyOfFinitePresentation (X ↘ Spec (CommRingCat.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) :
    letI := structureSectionsAlgebra A X V
    Algebra.FinitePresentation A Γ(X, V) := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation (X ↘ Spec (CommRingCat.of A))
    inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h2 : RingHom.FinitePresentation (((X ↘ Spec (CommRingCat.of A)).appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) :=
    (RingHom.finitePresentation_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv _).2 h
  let _ := structureSectionsAlgebra A X V
  have h3 : RingHom.FinitePresentation (algebraMap A Γ(X, V)) := by
    have := structureSections_algebraMap A X V
    rw [← CommRingCat.hom_ofHom (algebraMap A Γ(X, V)), this]
    exact h2
  exact RingHom.finitePresentation_algebraMap.mp h3

/-- On an integral scheme the Čech intersections of nonempty opens are nonempty. -/
theorem nonempty_cechOpen_of_isIntegral {X : Scheme.{u}} [IsIntegral X] {ι : Type*}
    (U : ι → X.Opens) (hU : ∀ i, Nonempty (U i)) :
    ∀ {m : ℕ} (x : Fin (m + 1) → ι), Nonempty (TopCat.Presheaf.cechOpen U x)
  | 0, x => by
    rw [show TopCat.Presheaf.cechOpen U x = U (x 0) from
      le_antisymm (TopCat.Presheaf.cechOpen_le U x 0)
        (le_iInf fun a ↦ by rw [Fin.fin_one_eq_zero a])]
    exact hU _
  | m + 1, x => by
    rw [← Fin.cons_self_tail x, TopCat.Presheaf.cechOpen_cons_eq]
    have := hU (x 0)
    have := nonempty_cechOpen_of_isIntegral U hU (Fin.tail x)
    exact integral_opens_inter_nonempty X _ _

set_option maxHeartbeats 4000000 in
/-- **Kawamata–Viehweg vanishing for an ample adjoint with simple normal crossing boundary, in
characteristic zero, in every positive cohomological degree.** -/
theorem kawamataViehwegVanishingSNCAmpleInDegree_of_charZero (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] (n cohDegree : ℕ) (hdegree : 1 ≤ cohDegree) :
    KawamataViehwegVanishingSNCAmpleInDegree K n cohDegree := by
  intro T _ _ _ _ _ cT r ξ hinj hξ hsnc E hEc Q m hm a ha hamp
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => by have := hnormT (z : T); exact normal_codimensionOne_stalk_DVR z
  obtain ⟨m', hm', P, e, he_imm, he, g, hg, hggen, f, hmA⟩ := hamp
  -- an atlas trivializing Q, basic in the standard charts
  choose mm c σ s q hc hcU hspan hq using fun k : Fin P =>
    exists_finite_snc_chart_span_isLocalEquationAt e hsnc Q k
  -- the flat index
  have hιne : Nonempty (Σ k : Fin P, Fin (mm k)) := by
    obtain ⟨k, j, -⟩ := exists_mem_basicOpen_of_span e s hspan (genericPoint T)
    exact ⟨⟨k, j⟩⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Σ k : Fin P, Fin (mm k)) = N + 1 :=
    ⟨_, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
  let eqv : Fin (N + 1) ≃ Σ k : Fin P, Fin (mm k) := (Fintype.equivFinOfCardEq hN).symm
  -- the base ring
  obtain ⟨B₁, hB₁, HB₁⟩ := exists_fg_forall_isPullback_projectiveClosure (T ↘ Spec (CommRingCat.of K)) e he
  obtain ⟨B₂, hB₂, HB₂⟩ := exists_fg_forall_smoothOfRelativeDimension_projectiveClosure (T ↘ Spec (CommRingCat.of K)) n e
    he
  obtain ⟨B₃, hB₃, HB₃⟩ := exists_fg_forall_exists_ne_zero_isIntegral_fibre (T ↘ Spec (CommRingCat.of K)) n e he
  choose B₄ hB₄ HB₄ using fun k : Fin r =>
    exists_fg_forall_exists_ne_zero_isIntegral_boundaryFibre e ξ he hsnc k
  obtain ⟨B₄', hB₄', hB₄le⟩ := exists_fg_upperBound B₄ hB₄
  obtain ⟨B₅, hB₅, HB₅⟩ := exists_fg_forall_iSup_basicOpen_eq_top e s hspan
  have hB₆ : (Algebra.adjoin ℤ {((n.factorial : K))⁻¹}).FG :=
    ⟨{((n.factorial : K))⁻¹}, by simp⟩
  obtain ⟨B, hBfg, hB⟩ := exists_fg_upperBound
    ![B₁, B₂, B₃, B₄', B₅, Algebra.adjoin ℤ {((n.factorial : K))⁻¹}]
    (fun i => by fin_cases i <;> assumption)
  have hB1 : B₁ ≤ B := hB 0
  have hB2 : B₂ ≤ B := hB 1
  have hB3 : B₃ ≤ B := hB 2
  have hB4 : ∀ k, B₄ k ≤ B := fun k => (hB₄le k).trans (hB 3)
  have hB5 : B₅ ≤ B := hB 4
  have hB6 : Algebra.adjoin ℤ {((n.factorial : K))⁻¹} ≤ B := hB 5
  have HB := HB₁ B hB1
  obtain ⟨sB, hsB, hcovB⟩ := HB₅ B hB5
  have : IsAffineHom (projectiveClosureMap (algebraMap B K) e) :=
    projectiveClosureMap_isAffineHom e _
  have hpre : ∀ k j, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB k j) = (c k j).U := by
    intro k j
    rw [preimage_basicOpen_closureChartMap, hsB, hcU]
  have hUBaff : ∀ k j, IsAffineOpen ((projectiveClosure (algebraMap B K) e).basicOpen (sB k j)) :=
    fun k j => (projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion
      (projectiveClosureι (algebraMap B K) e) k).basicOpen (sB k j)
  -- the charts of T on the preimages of the basic opens of the base model
  let c₂ : Fin (N + 1) → EtaleChart K T n := fun i =>
    etaleChartRestrict (c (eqv i).1 (eqv i).2)
      (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))
      ((hUBaff _ _).preimage _) (by rw [hpre]; exact (c _ _).nonempty) (hpre _ _).le
  let σ₂ : Fin (N + 1) → Fin r → Option (Fin n) := fun i k =>
    if ξ k ∈ (c₂ i).U then σ (eqv i).1 (eqv i).2 k else none
  have hc₂ : ∀ i, IsSNCChart (c₂ i) ξ (σ₂ i) := fun i =>
    (isSNCChart_normalize (isSNCChart_etaleChartRestrict (hc (eqv i).1 (eqv i).2) _ _ _ _)).1
  have hσ₂ : ∀ i k a, σ₂ i k = some a → ξ k ∈ (c₂ i).U := fun i =>
    (isSNCChart_normalize (isSNCChart_etaleChartRestrict (hc (eqv i).1 (eqv i).2) _ _ _ _)).2
  have hq₂ : ∀ i, ∀ y ∈ (c₂ i).U, Q.IsLocalEquationAt y (q (eqv i).1 (eqv i).2) :=
    fun i y hy => hq (eqv i).1 (eqv i).2 y ((hpre _ _).le hy)
  have hcov₂ : ∀ x : T, ∃ i, x ∈ (c₂ i).U := by
    intro x
    obtain ⟨k, j, hx⟩ := exists_mem_basicOpen_of_span e s hspan x
    refine ⟨eqv.symm ⟨k, j⟩, ?_⟩
    change x ∈ (fun t : Σ k : Fin P, Fin (mm k) => projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB t.1 t.2)) (eqv (eqv.symm ⟨k, j⟩))
    rw [Equiv.apply_symm_apply]
    change x ∈ projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB k j)
    rw [hpre, hcU]
    exact hx
  have hcoverT : iSup (fun c : EtaleChart K T n => c.U) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hcov₂ x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c₂ i, hi⟩
  have hUk : ∀ i, (c₂ i).U ≤ projectivePullbackCoordinateOpen e (eqv i).1 := fun i =>
    ((hpre _ _).le).trans ((hcU _ _).le.trans (T.basicOpen_le _))
  have : Nonempty (projectivePullbackCoordinateOpen e (eqv 0).1) :=
    ⟨⟨(Classical.arbitrary (c₂ 0).U).1, hUk 0 (Classical.arbitrary (c₂ 0).U).2⟩⟩
  have hk₀ := X_notMem_genericPoint_of_nonempty e (eqv 0).1
  -- the cocycle of Q on T and the normalized divisor Q'
  choose wT hwT using fun i j =>
    @exists_unit_germ_eq_of_isLocalEquationAt T _ Q ((c₂ i).U ⊓ (c₂ j).U)
      (integral_opens_inter_nonempty T _ _) (q (eqv i).1 (eqv i).2) (q (eqv j).1 (eqv j).2)
      (fun y hy => hq₂ i y hy.1) (fun y hy => hq₂ j y hy.2)
  have hw := isCocycleZero_of_germ (fun i => (c₂ i).U) (fun i => q (eqv i).1 (eqv i).2) wT hwT
  have hQ' := isLocalEquationAt_shift_cocycleEquation (fun i => (c₂ i).U)
    (fun i => q (eqv i).1 (eqv i).2) hq₂ wT hwT
  obtain ⟨f'', hf''⟩ := exists_eq_hyperplane_add_principal_normalize e cT (c₂ 0) hcoverT E Q m m'
    a g hg hggen f hmA (q (eqv 0).1 (eqv 0).2) (eqv 0).1 hk₀
  have hgQ0 : cocycleEquation (fun i => (c₂ i).U) wT 0 = 1 := by
    apply Units.ext
    have h00 := hwT 0 0
    rw [mul_inv_cancel, Units.val_one] at h00
    exact h00
  obtain ⟨wK, hwK⟩ := exists_chartRelation_of_eq_hyperplane_add_principal hnormT ξ hinj hξ E hEc e
    c₂ σ₂ hc₂ hcoverT (fun i => (eqv i).1) hUk (Q + principalCartierDivisor T
      (q (eqv 0).1 (eqv 0).2)⁻¹) (cocycleEquation (fun i => (c₂ i).U) wT) hQ' hgQ0 m m' a f'' hk₀
    hf''
  -- the ratios of the boundary coordinates on T
  choose bT hbT using fun a b k => exists_boundaryRatio_unit hnormT ξ hinj hξ E hEc (c₂ a) (c₂ b)
    (σ₂ a) (σ₂ b) (hc₂ a) (hc₂ b) k
  -- spreading to a larger ring
  have : IsAffineHom (pullback.diagonal (terminal.from (projectiveClosure (algebraMap B K) e))) :=
    projectiveClosure_isAffineHom_diagonal _ e
  have hUBne : ∀ i, Nonempty (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) :=
    fun i => (c₂ i).nonempty
  have hUBne2 : ∀ a b, Nonempty (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
      ((projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))) :=
    fun a b => integral_opens_inter_nonempty T (c₂ a).U (c₂ b).U
  choose A₆ hA₆ HA₆ using fun i : Fin (N + 1) =>
    exists_fg_forall_etale_closureTransition e he B HB (eqv i).1 (sB (eqv i).1 (eqv i).2)
      (c₂ i).coords (etaleChart_coords_etale (c₂ i))
  obtain ⟨A₇, hA₇, HA₇⟩ := exists_fg_forall_cocycle_closureTransition e he B HB
    (fun i => (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))
    (fun i j => (hUBaff _ _).inf (hUBaff _ _)) wT hw
  choose A₈ hA₈ HA₈ using fun i : Fin (N + 1) =>
    exists_fg_forall_unit_closureTransition e he B HB (hUBaff (eqv i).1 (eqv i).2) {wK i}
  choose A₉ hA₉ HA₉ using fun ab : Fin (N + 1) × Fin (N + 1) =>
    exists_fg_forall_unit_closureTransition e he B HB ((hUBaff _ _).inf (hUBaff _ _))
      (Finset.univ.image fun k => (bT ab.1 ab.2 k : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ
        ((projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv ab.1).1 (eqv ab.1).2) ⊓
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv ab.2).1 (eqv ab.2).2)))ˣ))
  obtain ⟨A₆', hA₆', hA₆le⟩ := exists_fg_upperBound A₆ hA₆
  obtain ⟨A₈', hA₈', hA₈le⟩ := exists_fg_upperBound A₈ hA₈
  obtain ⟨A₉', hA₉', hA₉le⟩ := exists_fg_upperBound A₉ hA₉
  obtain ⟨A₀, hA₀fg, hA₀⟩ := exists_fg_upperBound ![B, A₆', A₇, A₈', A₉']
    (fun i => by fin_cases i <;> assumption)
  obtain ⟨A, hA₀A, hAfg, hAsm⟩ := exists_fg_smooth_int_of_charZero A₀ hA₀fg
  have hBA : B ≤ A := (hA₀ 0).trans hA₀A
  have hA6 : ∀ i, A₆ i ≤ A := fun i => (hA₆le i).trans ((hA₀ 1).trans hA₀A)
  have hA7 : A₇ ≤ A := (hA₀ 2).trans hA₀A
  have hA8 : ∀ i, A₈ i ≤ A := fun i => (hA₈le i).trans ((hA₀ 3).trans hA₀A)
  have hA9 : ∀ ab, A₉ ab ≤ A := fun ab => (hA₉le ab).trans ((hA₀ 4).trans hA₀A)
  -- the model over A
  let _ := projectiveClosureOver e (algebraMap A K)
  have HA := HB₁ A (hB1.trans hBA)
  have : SmoothOfRelativeDimension n
      (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A)) := HB₂ A (hB2.trans hBA)
  have : Smooth (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A)) :=
    SmoothOfRelativeDimension.smooth n _
  have : IsProper (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A)) :=
    projectiveClosure_toBase_isProper _ e
  have : IsAffineHom (pullback.diagonal (terminal.from (projectiveClosure (algebraMap A K) e))) :=
    projectiveClosure_isAffineHom_diagonal _ e
  have : IsIntegral (projectiveClosure (algebraMap A K) e) :=
    projectiveClosure_isIntegral_of_isClosedImmersion e (algebraMap A K)
  have : IsAffineHom (projectiveClosureMap (algebraMap A K) e) :=
    projectiveClosureMap_isAffineHom e _
  have hψ' := fun i => HA₆ i A hBA (hA6 i)
  dsimp only at hψ'
  choose ψ hψet hψ using hψ'
  obtain ⟨wA, hwA, hwAT⟩ := HA₇ A hBA hA7
  choose wAm hwAm using fun i => HA₈ i A hBA (hA8 i) (wK i) (Finset.mem_singleton_self _)
  choose bA hbA using fun a b k => HA₉ (a, b) A hBA (hA9 (a, b)) (bT a b k)
    (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  -- the atlas of the model over A
  have : IsAffineHom (closureTransitionOfLE e hBA) := closureTransition_isAffineHom e _ _ _ _
  have hV : ∀ i, IsAffineOpen (closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) :=
    fun i => (hUBaff _ _).preimage _
  have hφpre : ∀ i, projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) = (c₂ i).U :=
    fun i => projectiveClosureMap_preimage_closureTransitionOfLE e hBA _
  have hcovUB : ⨆ i, (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) =
      ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ⨆ k, ⨆ j, (projectiveClosure (algebraMap B K) e).basicOpen (sB k j) := by
      rw [hcovB]
      trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hk
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨eqv.symm ⟨k, j⟩, ?_⟩
    change x ∈ (fun t : Σ k : Fin P, Fin (mm k) =>
      (projectiveClosure (algebraMap B K) e).basicOpen (sB t.1 t.2)) (eqv (eqv.symm ⟨k, j⟩))
    rw [Equiv.apply_symm_apply]
    exact hj
  have hcovV : ⨆ i, closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcovUB, Scheme.Hom.preimage_top]
  have hVk : ∀ i, closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ≤
      projectivePullbackCoordinateOpen (projectiveClosureι (algebraMap A K) e) (eqv i).1 := by
    intro i
    exact (Scheme.Hom.preimage_mono _ ((projectiveClosure (algebraMap B K) e).basicOpen_le _)).trans
      (closureTransition_preimage_chart e _ _ _ _ (eqv i).1).le
  have hVne : ∀ i, Nonempty (closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) := by
    intro i
    obtain ⟨⟨x, hx⟩⟩ := (c₂ i).nonempty
    rw [← hφpre i] at hx
    exact ⟨⟨_, hx⟩⟩
  -- the opens away from the boundary
  have hψne : ∀ i j, ψ i (MvPolynomial.X j) ≠ 0 := by
    intro i j h0
    have h := hψ i j
    rw [h0, map_zero] at h
    exact etaleChart_coordinate_ne_zero (c₂ i) j h.symm
  have hV'ne : ∀ i, Nonempty ((projectiveClosure (algebraMap A K) e).basicOpen
      (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j))) := by
    intro i
    have := hVne i
    have hprod : (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hψne i j
    have hbot := (AlgebraicGeometry.basicOpen_eq_bot_iff _).not.mpr hprod
    exact (TopologicalSpace.Opens.nonempty_coeSort).mpr
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hbot)
  -- elements away from which the fibres are good
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  obtain ⟨f₁, hf₁, Hf₁⟩ := HB₃ A (hB3.trans hBA) hAfg
  choose f₂ hf₂ Hf₂ using fun k => HB₄ k A ((hB4 k).trans hBA) hAfg
  choose f₃ hf₃ Hf₃ using fun i => exists_ne_zero_forall_nonempty_preimage_fibre
    (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A)) (hV i)
    (Classical.arbitrary (closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))).1
    (Classical.arbitrary (closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))).2
  choose f₄ hf₄ Hf₄ using fun i => exists_ne_zero_forall_nonempty_preimage_fibre
    (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A)) ((hV i).basicOpen _)
    (Classical.arbitrary ((projectiveClosure (algebraMap A K) e).basicOpen
      (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j)))).1
    (Classical.arbitrary ((projectiveClosure (algebraMap A K) e).basicOpen
      (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j)))).2
  have hF : f₁ * (∏ k, f₂ k) * (∏ i, f₃ i) * (∏ i, f₄ i) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hf₁ ?_) ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun k _ => hf₂ k
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hf₃ i
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hf₄ i
  -- the closed point
  obtain ⟨𝔪, h𝔪, hF𝔪⟩ := exists_isMaximal_notMem hF
  have : Finite 𝔪.ResidueField := finite_residueField_of_isMaximal 𝔪
  have hFκ : algebraMap A 𝔪.ResidueField (f₁ * (∏ k, f₂ k) * (∏ i, f₃ i) * (∏ i, f₄ i)) ≠ 0 :=
    fun h0 => hF𝔪 (Ideal.algebraMap_residueField_eq_zero.mp h0)
  simp only [map_mul, map_prod] at hFκ
  have hu₁ : IsUnit (algebraMap A 𝔪.ResidueField f₁) :=
    (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hFκ))).isUnit
  have hu₂ : ∀ k, IsUnit (algebraMap A 𝔪.ResidueField (f₂ k)) := fun k =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul
      (left_ne_zero_of_mul hFκ))) k (Finset.mem_univ k)).isUnit
  have hu₃ : ∀ i, IsUnit (algebraMap A 𝔪.ResidueField (f₃ i)) := fun i =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hFκ)) i
      (Finset.mem_univ i)).isUnit
  have hu₄ : ∀ i, IsUnit (algebraMap A 𝔪.ResidueField (f₄ i)) := fun i =>
    (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hFκ) i (Finset.mem_univ i)).isUnit
  -- the residue characteristic
  have : CharP 𝔪.ResidueField (ringChar 𝔪.ResidueField) := ringChar.charP _
  have hp : (ringChar 𝔪.ResidueField).Prime := CharP.char_is_prime 𝔪.ResidueField _
  have : Fact (ringChar 𝔪.ResidueField).Prime := ⟨hp⟩
  have hnu : IsUnit ((n.factorial : ℕ) : A) := by
    have hmem : ((n.factorial : K))⁻¹ ∈ A :=
      (hB6.trans hBA) (Algebra.subset_adjoin (Set.mem_singleton _))
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    have hne : ((n.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    change ((n.factorial : ℕ) : K) * ((n.factorial : K))⁻¹ = 1
    exact mul_inv_cancel₀ hne
  have hpn : n < ringChar 𝔪.ResidueField := by
    have hnκ : ((n.factorial : ℕ) : 𝔪.ResidueField) ≠ 0 := by
      have := (hnu.map (algebraMap A 𝔪.ResidueField)).ne_zero
      simpa using this
    by_contra hle
    push Not at hle
    have hdvd : ringChar 𝔪.ResidueField ∣ n.factorial := (Nat.Prime.dvd_factorial hp).mpr hle
    exact hnκ ((CharP.cast_eq_zero_iff 𝔪.ResidueField _ _).mpr hdvd)
  -- the lift of the residue map to W₂
  obtain ⟨ψW, hψW⟩ := exists_wittTwo_lift (ringChar 𝔪.ResidueField) 𝔪.ResidueField
    (algebraMap A 𝔪.ResidueField)
  let _ : Algebra A (WittTwo (ringChar 𝔪.ResidueField) 𝔪.ResidueField) := ψW.toAlgebra
  have hW : ∀ a : A, wittTwoReduction (ringChar 𝔪.ResidueField) 𝔪.ResidueField
      (algebraMap A (WittTwo (ringChar 𝔪.ResidueField) 𝔪.ResidueField) a) =
        algebraMap A 𝔪.ResidueField a := fun a => RingHom.congr_fun hψW a
  -- the closed fibre
  have hψFE : ∀ i, (ψ i).toRingHom.FormallyEtale := fun i =>
    @Algebra.Etale.formallyEtale _ _ _ _ _ (hψet i)
  let Y := pullback (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
    (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField)))
  let _ : Y.Over (Spec (CommRingCat.of 𝔪.ResidueField)) := ⟨pullback.snd _ _⟩
  have Hk : IsPullback (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
      (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField))
      (projectiveClosure (algebraMap A K) e ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) :=
    IsPullback.of_hasPullback _ _
  have : IsIntegral Y := Hf₁ 𝔪.ResidueField hu₁
  have : SmoothOfRelativeDimension n
      (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A) :=
    HB₂ A (hB2.trans hBA)
  have : IsProper (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A) :=
    projectiveClosure_toBase_isProper _ e
  have : SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField)) := by
    change SmoothOfRelativeDimension n (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  have : Smooth (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField)) := SmoothOfRelativeDimension.smooth n _
  have : IsProper (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField)) := by
    change IsProper (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField))
  have : IsAffineHom (pullback.diagonal (terminal.from Y)) :=
    isAffineHom_diagonal_terminal_of_separated_toSpec (Y ↘ Spec (CommRingCat.of 𝔪.ResidueField))
  have : IsAffineHom (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField)))) :=
    inferInstance
  have hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) :=
    fun y => smooth_stalk_isIntegrallyClosed (K := 𝔪.ResidueField) y
  have : ∀ z : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (z : Y)) :=
    fun z => by have := hnormY (z : Y); exact normal_codimensionOne_stalk_DVR z
  have hneY : ∀ i, Nonempty (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ
        (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))) :=
    fun i => Hf₃ i 𝔪.ResidueField (hu₃ i)
  have hneY' : ∀ i, Nonempty (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ
        (projectiveClosure (algebraMap A K) e).basicOpen
          (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j))) :=
    fun i => Hf₄ i 𝔪.ResidueField (hu₄ i)
  -- the charts of the generic fibre are those of T
  have hneK : ∀ i, Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))) :=
    fun i => (hφpre i).symm ▸ (c₂ i).nonempty
  have hcK : ∀ i, IsSNCChart (fibreEtaleChart HA (hV i) (ψ i) (hψFE i) (hneK i)) ξ (σ₂ i) := by
    intro i
    refine isSNCChart_congr (c := c₂ i) (hφpre i) (fun a => ?_) (hc₂ i)
    rw [fibreEtaleChart_coords_X]
    have h1 := congrArg (fun t => T.presheaf.map (homOfLE (hφpre i).le).op t) (hψ i a)
    simp only at h1
    exact (appLE_restrict_apply (g := projectiveClosureMap (algebraMap A K) e) _
      (hφpre i).le _).symm.trans h1
  have hσK : ∀ i k a, σ₂ i k = some a → ξ k ∈ projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) :=
    fun i k a h => (hφpre i).symm ▸ hσ₂ i k a h
  -- the boundary of the closed fibre
  have hbint : ∀ k, IsIntegral (boundaryFibre e ξ (algebraMap A K) 𝔪.ResidueField k) := fun k =>
    have := Hf₂ k 𝔪.ResidueField (hu₂ k)
    boundaryFibre_isIntegral e ξ (algebraMap A K) 𝔪.ResidueField k
  have := polynomialProjectiveCoefficientMap_isAffineHom (n := P) (algebraMap A K)
  have hξ' : ∀ k, closure ({boundaryFibrePoint e ξ (algebraMap A K) 𝔪.ResidueField k} : Set Y) =
      (pullback.fst (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
        (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField)))) ⁻¹'
        closure ({projectiveClosureMap (algebraMap A K) e (ξ k)} :
          Set (projectiveClosure (algebraMap A K) e)) := fun k => by
    rw [closure_boundaryFibrePoint, range_boundaryClosureInclusion]
  have hfp : ∀ i, Algebra.FinitePresentation A Γ(projectiveClosure (algebraMap A K) e,
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) :=
    fun i => finitePresentation_sections_of_locallyOfFinitePresentation (hV i)
  have hcsY : ∀ i, IsSNCChart (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY i)
      (fun k => boundaryFibrePoint e ξ (algebraMap A K) 𝔪.ResidueField k) (σ₂ i) := fun i =>
    isSNCChart_fibre HA Hk (hV i) (ψ i) (hψFE i) (hneK i) (hneY i) Subtype.val_injective ξ (σ₂ i)
      (hcK i) (hσK i) _ hξ'
  have hcovY : ∀ y : Y, ∃ i, y ∈ (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY i).U := by
    intro y
    have hy : y ∈ (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
        polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom
          (algebraMap A 𝔪.ResidueField)))) ⁻¹ᵁ ⨆ i, closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) := by
      rw [hcovV]
      trivial
    rw [Scheme.Hom.preimage_iSup] at hy
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact ⟨i, hi⟩
  obtain ⟨hinjY, hcohY, hsncY⟩ := snc_points_of_cover
    (fun k => boundaryFibrePoint e ξ (algebraMap A K) 𝔪.ResidueField k)
    (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY) σ₂ hcsY hcovY
  obtain ⟨E', -, -, hEc'⟩ := exists_snc_component_cartier _ hcohY hsncY
  -- the hypotheses of check 554
  have hcoverY : iSup (fun c : EtaleChart 𝔪.ResidueField Y n => c.U) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hcovY y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hi⟩
  have hcovY' : ⨆ i, (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY i).U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hcovY y
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hunitA : ∀ i, ∀ j ∈ logSetOf (σ₂ i), IsUnit ((projectiveClosure (algebraMap A K) e).presheaf.map
      (homOfLE ((projectiveClosure (algebraMap A K) e).basicOpen_le
        (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j)))).op (ψ i (MvPolynomial.X j))) := by
    intro i j hj
    refine isUnit_of_dvd_unit (map_dvd _
      (Finset.dvd_prod_of_mem (fun j => ψ i (MvPolynomial.X j)) hj)) ?_
    exact (projectiveClosure (algebraMap A K) e).toRingedSpace.isUnit_res_basicOpen _
  have hunitY : ∀ i, ∀ j ∈ logSetOf (σ₂ i), IsUnit ((fibreAtlasRestrictCharts 𝔪.ResidueField Hk hV ψ
      hψFE hneY (fun i => (hV i).basicOpen _)
      (fun i => (projectiveClosure (algebraMap A K) e).basicOpen_le _) hneY' i).coords
        (MvPolynomial.X j)) := by
    intro i j hj
    have h1 : (fibreAtlasRestrictCharts 𝔪.ResidueField Hk hV ψ hψFE hneY
        (fun i => (hV i).basicOpen _)
        (fun i => (projectiveClosure (algebraMap A K) e).basicOpen_le _) hneY' i).coords
          (MvPolynomial.X j) =
        (Y.presheaf.map (homOfLE ((Opens.map (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
          polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom
            (algebraMap A 𝔪.ResidueField)))).base).monotone
              ((projectiveClosure (algebraMap A K) e).basicOpen_le
                (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j))))).op).hom
          ((fibreEtaleChart Hk (hV i) (ψ i) (hψFE i) (hneY i)).coords (MvPolynomial.X j)) := rfl
    rw [h1, fibreEtaleChart_coords_X, appLE_restrict_apply,
      ← appLE_of_restrict_apply (h := (projectiveClosure (algebraMap A K) e).basicOpen_le
        (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j))) le_rfl]
    exact (hunitA i j hj).map _
  -- germs of the spread functions
  have hgerm : ∀ {U : (projectiveClosure (algebraMap A K) e).Opens} {W : T.Opens}
      [Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ U)] [Nonempty W]
      (h : W ≤ projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ U)
      (s : Γ(projectiveClosure (algebraMap A K) e, U)) (t : Γ(T, W)),
      (projectiveClosureMap (algebraMap A K) e).appLE U W h s = t →
        pullbackGerm (projectiveClosureMap (algebraMap A K) e) U s = T.germToFunctionField W t := by
    intro U W _ _ h s t hst
    rw [← germToFunctionField_appLE_eq_pullbackGerm _ h, hst]
  have hψc : ∀ i j, pullbackGerm (projectiveClosureMap (algebraMap A K) e)
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))
      (ψ i (MvPolynomial.X j)) = T.germToFunctionField (c₂ i).U ((c₂ i).coords (MvPolynomial.X j)) :=
    fun i j => hgerm (hφpre i).ge _ _ (hψ i j)
  -- the boundary relations on the model
  have : IsDominant (projectiveClosureMap (algebraMap A K) e) :=
    projectiveClosureMap_isDominant e (algebraMap A K)
  have hneAB : ∀ a b, Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))) := by
    intro a b
    have := integral_opens_inter_nonempty T (c₂ a).U (c₂ b).U
    obtain ⟨⟨x, hxa, hxb⟩⟩ := this
    have h1 : x ∈ projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2)) :=
      (hφpre a).symm ▸ hxa
    have h2 : x ∈ projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2)) :=
      (hφpre b).symm ▸ hxb
    exact ⟨⟨x, h1, h2⟩⟩
  have hbAg : ∀ a b (k : Fin r), ∃ w : Γ(projectiveClosure (algebraMap A K) e,
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))ˣ,
      haveI := hneAB a b
      pullbackGerm (projectiveClosureMap (algebraMap A K) e) _
        (w : Γ(projectiveClosure (algebraMap A K) e, closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))) =
        ((sncChartComponentEquation (c₂ a) (σ₂ a) k * (sncChartComponentEquation (c₂ b) (σ₂ b) k)⁻¹ :
          T.functionFieldˣ) : T.functionField) := by
    intro a b k
    have := hneAB a b
    have : Nonempty ((c₂ a).U ⊓ (c₂ b).U : T.Opens) := integral_opens_inter_nonempty T _ _
    refine ⟨bA a b k, ?_⟩
    have hle : (c₂ a).U ⊓ (c₂ b).U ≤
        projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2)) ⊓
        projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2)) :=
      le_inf (inf_le_left.trans (hφpre a).ge) (inf_le_right.trans (hφpre b).ge)
    exact (hgerm (U := closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))
      (W := (c₂ a).U ⊓ (c₂ b).U) hle _ _ (hbA a b k)).trans (hbT a b k)
  have hbd : ∀ a b (k : Fin r), ∃ w : Γ(projectiveClosure (algebraMap A K) e,
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2))ˣ,
      (projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE inf_le_left).op
          (componentSection (ψ a) (σ₂ a) k) =
        (w : Γ(projectiveClosure (algebraMap A K) e, _)) *
          (projectiveClosure (algebraMap A K) e).presheaf.map (homOfLE inf_le_right).op
            (componentSection (ψ b) (σ₂ b) k) := by
    intro a b k
    have := hneAB a b
    have : Nonempty (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2) :
          (projectiveClosure (algebraMap A K) e).Opens) :=
      ⟨⟨_, (Classical.arbitrary (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ
        (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv a).1 (eqv a).2) ⊓
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv b).1 (eqv b).2)))).2⟩⟩
    obtain ⟨w, hw⟩ := hbAg a b k
    exact ⟨w, componentSection_relation (projectiveClosureMap (algebraMap A K) e) (ψ a) (ψ b)
      (c₂ a) (c₂ b) (hψc a) (hψc b) (σ₂ a) (σ₂ b) k _ hw⟩
  -- the Čech intersections
  have hVc : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen
      (fun i => closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) x) :=
    fun q x => Scheme.Modules.isAffineOpen_cechOpen hV x
  have hV'c : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen
      (fun i => (projectiveClosure (algebraMap A K) e).basicOpen
        (∏ j ∈ logSetOf (σ₂ i), ψ i (MvPolynomial.X j))) x) :=
    fun q x => Scheme.Modules.isAffineOpen_cechOpen (fun i => (hV i).basicOpen _) x
  have haffY : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen
      (fun i => (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY i).U) x) := fun q x => by
    have h := (hVc q x).preimage (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
    rw [← CohomologyAux.cechOpen_preimage] at h
    exact h
  have haffY' : ∀ q (x : Fin (q + 1) → Fin (N + 1)), IsAffineOpen (TopCat.Presheaf.cechOpen
      (fun i => (fibreAtlasRestrictCharts 𝔪.ResidueField Hk hV ψ hψFE hneY
        (fun i => (hV i).basicOpen _)
        (fun i => (projectiveClosure (algebraMap A K) e).basicOpen_le _) hneY' i).U) x) :=
    fun q x => by
    have h := (hV'c q x).preimage (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
    rw [← CohomologyAux.cechOpen_preimage] at h
    exact h
  have hneYc : ∀ q (x : Fin (q + 1) → Fin (N + 1)), Nonempty (TopCat.Presheaf.cechOpen
      (fun i => (fibreAtlasCharts 𝔪.ResidueField Hk hV ψ hψFE hneY i).U) x) :=
    fun q x => nonempty_cechOpen_of_isIntegral _ hneY x
  have hneYc' : ∀ q (x : Fin (q + 1) → Fin (N + 1)), Nonempty (TopCat.Presheaf.cechOpen
      (fun i => (fibreAtlasRestrictCharts 𝔪.ResidueField Hk hV ψ hψFE hneY
        (fun i => (hV i).basicOpen _)
        (fun i => (projectiveClosure (algebraMap A K) e).basicOpen_le _) hneY' i).U) x) :=
    fun q x => nonempty_cechOpen_of_isIntegral _ hneY' x
  -- the embedding of the closed fibre
  have : IsClosedImmersion (fibreProjectiveMap (L := 𝔪.ResidueField)
      (projectiveClosureι (algebraMap A K) e)) := fibreProjectiveMap_isClosedImmersion _
  have heYeq : ∀ k, projectivePullbackHomogeneousEquation (fibreProjectiveMap (L := 𝔪.ResidueField)
      (projectiveClosureι (algebraMap A K) e)) k 1 (MvPolynomial.X (eqv 0).1)
        (MvPolynomial.isHomogeneous_X _ (eqv 0).1) =
      (pullback.fst (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
        (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField)))).appLE _ _
        (fibreProjectiveMap_preimage_coordinate _ k).le
        (projectivePullbackHomogeneousEquation (projectiveClosureι (algebraMap A K) e) k 1
          (MvPolynomial.X (eqv 0).1) (MvPolynomial.isHomogeneous_X A (eqv 0).1)) := by
    intro k
    have h := fibreProjectiveMap_homogeneousEquation (L := 𝔪.ResidueField)
      (projectiveClosureι (algebraMap A K) e) k 1 (MvPolynomial.X (eqv 0).1)
      (MvPolynomial.isHomogeneous_X A (eqv 0).1)
    simp only [MvPolynomial.map_X] at h
    exact h
  -- the relation on the model
  have hneW : ∀ i, Nonempty (projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))) :=
    fun i => hneAB i 0
  have hneYW : ∀ i, Nonempty (pullback.fst (projectiveClosureι (algebraMap A K) e ≫
      polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ
      (closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))) := fun i => by
    have := hneY i
    have := hneY 0
    exact integral_opens_inter_nonempty Y
      (pullback.fst (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
        (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ
          (closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)))
      (pullback.fst (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
        (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ
          (closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2)))
  have hgQuT : ∀ i, haveI := hneW i
      (cocycleEquation (fun i => (c₂ i).U) wT i : T.functionField) =
        pullbackGerm (projectiveClosureMap (algebraMap A K) e)
          (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
          closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))
          (wA i 0 : Γ(projectiveClosure (algebraMap A K) e,
            closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
            closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))) := by
    intro i
    have := hneW i
    have : Nonempty ((c₂ i).U ⊓ (c₂ 0).U : T.Opens) := integral_opens_inter_nonempty T _ _
    have hle : (c₂ i).U ⊓ (c₂ 0).U ≤
        projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) ⊓
        projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2)) :=
      le_inf (inf_le_left.trans (hφpre i).ge) (inf_le_right.trans (hφpre 0).ge)
    exact (hgerm (U := closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))
      (W := (c₂ i).U ⊓ (c₂ 0).U) hle _ _ (hwAT i 0)).symm
  have hwKA : ∀ i, pullbackGerm (projectiveClosureMap (algebraMap A K) e)
      (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))
      (wAm i : Γ(projectiveClosure (algebraMap A K) e,
        closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))) =
        T.germToFunctionField (c₂ i).U (wK i : Γ(T, (c₂ i).U)) :=
    fun i => hgerm (hφpre i).ge _ _ (hwAm i)
  have hrelA := fun i => closure_relation_of_chartRelation e A HA hV (fun i => (eqv i).1) hVk ψ
    hψFE (hne := hneK) (fun i => (hV i).inf (hV 0)) (fun i => inf_le_left) (fun i => inf_le_right)
    (W := fun i => closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
        (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))
    c₂ hψc hUk (fun i => (wA i 0 : Γ(projectiveClosure (algebraMap A K) e,
      closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
      closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv 0).1 (eqv 0).2))))
    (cocycleEquation (fun i => (c₂ i).U) wT) hgQuT wAm wK hwKA σ₂ m m' a hwK i
  -- vanishing on the closed fibre (check 554)
  have hvan : ∀ Qk : CartierDivisor Y, (∀ i, ∀ z ∈ pullback.fst (projectiveClosureι
      (algebraMap A K) e ≫ polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom
        (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
          (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)),
        Qk.IsLocalEquationAt z (cocycleEquation (fun k => pullback.fst (projectiveClosureι
          (algebraMap A K) e ≫ polynomialProjectiveToBase P A) (Spec.map (CommRingCat.ofHom
            (algebraMap A 𝔪.ResidueField))) ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
              (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv k).1 (eqv k).2)))
          (pullbackCocycle (fun i => closureTransitionOfLE e hBA ⁻¹ᵁ
              (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2))
            (pullback.fst (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase P A)
              (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField)))) wA) i)) →
      ∀ j, 1 ≤ j → Subsingleton (Scheme.Modules.Cohomology Qk.sheaf j) := by
    intro Qk hQk j hj
    have := hneYW
    exact subsingleton_cohomology_of_fibreModel (ringChar 𝔪.ResidueField) 𝔪.ResidueField hW Hk hV
      ψ hψFE hneY (fun i => (hV i).basicOpen _)
      (fun i => (projectiveClosure (algebraMap A K) e).basicOpen_le _) hneY' hnormY _ hinjY hcohY
      E' hEc' hsncY hcoverY hpn σ₂ hcsY hcovY' hunitY hbd hVc hV'c haffY hneYc haffY' hneYc'
      (projectiveClosureι (algebraMap A K) e)
      (fibreProjectiveMap (L := 𝔪.ResidueField) (projectiveClosureι (algebraMap A K) e))
      (fibreProjectiveMap_toBase _) (fibreProjectiveMap_preimage_coordinate _) (eqv 0).1 heYeq
      (fun i => (eqv i).1) rfl hVk (fun i => (hV i).inf (hV 0)) (fun i => inf_le_left)
      (fun i => inf_le_right) _ wAm Qk _ hQk (fun i => rfl) m m' hm hm' a ha hrelA hj
  -- vanishing on T (check 555)
  have : IsAffineHom (pullback.diagonal (terminal.from T)) :=
    isAffineHom_diagonal_terminal_of_separated_toSpec (T ↘ Spec (CommRingCat.of K))
  have := hVne
  have := hneY
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  have hQK := subsingleton_cohomology_of_modelCocycle
    (fun i => closureTransitionOfLE e hBA ⁻¹ᵁ
      (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) hV hcovV
    (fun x => nonempty_cechOpen_of_isIntegral _ hVne x) wA hwA 𝔪 Hk
    (fun x => nonempty_cechOpen_of_isIntegral _ hneY x) hvan K Subtype.val_injective HA
    (fun x => nonempty_cechOpen_of_isIntegral _ hneK x)
    (Q + principalCartierDivisor T (q (eqv 0).1 (eqv 0).2)⁻¹)
    (cocycleEquation (fun i => (c₂ i).U) wT)
    (fun i z hz => hQ' i z ((hφpre i) ▸ hz))
    (fun i j _ => by
      have := hneAB i j
      have : Nonempty ((c₂ i).U ⊓ (c₂ j).U : T.Opens) := integral_opens_inter_nonempty T _ _
      have hle : (c₂ i).U ⊓ (c₂ j).U ≤
          projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2)) ⊓
          projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv j).1 (eqv j).2)) :=
        le_inf (inf_le_left.trans (hφpre i).ge) (inf_le_right.trans (hφpre j).ge)
      have h1 := hgerm (U := closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv i).1 (eqv i).2) ⊓
          closureTransitionOfLE e hBA ⁻¹ᵁ
            (projectiveClosure (algebraMap B K) e).basicOpen (sB (eqv j).1 (eqv j).2))
        (W := (c₂ i).U ⊓ (c₂ j).U) hle _ _ (hwAT i j)
      exact (congrArg (· * (cocycleEquation (fun i => (c₂ i).U) wT j : T.functionField)) h1).trans
        (cocycleEquation_transition (fun i => (c₂ i).U) wT hw i j).symm)
    hdegree
  -- back to Q
  have e1 := actualCohomologyLinearEquivOfIso
    (cartierSheafPrincipalShiftIso Q (q (eqv 0).1 (eqv 0).2)⁻¹).symm cohDegree
  exact e1.toEquiv.subsingleton

/-- The original degree-one interface is the specialization of all-positive-degree
ample SNC vanishing. Its statement is unchanged. -/
theorem kawamataViehwegVanishingSNCAmple_of_charZero (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] (n : ℕ) : KawamataViehwegVanishingSNCAmple K n :=
  kawamataViehwegVanishingSNCAmpleInDegree_of_charZero K n 1 le_rfl

/-- **Kawamata–Viehweg vanishing on smooth projective varieties in characteristic zero.** -/
theorem kawamataViehwegVanishingSNCProjective_of_charZero (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] (n : ℕ) : KawamataViehwegVanishingSNCProjective K n :=
  kawamataViehwegVanishingSNCProjective_of_ample K (kawamataViehwegVanishingSNCAmple_of_charZero K n)

/-- **Kawamata–Viehweg vanishing on smooth proper varieties in characteristic zero** (nef and big
adjoint with simple normal crossing boundary). -/
theorem kawamataViehwegVanishingSNC_of_charZero (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] (n : ℕ) : KawamataViehwegVanishingSNC K n :=
  kawamataViehwegVanishingSNC_of_projective K (kawamataViehwegVanishingSNCProjective_of_charZero K n)

/-- **The sum form of Kawamata–Viehweg vanishing in characteristic zero.** -/
theorem kawamataViehwegVanishingSNCSum_of_charZero (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] (n : ℕ) : KawamataViehwegVanishingSNCSum K n :=
  kawamataViehwegVanishingSNCSum_of_projective K
    (kawamataViehwegVanishingSNCProjective_of_charZero K n)

/-- **The mixed Fujita freeness theorem (F1)**, with Kawamata–Viehweg vanishing proved. -/
theorem mixedFujitaFreeness_proved : MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_ampleKV fun K _ _ _ n => kawamataViehwegVanishingSNCAmple_of_charZero K n

end MixedFujita

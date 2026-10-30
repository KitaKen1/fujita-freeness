/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StratumTangentSaturation
public import MixedFujita.SNCChartReindex
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Fibre charts (step 9, generic restriction). Let η be a point of a simple normal crossing chart
with n + d coordinates and h_1, …, h_d germs at η (the pullbacks of coordinates of the base at the
image of η). If on the residue field of η the differentials of the coordinates of the members
through η and of the h_l are linearly independent (transversality of the stratum through η to the
fibre), there is a simple normal crossing chart at η whose last d coordinates are the h_l at η and
whose members all have coordinates among the first n (`exists_fibreChart`).

The members not through η are removed by shrinking the chart, and the chart is saturated with
tangent coordinates from the h_l (`exists_tangent_saturated_chart`): every h_l then has all its
derivatives in the remaining free coordinates in the maximal ideal, so its differential on the
residue field lies in the span of the member and tangent coordinates. Independence forces at least
d tangent coordinates, and as they are distinct germs among the h_l there are exactly d of them,
one for each h_l. A permutation puts them last.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

section Linear

/-- A linearly independent family all of whose coordinates in a basis vanish outside a finite set
A has at most |A| members. -/
theorem card_le_of_linearIndependent_of_repr_support {κ V ι J : Type*} [Field κ]
    [AddCommGroup V] [Module κ V] [Fintype ι] [DecidableEq ι] [Fintype J]
    (βκ : Module.Basis ι κ V) (A : Finset ι) {v : J → V} (hv : LinearIndependent κ v)
    (hA : ∀ j, ∀ b ∉ A, βκ.repr (v j) b = 0) : Fintype.card J ≤ A.card := by
  let π : V →ₗ[κ] (A → κ) := LinearMap.pi fun b : A => βκ.coord b
  have hdisj : Disjoint (Submodule.span κ (Set.range v)) (LinearMap.ker π) := by
    rw [Submodule.disjoint_def]
    intro x hx hπ
    have hW : ∀ b ∉ A, βκ.repr x b = 0 := by
      clear hπ
      intro b hb
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact hA j b hb
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul a y _ hy => simp [hy]
    apply βκ.repr.injective
    ext b
    by_cases hb : b ∈ A
    · have h := congrFun (LinearMap.mem_ker.mp hπ) ⟨b, hb⟩
      simpa [π] using h
    · simpa using hW b hb
  have h := (hv.map hdisj).fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using h

end Linear

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

open Classical in
/-- Shrinking a simple normal crossing chart around η away from the members not through η and
forgetting these members. -/
theorem exists_snc_chart_through {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σ) {η : X} (hη : η ∈ c.U) :
    ∃ (c' : EtaleChart K X n) (hη' : η ∈ c'.U), c'.U ≤ c.U ∧
      IsSNCChart c' ξ (fun k => if η ∈ closure ({ξ k} : Set X) then σ k else none) ∧
      ∀ a, etaleChartStalkCoords c' η hη' (MvPolynomial.X a) =
        etaleChartStalkCoords c η hη (MvPolynomial.X a) := by
  classical
  let C : Set X := ⋃ k ∈ {k | η ∉ closure ({ξ k} : Set X)}, closure ({ξ k} : Set X)
  have hC : IsClosed C :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun k _ => isClosed_closure
  have hηC : η ∉ C := by
    simp only [C, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
    intro k hk hηk
    exact hk hηk
  obtain ⟨g, hle, hηg⟩ := c.isAffine.exists_basicOpen_le (V := ⟨Cᶜ, hC.isOpen_compl⟩)
    ⟨η, hηC⟩ hη
  have h0 := isSNCChart_basicOpen hc g ⟨⟨η, hηg⟩⟩
  refine ⟨etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩, hηg, X.basicOpen_le g, ⟨?_, fun k => ?_⟩,
    fun a => ?_⟩
  · intro i j a hi hj
    have hi' : σ i = some a := by
      by_cases h1 : η ∈ closure ({ξ i} : Set X)
      · simpa only [h1, ↓reduceIte] using hi
      · simp [h1] at hi
    have hj' : σ j = some a := by
      by_cases h1 : η ∈ closure ({ξ j} : Set X)
      · simpa only [h1, ↓reduceIte] using hj
      · simp [h1] at hj
    exact hc.1 i j a hi' hj'
  · by_cases hk : η ∈ closure ({ξ k} : Set X)
    · simp only [hk, ↓reduceIte]
      exact h0.2 k
    · simp only [hk, ↓reduceIte, Option.elim_none]
      change closure ({ξ k} : Set X) ∩ X.basicOpen g = ∅
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz hzg
      exact hle hzg (Set.mem_biUnion (x := k) hk hz)
  · rw [etaleChartStalkCoords_basicOpen]

/-- Fibre charts: if on the residue field of η the differentials of the coordinates of the members
through η and of the germs h_l are independent, there is a simple normal crossing chart at η whose
last d coordinates are the h_l at η and whose members have coordinates among the first n. -/
theorem exists_fibreChart {d r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin (n + d))) (η : X)
    (c : EtaleChart K X (n + d)) (hη : η ∈ c.U) (hc : IsSNCChart c ξ σ)
    (h : Fin d → X.presheaf.stalk η) (F : Type*) [Field F] [Algebra (X.presheaf.stalk η) F]
    (hF : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η),
      algebraMap (X.presheaf.stalk η) F x = 0)
    (hind : LinearIndependent F
      (Sum.elim
        (fun a : {a : Fin (n + d) // ∃ k, σ k = some a ∧ η ∈ closure ({ξ k} : Set X)} =>
          (1 : F) ⊗ₜ[X.presheaf.stalk η]
            KaehlerDifferential.D K (X.presheaf.stalk η)
              (etaleChartStalkCoords c η hη (MvPolynomial.X a.1)))
        (fun l => (1 : F) ⊗ₜ[X.presheaf.stalk η]
          KaehlerDifferential.D K (X.presheaf.stalk η) (h l)))) :
    ∃ (Fc : EtaleChart K X (n + d)) (hFc : η ∈ Fc.U) (σF : Fin r → Option (Fin (n + d))),
      Fc.U ≤ c.U ∧ IsSNCChart Fc ξ σF ∧ (∀ k a, σF k = some a → (a : ℕ) < n) ∧
      ∀ l, etaleChartStalkCoords Fc η hFc (MvPolynomial.X (Fin.natAdd n l)) = h l := by
  classical
  -- forget the members not through η
  obtain ⟨c₁, hη₁, hle₁, hc₁, hcoord₁⟩ := exists_snc_chart_through hc hη
  set σ₁ : Fin r → Option (Fin (n + d)) :=
    fun k => if η ∈ closure ({ξ k} : Set X) then σ k else none with hσ₁
  -- saturate with tangent coordinates from the h_l
  obtain ⟨c', hη', T, hle', hc', hT, hsame, hsat⟩ :=
    exists_tangent_saturated_chart ξ σ₁ η (Set.range h) c₁ hη₁ hc₁
  set y' := etaleChartStalkCoords c' η hη' with hy'def
  have hy' : y'.toRingHom.FormallyEtale := etaleChartStalkCoords_formallyEtale c' η hη'
  set β := etaleCoordinateBasis y' hy' with hβ
  set βκ := β.baseChange F with hβκ
  set S : Finset (Fin (n + d)) :=
    Finset.univ.filter (fun a => ∃ k, σ k = some a ∧ η ∈ closure ({ξ k} : Set X)) with hS
  have hσ₁S : ∀ k b, σ₁ k = some b → b ∈ S := by
    intro k b hkb
    by_cases h1 : η ∈ closure ({ξ k} : Set X)
    · simp only [hσ₁, h1, ↓reduceIte] at hkb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, hkb, h1⟩
    · simp [hσ₁, h1] at hkb
  have hTS : ∀ b ∈ T, b ∉ S := by
    intro b hb hbS
    obtain ⟨k, hk, hηk⟩ := (Finset.mem_filter.mp hbS).2
    exact (hT b hb).1 k (by simp only [hσ₁, hηk, ↓reduceIte]; exact hk)
  -- the member coordinates are unchanged
  have hC1 : ∀ a ∈ S, y' (MvPolynomial.X a) = etaleChartStalkCoords c η hη (MvPolynomial.X a) :=
    fun a ha => (hsame a fun haT => hTS a haT ha).trans (hcoord₁ a)
  -- support of the differentials in the basis
  have hrepr : ∀ (s : (X.presheaf.stalk η)) (b : Fin (n + d)),
      βκ.repr ((1 : F) ⊗ₜ[(X.presheaf.stalk η)] KaehlerDifferential.D K (X.presheaf.stalk η) s) b =
        algebraMap (X.presheaf.stalk η) F (etaleCoordinateDerivation y' hy' b s) := by
    intro s b
    rw [hβκ, Module.Basis.baseChange_repr_tmul, etaleCoordinateDerivation_apply, Algebra.smul_def,
      mul_one]
  have hsupp : ∀ j, ∀ b ∉ T ∪ S, βκ.repr (Sum.elim
      (fun a : {a : Fin (n + d) // ∃ k, σ k = some a ∧ η ∈ closure ({ξ k} : Set X)} =>
        (1 : F) ⊗ₜ[(X.presheaf.stalk η)] KaehlerDifferential.D K (X.presheaf.stalk η)
          (etaleChartStalkCoords c η hη (MvPolynomial.X a.1)))
      (fun l => (1 : F) ⊗ₜ[(X.presheaf.stalk η)] KaehlerDifferential.D K (X.presheaf.stalk η) (h l)) j) b = 0 := by
    intro j b hb
    rw [Finset.mem_union, not_or] at hb
    have hbσ : ∀ k, σ₁ k ≠ some b := fun k hk => hb.2 (hσ₁S k b hk)
    cases j with
    | inl a =>
      have haS : a.1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩
      simp only [Sum.elim_inl]
      rw [← hC1 a.1 haS, hrepr, etaleCoordinateDerivation_coordinate]
      have hne : a.1 ≠ b := fun e => hb.2 (e ▸ haS)
      simp only [hne, ↓reduceIte, map_zero]
    | inr l =>
      simp only [Sum.elim_inr]
      rw [hrepr]
      exact hF _ (hsat (h l) (Set.mem_range_self l) b hbσ hb.1)
  -- at least d tangent coordinates
  have hcardS : Fintype.card
      {a : Fin (n + d) // ∃ k, σ k = some a ∧ η ∈ closure ({ξ k} : Set X)} = S.card := by
    rw [Fintype.card_subtype]
  have hge : S.card + d ≤ T.card + S.card := by
    have h1 := card_le_of_linearIndependent_of_repr_support βκ (T ∪ S) hind hsupp
    rw [Fintype.card_sum, hcardS, Fintype.card_fin] at h1
    exact h1.trans (Finset.card_union_le T S)
  -- each tangent coordinate is one of the h_l, and distinct ones are distinct
  have hTl : ∀ b : T, ∃ l, h l = y' (MvPolynomial.X b.1) := fun b => (hT b.1 b.2).2
  choose φ hφ using hTl
  have hφinj : Function.Injective φ := by
    intro b b' hbb'
    have h1 : y' (MvPolynomial.X b.1) = y' (MvPolynomial.X b'.1) := by
      rw [← hφ b, ← hφ b', hbb']
    have h2 : β b.1 = β b'.1 := by
      rw [hβ, etaleCoordinateBasis_apply, etaleCoordinateBasis_apply, h1]
    exact Subtype.ext (β.injective h2)
  have hcardT : Fintype.card T = d := by
    have h1 := Fintype.card_le_of_injective φ hφinj
    rw [Fintype.card_fin] at h1
    rw [Fintype.card_coe] at h1 ⊢
    omega
  have hφbij : Function.Bijective φ :=
    (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hφinj, by rw [hcardT, Fintype.card_fin]⟩
  let eT : T ≃ Fin d := Equiv.ofBijective φ hφbij
  -- the complement has n elements
  have hcardC : Fintype.card {b : Fin (n + d) // b ∉ T} = n := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have h1 : Fintype.card {b : Fin (n + d) // b ∈ T} = d := by
      simp only [Fintype.card_coe] at hcardT ⊢
      exact hcardT
    omega
  let eC : Fin n ≃ {b : Fin (n + d) // b ∉ T} := (Fintype.equivFinOfCardEq hcardC).symm
  let e : Fin (n + d) ≃ Fin (n + d) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eC eT.symm).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun b => b ∈ T))))
  have he_nat : ∀ l, e (Fin.natAdd n l) = (eT.symm l).1 := by
    intro l
    simp [e, finSumFinEquiv_symm_apply_natAdd]
  have he_cast : ∀ i, e (Fin.castAdd d i) ∉ T := by
    intro i
    have : e (Fin.castAdd d i) = (eC i).1 := by
      simp [e, finSumFinEquiv_symm_apply_castAdd]
    rw [this]
    exact (eC i).2
  refine ⟨etaleChartReindex c' e, hη', fun k => (σ₁ k).map e.symm, hle'.trans hle₁,
    isSNCChart_reindex c' ξ σ₁ hc' e, ?_, ?_⟩
  · intro k a hka
    obtain ⟨b, hb, hba⟩ := Option.map_eq_some_iff.mp hka
    have hbS := hσ₁S k b hb
    have hbT : b ∉ T := fun hbT => hTS b hbT hbS
    have hab : e a = b := by rw [← hba, Equiv.apply_symm_apply]
    induction a using Fin.addCases with
    | left i => simp
    | right l =>
      exfalso
      apply hbT
      rw [← hab, he_nat]
      exact (eT.symm l).2
  · intro l
    rw [etaleChartReindex_stalk_variable, he_nat]
    have h1 := hφ (eT.symm l)
    have h2 : φ (eT.symm l) = l := eT.apply_symm_apply l
    rw [h2] at h1
    exact h1.symm

end Charts

end MixedFujita

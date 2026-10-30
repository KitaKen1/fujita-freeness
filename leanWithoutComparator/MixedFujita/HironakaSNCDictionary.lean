/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBertini
public import Hironaka.Scheme.Snc.SpreadSnc
public import Hironaka.Resolution.Algebraic.Snc.DictionaryComponents
public import Hironaka.Scheme.Smooth.EtaleCoordinates
public import Hironaka.Algebra.RegularSmooth.SchemeForms
public import Hironaka.Scheme.IdealSheaf.StalkLe

/-!
Dictionary between the simple normal crossing notions of the vendored resolution library and of
this project (step 7). The library states simple normal crossings in the stalks: at every point a
regular system of parameters contains a generator of the ideal of each component through the point
(Kollár's Definition 24 for a family of divisors, Hironaka's Definition 2 for a closed subscheme).
This project states them on étale charts: every point lies in an affine open with n étale
coordinates on which each member of the family is the zero locus of one coordinate, or is absent.
On a scheme smooth of relative dimension n over a perfect field the first gives the second: every
point specializes to a closed point, at a closed point the parameters are n in number, and the
library spreads them to étale coordinates on an affine neighbourhood on which the components
through the point are coordinate hyperplanes and the others are absent. The two structures of
algebra over the base field on the sections over an open coincide.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- The algebra structure of this project on the sections over an open is the one the resolution
library attaches to the structure morphism. -/
theorem cartierBaseOpenAlgebra_eq_sectionsAlgebra (U : X.Opens) :
    cartierBaseOpenAlgebra K X U = (X ↘ Spec (CommRingCat.of K)).sectionsAlgebra U := by
  unfold cartierBaseOpenAlgebra Scheme.Hom.sectionsAlgebra
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]

/-- Étale coordinates of the resolution library on an affine open form an étale chart. -/
noncomputable def etaleChartOfToAffineSpace (U : X.affineOpens) (hne : Nonempty U.1)
    (v : Fin n → Γ(X, U.1))
    (hv : Etale (toAffineSpace (X ↘ Spec (CommRingCat.of K)) U.1 v)) : EtaleChart K X n where
  U := U.1
  isAffine := U.2
  nonempty := hne
  coords := MvPolynomial.aeval v
  formallyEtale := by
    have h := ((etale_toAffineSpace_iff (X ↘ Spec (CommRingCat.of K)) U.2 v).mp hv).1
    have key : ∀ P : Algebra K Γ(X, U.1),
        P = (X ↘ Spec (CommRingCat.of K)).sectionsAlgebra U.1 →
        (@AlgHom.toRingHom K (MvPolynomial (Fin n) K) Γ(X, U.1) _ _ _ _ P
          (@MvPolynomial.aeval K Γ(X, U.1) (Fin n) _ _ P v)).FormallyEtale := by
      rintro P rfl
      exact h
    exact key _ (cartierBaseOpenAlgebra_eq_sectionsAlgebra (K := K) U.1)

theorem etaleChartOfToAffineSpace_coords (U : X.affineOpens) (hne : Nonempty U.1)
    (v : Fin n → Γ(X, U.1))
    (hv : Etale (toAffineSpace (X ↘ Spec (CommRingCat.of K)) U.1 v)) (a : Fin n) :
    (etaleChartOfToAffineSpace U hne v hv).coords (MvPolynomial.X a) = v a :=
  MvPolynomial.aeval_X v a

/-- A family of divisors with simple normal crossings in the sense of Kollár's Definition 24, on a
scheme smooth of relative dimension n over a perfect field, is a simple normal crossing family on
étale charts: ξ lists points whose closures are the supports of distinct members. -/
theorem isSNCFamily_of_divisorFamily_isSnc [PerfectField K]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (F : Scheme.DivisorFamily X) (hF : F.IsSnc) {r : ℕ} (ξ : Fin r → X) (e : Fin r → F.ι)
    (he : Function.Injective e)
    (hξ : ∀ i, ((F.component (e i)).support : Set X) = closure {ξ i}) :
    IsSNCFamily K n ξ := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hjac : JacobsonSpace X :=
    LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  intro x
  -- a closed point in the closure of x
  obtain ⟨x₀, hx₀x, hx₀cl⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set X))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hx₀cl' : IsClosed ({x₀} : Set X) := hx₀cl
  have hspec : x ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀x
  -- the parameters at the closed point are n in number
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := hF.2 x₀
  have hmn : m = n := by
    have h1 := Scheme.ringKrullDim_stalk_of_smoothOfRelativeDimension_of_isClosed
      (X ↘ Spec (CommRingCat.of K)) n hx₀cl'
    have h2 := hz.2
    rw [h1] at h2
    exact_mod_cast h2
  subst hmn
  -- étale coordinates on which the components through the point are coordinate hyperplanes
  obtain ⟨E, c', hc'inj, -, hideal, htop⟩ := exists_etaleCoordinatesAdapted_of_snc
    (X ↘ Spec (CommRingCat.of K)) m (Z := ⊥) F.component hx₀cl' hz.1.symm ∅
    (by rw [Scheme.IdealSheafData.stalkIdeal_bot, Finset.coe_empty, Set.image_empty,
      Ideal.span_empty]) c hcinj hc
  let σ : Fin r → Option (Fin m) := fun i =>
    if h : x₀ ∈ (F.component (e i)).support then some (c' ⟨e i, h⟩) else none
  refine ⟨etaleChartOfToAffineSpace E.U ⟨⟨x₀, E.mem⟩⟩ E.v E.etale, σ,
    hspec.mem_open E.U.1.isOpen E.mem, ?_, ?_⟩
  · intro i j a hi hj
    by_cases h1 : x₀ ∈ (F.component (e i)).support
    · by_cases h2 : x₀ ∈ (F.component (e j)).support
      · simp only [σ, h1, h2, ↓reduceDIte, Option.some.injEq] at hi hj
        have h3 := hc'inj (hi.trans hj.symm)
        exact he (congrArg Subtype.val h3)
      · simp [σ, h2] at hj
    · simp [σ, h1] at hi
  · intro i
    rw [← hξ i]
    by_cases h1 : x₀ ∈ (F.component (e i)).support
    · have hσ : σ i = some (c' ⟨e i, h1⟩) := by simp [σ, h1]
      rw [hσ, Option.elim_some, etaleChartOfToAffineSpace_coords]
      change ((F.component (e i)).support : Set X) ∩ E.U.1 = _
      rw [(F.component (e i)).coe_support_inter E.U, hideal ⟨e i, h1⟩, Scheme.zeroLocus_span]
      rfl
    · have hσ : σ i = none := by simp [σ, h1]
      rw [hσ, Option.elim_none]
      change ((F.component (e i)).support : Set X) ∩ E.U.1 = ∅
      have ht := congrArg (fun I : (E.U.1 : Scheme.{u}).IdealSheafData => (I.support : Set E.U.1))
        (htop (e i) h1)
      simp only [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
        Scheme.IdealSheafData.support_top, Closeds.coe_bot] at ht
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy hyU
      have : (⟨y, hyU⟩ : E.U.1) ∈ (E.U.1.ι ⁻¹' ((F.component (e i)).support : Set X)) := hy
      rw [ht] at this
      exact this

/-- A closed subscheme with only normal crossings in the sense of Hironaka's Definition 2, on a
Noetherian scheme smooth of relative dimension n over a perfect field: distinct generic points of
its support form a simple normal crossing family on étale charts. -/
theorem isSNCFamily_of_isSncBoundary [PerfectField K]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [NoetherianSpace X]
    (E : X.IdealSheafData) (hE : E.IsSncBoundary) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, ξ i ∈ E.support.genericPoints) :
    IsSNCFamily K n ξ := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hF := (Hironaka.Sequence.isSncBoundary_iff_isSnc_componentFamily
    (X ↘ Spec (CommRingCat.of K)) E).mp hE
  refine isSNCFamily_of_divisorFamily_isSnc E.componentFamily hF ξ (fun i => ⟨ξ i, hξ i⟩)
    (fun i j h => hinj (congrArg Subtype.val h)) fun i => ?_
  change ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {ξ i})).support : Set X) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end MixedFujita

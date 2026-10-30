/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-!
Algebraic Hartogs (step 15). Let A be a Noetherian domain with fraction field K and h = b/a in K
not in A, so that b is not in (a). Some associated prime P = ((a) : c) of A/(a) contains the
denominator ideal ((a) : b) of h, and t = c/a satisfies t P ⊆ A. If t P ⊆ P, then t is integral
over A (P is finitely generated and nonzero), so t lies in A_P when A_P is integrally closed, and
then s c ∈ (a) for some s ∉ P, that is s ∈ P: impossible. Otherwise u = t p₀ is not in P for some
p₀ ∈ P, every p ∈ P has u p ∈ (p₀), P is minimal over (p₀) and has height one by Krull's
principal ideal theorem. If h lies in A_P for every height-one P, the denominator ideal is not
contained in P: impossible. So a Noetherian domain with integrally closed localizations is the
intersection of its localizations at height-one primes. On a normal locally Noetherian integral
scheme a rational function regular at the codimension-one points of an affine open U is a
section over U, and a rational function regular at the codimension-one points of a neighbourhood
of x is regular at x.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

section Ring

variable {A K : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- Algebraic Hartogs: if A_P is integrally closed in K at the nonzero primes P, an element of K
lying in A_P for every height-one prime P lies in A. -/
theorem mem_range_of_forall_height_eq_one
    (hloc : ∀ P : Ideal A, P.IsPrime → P ≠ ⊥ → ∀ t : K, IsIntegral A t →
      ∃ s ∉ P, algebraMap A K s * t ∈ (algebraMap A K).range)
    (h : K) (hh : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      ∃ s ∉ P, algebraMap A K s * h ∈ (algebraMap A K).range) :
    h ∈ (algebraMap A K).range := by
  obtain ⟨b, a, ha, rfl⟩ := IsFractionRing.div_surjective (A := A) h
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha0
  have hdiv : ∀ s : A, algebraMap A K s * (algebraMap A K b / algebraMap A K a) ∈
      (algebraMap A K).range → s * b ∈ Ideal.span {a} := by
    rintro s ⟨e, he⟩
    refine Ideal.mem_span_singleton'.mpr ⟨e, hinj ?_⟩
    rw [map_mul, map_mul, he]
    field_simp
  by_contra hnot
  have hb : b ∉ Ideal.span {a} := by
    intro hb
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hb
    exact hnot ⟨e, by rw [← he, map_mul]; field_simp⟩
  have hmem : ∀ r z : A, r ∈ (⊥ : Submodule A (A ⧸ Ideal.span {a})).colon
      {Ideal.Quotient.mk (Ideal.span {a}) z} ↔ r * z ∈ Ideal.span {a} := by
    intro r z
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hx : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hxP⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hx
  obtain ⟨hPprime, y, hPy⟩ := isAssociatedPrime_iff.mp hP
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hPc : ∀ r : A, r ∈ P ↔ r * c ∈ Ideal.span {a} := fun r => by
    rw [hPy]
    exact hmem r c
  have hden : ∀ s : A, s * b ∈ Ideal.span {a} → s ∈ P := fun s hs => hxP ((hmem s b).mpr hs)
  have haP : a ∈ P := (hPc a).mpr (Ideal.mul_mem_right c _ (Ideal.mem_span_singleton_self a))
  have hP0 : P ≠ ⊥ := fun h0 => ha0 (by rw [h0] at haP; exact (Submodule.mem_bot A).mp haP)
  have hquot : ∀ p ∈ P, ∃ d : A, d * a = p * c := fun p hp =>
    Ideal.mem_span_singleton'.mp ((hPc p).mp hp)
  by_cases hcase : ∀ p ∈ P, ∀ d : A, d * a = p * c → d ∈ P
  · -- c/a stabilizes P, hence is integral over A
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hN : N ≠ ⊥ := by
      intro h0
      have : algebraMap A K a ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap A K) haP
      rw [h0, Submodule.mem_bot] at this
      exact haK this
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have htN : ∀ n ∈ N, (algebraMap A K c / algebraMap A K a) • n ∈ N := by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨d, hd⟩ := hquot p hp
      refine ⟨d, hcase p hp d hd, ?_⟩
      have hd' : algebraMap A K d * algebraMap A K a = algebraMap A K p * algebraMap A K c := by
        rw [← map_mul, ← map_mul, hd]
      change algebraMap A K d = algebraMap A K c / algebraMap A K a * algebraMap A K p
      field_simp
      linear_combination hd'
    have hint : IsIntegral A (algebraMap A K c / algebraMap A K a) :=
      isIntegral_of_smul_mem_submodule N hN hNfg _ htN
    obtain ⟨s, hsP, e, he⟩ := hloc P hPprime hP0 _ hint
    apply hsP
    rw [hPc]
    refine Ideal.mem_span_singleton'.mpr ⟨e, hinj ?_⟩
    rw [map_mul, map_mul, he]
    field_simp
  · -- P is minimal over a principal ideal, hence of height one
    obtain ⟨p₀, hp₀, d₀, hd₀, hd₀P⟩ : ∃ p₀ ∈ P, ∃ d₀ : A, d₀ * a = p₀ * c ∧ d₀ ∉ P := by
      by_contra hne
      exact hcase fun p hp d hd => by_contra fun hdP => hne ⟨p, hp, d, hd, hdP⟩
    have hmin : P ∈ (Ideal.span {p₀}).minimalPrimes := by
      refine ⟨⟨hPprime, (Ideal.span_singleton_le_iff_mem P).mpr hp₀⟩, ?_⟩
      rintro Q ⟨hQ, hQle⟩ hQP p hp
      obtain ⟨d, hd⟩ := hquot p hp
      have hcancel : d₀ * p = p₀ * d := by
        apply mul_right_cancel₀ ha0
        calc d₀ * p * a = p * (d₀ * a) := by ring
          _ = p * (p₀ * c) := by rw [hd₀]
          _ = p₀ * (p * c) := by ring
          _ = p₀ * (d * a) := by rw [hd]
          _ = p₀ * d * a := by ring
      have hmemQ : d₀ * p ∈ Q :=
        hcancel ▸ hQle (Ideal.mul_mem_right d _ (Ideal.mem_span_singleton_self p₀))
      exact (hQ.mem_or_mem hmemQ).resolve_left fun h => hd₀P (hQP h)
    have : (Ideal.span {p₀}).IsPrincipal := ⟨⟨p₀, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
    have hne : P.height ≠ 0 := fun h0 => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
    obtain ⟨s, hsP, hs⟩ := hh P hPprime (le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne))
    exact hsP (hden s (hdiv s hs))

/-- Algebraic Hartogs for an integrally closed Noetherian domain. -/
theorem mem_range_of_forall_height_eq_one_of_isIntegrallyClosed [IsIntegrallyClosed A] (h : K)
    (hh : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      ∃ s ∉ P, algebraMap A K s * h ∈ (algebraMap A K).range) :
    h ∈ (algebraMap A K).range := by
  refine mem_range_of_forall_height_eq_one (fun P hP _ t ht => ?_) h hh
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp ht
  exact ⟨1, (Ideal.ne_top_iff_one P).mp hP.ne_top, y, by rw [map_one, one_mul, hy]⟩

end Ring

section Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X]

omit [IsIntegral X] in
theorem fromSpec_mem_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    (y : PrimeSpectrum Γ(X, U)) : hU.fromSpec y ∈ U := by
  rw [← SetLike.mem_coe, ← hU.range_fromSpec]
  exact Set.mem_range_self _

/-- An element of the function field regular at the point of an affine open U corresponding to a
prime P of Γ(U) becomes a section over U after multiplication by some s ∉ P. -/
theorem exists_mul_mem_range_of_mem_stalk (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (P : Ideal Γ(X, U)) (hP : P.IsPrime) (z : X.functionField)
    (hz : z ∈ (algebraMap (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) X.functionField).range) :
    ∃ s ∉ P, algebraMap Γ(X, U) X.functionField s * z ∈
      (algebraMap Γ(X, U) X.functionField).range := by
  obtain ⟨w, rfl⟩ := hz
  have hξ : hU.fromSpec ⟨P, hP⟩ ∈ U := fromSpec_mem_of_isAffineOpen hU _
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec ⟨P, hP⟩, hξ⟩ : U)
  have := hU.isLocalization_stalk' ⟨P, hP⟩ hξ
  have := functionField_isScalarTower X U ⟨hU.fromSpec ⟨P, hP⟩, hξ⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj P.primeCompl w
  refine ⟨s, s.2, r, ?_⟩
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩))
      X.functionField r,
    IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩))
      X.functionField (s : Γ(X, U)), ← hrs, map_mul, mul_comm]

variable [IsLocallyNoetherian X]

/-- Hartogs on a normal locally Noetherian integral scheme: a rational function regular at every
codimension-one point of an affine open U is a section over U. -/
theorem mem_range_sections_of_codimOne (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (h : X.functionField)
    (hh : ∀ ξ : X, ξ ∈ U → Order.coheight ξ = 1 →
      h ∈ (algebraMap (X.presheaf.stalk ξ) X.functionField).range) :
    h ∈ (algebraMap Γ(X, U) X.functionField).range := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine mem_range_of_forall_height_eq_one (A := Γ(X, U)) ?_ h ?_
  · intro P hP _ t ht
    apply exists_mul_mem_range_of_mem_stalk U hU P hP t
    have hξ : hU.fromSpec ⟨P, hP⟩ ∈ U := fromSpec_mem_of_isAffineOpen hU _
    have := functionField_isScalarTower X U ⟨hU.fromSpec ⟨P, hP⟩, hξ⟩
    have := hnorm (hU.fromSpec ⟨P, hP⟩)
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec ⟨P, hP⟩, hξ⟩ : U)
    exact IsIntegrallyClosed.isIntegral_iff.mp
      (ht.tower_top (A := X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)))
  · intro P hP h1
    have := hP
    apply exists_mul_mem_range_of_mem_stalk U hU P hP h
    have hξ : hU.fromSpec ⟨P, hP⟩ ∈ U := fromSpec_mem_of_isAffineOpen hU _
    apply hh _ hξ
    have hdim := ringKrullDim_stalk_eq_coheight (hU.fromSpec ⟨P, hP⟩)
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec ⟨P, hP⟩, hξ⟩ : U)
    have := hU.isLocalization_stalk' ⟨P, hP⟩ hξ
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P
      (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)), h1] at hdim
    exact_mod_cast hdim.symm

/-- Hartogs at a point: a rational function regular at every codimension-one point of an open W
containing x is regular at x. -/
theorem mem_range_stalk_of_codimOne (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (x : X) (W : X.Opens) (hxW : x ∈ W) (h : X.functionField)
    (hh : ∀ ξ : X, ξ ∈ W → Order.coheight ξ = 1 →
      h ∈ (algebraMap (X.presheaf.stalk ξ) X.functionField).range) :
    h ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨g, hg⟩ := mem_range_sections_of_codimOne hnorm U hU h fun ξ hξ h1 => hh ξ (hUW hξ) h1
  refine ⟨X.presheaf.germ U x hxU g, ?_⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact hg

end Scheme

end MixedFujita

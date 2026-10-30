/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HypersurfaceQuotientEtale
public import MixedFujita.SmoothSchemeComponents

/-!
Smooth domain neighbourhoods of a point (step 9, restriction theorem).

If the localization of a noetherian ring C at a prime P is a domain, then so is a localization
C_c at one element c ∉ P (`exists_away_isDomain_of_isDomain_atPrime`): the kernel Q of C → C_P is
a finitely generated prime ideal inside P, each generator is killed by an element outside P, and
in C_c for the product c of these elements Q becomes the zero ideal, which stays prime. Applied to
a K-algebra of finite presentation with N étale coordinates (its spectrum is smooth, so its stalks
are domains), this gives a basic open neighbourhood of a K-point whose ring is a smooth domain of
relative dimension N (`exists_away_isDomain_smoothOfRelativeDimension`): the hypersurface of the
first étale coordinate (check-320), localized there, is again a smooth K-domain, as needed for the
induction on the codimension in the restriction theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Algebra

/-- If the localization of a noetherian ring at a prime P is a domain, so is its localization at
one element outside P. -/
theorem exists_away_isDomain_of_isDomain_atPrime {C : Type*} [CommRing C] [IsNoetherianRing C]
    (P : Ideal C) [P.IsPrime] [IsDomain (Localization.AtPrime P)] :
    ∃ c ∉ P, IsDomain (Localization.Away c) := by
  classical
  let Q := RingHom.ker (algebraMap C (Localization.AtPrime P))
  have hQprime : Q.IsPrime := RingHom.ker_isPrime _
  have hQP : Q ≤ P := by
    intro x hx
    obtain ⟨⟨m, hm⟩, hmx⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mp hx
    exact ((‹P.IsPrime›.mem_or_mem (hmx.symm ▸ P.zero_mem)).resolve_left hm)
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian Q : Q.FG)
  have hw : ∀ q ∈ s, ∃ t ∉ P, t * q = 0 := by
    intro q hq
    have hqQ : q ∈ Q := hs ▸ Ideal.subset_span hq
    obtain ⟨⟨m, hm⟩, hmq⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ q).mp hqQ
    exact ⟨m, hm, hmq⟩
  choose! t ht0 ht1 using hw
  let c := ∏ q ∈ s, t q
  have hcP : c ∉ P := by
    intro hc
    obtain ⟨q, hq, hqP⟩ := Ideal.IsPrime.prod_mem_iff.mp hc
    exact ht0 q hq hqP
  refine ⟨c, hcP, ?_⟩
  -- Q becomes zero in C_c
  have hmap : Q.map (algebraMap C (Localization.Away c)) = ⊥ := by
    rw [← hs, Ideal.map_span, Ideal.span_eq_bot]
    rintro _ ⟨q, hq, rfl⟩
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers c)]
    refine ⟨⟨c, 1, pow_one c⟩, ?_⟩
    change (∏ q ∈ s, t q) * q = 0
    rw [← Finset.mul_prod_erase s t hq, mul_comm (t q), mul_assoc, ht1 q hq, mul_zero]
  -- and stays prime
  have hdisj : Disjoint (Submonoid.powers c : Set C) (Q : Set C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hcP (‹P.IsPrime›.mem_of_pow_mem k (hQP hk))
  have hprime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers c)
    (Localization.Away c) Q hQprime hdisj
  rw [hmap] at hprime
  exact IsDomain.of_bot_isPrime _

end Algebra

section Smooth

variable {K : Type u} [Field K] {C : Type u} [CommRing C] [Algebra K C]

attribute [local instance] specAlgebraOver

/-- A K-algebra of finite presentation with N étale coordinates is, on a basic open neighbourhood
of a K-point, a smooth K-domain of relative dimension N. -/
theorem exists_away_isDomain_smoothOfRelativeDimension [Algebra.FinitePresentation K C] {N : ℕ}
    (v : MvPolynomial (Fin N) K →ₐ[K] C) (hv : v.toRingHom.FormallyEtale) (χ : C →ₐ[K] K) :
    ∃ c : C, χ c ≠ 0 ∧ IsDomain (Localization.Away c) ∧
      SmoothOfRelativeDimension N
        (Spec (CommRingCat.of (Localization.Away c)) ↘ Spec (CommRingCat.of K)) := by
  -- C is smooth over K
  haveI : Algebra.FormallySmooth K C := by
    letI := v.toRingHom.toAlgebra
    haveI : Algebra.FormallyEtale (MvPolynomial (Fin N) K) C := hv
    haveI : IsScalarTower K (MvPolynomial (Fin N) K) C :=
      IsScalarTower.of_algebraMap_eq fun k => (v.commutes k).symm
    exact Algebra.FormallySmooth.comp K (MvPolynomial (Fin N) K) C
  haveI : Algebra.Smooth K C := ⟨inferInstance, inferInstance⟩
  have hsm := specAlgebraOver_smooth (K := K) C
  -- the stalk at the K-point, a localization at the prime, is a domain
  let P : Ideal C := RingHom.ker χ.toRingHom
  haveI : P.IsPrime := RingHom.ker_isPrime _
  have hdom := smoothScheme_stalk_isDomain
    (Spec (CommRingCat.of C) ↘ Spec (CommRingCat.of K)) (specAlgHomPoint χ)
  letI : Algebra C ((Spec (CommRingCat.of C)).presheaf.stalk (specAlgHomPoint χ)) :=
    StructureSheaf.stalkAlgebra C (specAlgHomPoint χ)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of C)).presheaf.stalk (specAlgHomPoint χ))
      P := StructureSheaf.IsLocalization.to_stalk C (specAlgHomPoint χ)
  haveI : IsDomain (Localization.AtPrime P) :=
    MulEquiv.isDomain ((Spec (CommRingCat.of C)).presheaf.stalk (specAlgHomPoint χ))
      (IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
        ((Spec (CommRingCat.of C)).presheaf.stalk (specAlgHomPoint χ))).toRingEquiv.toMulEquiv
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing K C
  obtain ⟨c, hcP, hdomc⟩ := exists_away_isDomain_of_isDomain_atPrime P
  refine ⟨c, fun h0 => hcP h0, hdomc, ?_⟩
  -- the localization keeps the étale coordinates
  haveI : Algebra.Smooth C (Localization.Away c) := Algebra.Smooth.of_isLocalization_Away c
  haveI : Algebra.Smooth K (Localization.Away c) := Algebra.Smooth.comp K C (Localization.Away c)
  let v' := (IsScalarTower.toAlgHom K C (Localization.Away c)).comp v
  have hloc : (IsScalarTower.toAlgHom K C (Localization.Away c)).toRingHom.FormallyEtale := by
    change (algebraMap C (Localization.Away c)).FormallyEtale
    exact RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c))
  have hv' : v'.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp hv hloc
  exact specAlgebraOver_smoothOfRelativeDimension (K := K) (Localization.Away c) v' hv'

end Smooth

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Hironaka.Algebra.RegularSmooth.RegularImpliesSmooth
public import Mathlib.RingTheory.EssentialFiniteness

/-!
A regular local algebra essentially of finite type over a perfect field is
formally smooth. The finite type subalgebra in the existing essential-finiteness
presentation is localized at the inverse image of the maximal ideal. This
allows the existing finite type regular/smooth theorem to apply to actual stalks.
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Perfect-field regularity implies formal smoothness for essentially finite type local algebras. -/
theorem formallySmooth_of_regular_essFiniteType_perfectField
    (k S : Type u) [Field k] [PerfectField k] [CommRing S] [IsLocalRing S]
    [IsRegularLocalRing S] [Algebra k S] [Algebra.EssFiniteType k S] :
    Algebra.FormallySmooth k S := by
  let C := Algebra.EssFiniteType.subalgebra k S
  let p : Ideal C := Ideal.comap (algebraMap C S) (IsLocalRing.maximalIdeal S)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hmon : Algebra.EssFiniteType.submonoid k S = p.primeCompl := by
    ext x
    change IsUnit (algebraMap C S x) ↔ algebraMap C S x ∉ IsLocalRing.maximalIdeal S
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  letI : IsLocalization.AtPrime S p := by
    change IsLocalization p.primeCompl S
    rw [← hmon]
    exact Algebra.EssFiniteType.isLocalization k S
  let e : Localization.AtPrime p ≃ₐ[k] S :=
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) S).restrictScalars k
  letI : IsRegularLocalRing (Localization.AtPrime p) :=
    IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  haveI : Algebra.IsSmoothAt k p :=
    Algebra.IsSmoothAt.of_isRegularLocalRing_of_perfectField p
  exact Algebra.FormallySmooth.of_equiv e

end MixedFujita

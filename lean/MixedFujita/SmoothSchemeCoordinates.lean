/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothAtCompletion
public import MixedFujita.CartierTaylorCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
Use the actual structure morphism, affine germs, and stalk localization to
construct K-algebra completed coordinates at a rational point of a smooth
scheme. The K-action agrees with the existing Cartier section Taylor map.
The number of variables is existential; its identification with dim X is
not asserted here. A K-valued local point is a rational-point hypothesis,
not a supplied coordinate or residue-field isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra

@[instance_reducible]
noncomputable def cartierBaseOpenAlgebra (K : Type u) [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] (U : X.Opens) : Algebra K Γ(X, U) :=
  ((X.baseRingToStructurePresheaf K).app (op U)).hom.toAlgebra

attribute [local instance] cartierBaseOpenAlgebra

theorem cartierBaseOpenLocalScalarTower {U : X.Opens} (x : X) (hx : x ∈ U) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
    IsScalarTower K Γ(X, U) (X.presheaf.stalk x) := by
  let germAlgebra := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  apply IsScalarTower.of_algebraMap_eq
  intro k
  dsimp [Algebra.algebraMap, cartierBaseLocalAlgebra, cartierBaseOpenAlgebra,
    cartierGlobalStalkAlgebra, germAlgebra, RingHom.toAlgebra]
  rw [Scheme.baseRingToStructurePresheaf_app]
  change (X.presheaf.germ ⊤ x (Opens.mem_top x))
      (Scheme.Modules.baseRingToGlobalSections K X k) =
    (X.presheaf.germ U x hx) ((X.presheaf.map U.leTop.op)
      (Scheme.Modules.baseRingToGlobalSections K X k))
  exact (X.presheaf.Γgerm_res_apply x hx _).symm

theorem smoothScheme_affineOpen_smooth {U : X.Opens} (hU : IsAffineOpen U)
    [Smooth (X ↘ Spec (CommRingCat.of K))] : Algebra.Smooth K Γ(X, U) := by
  apply RingHom.smooth_algebraMap.mp
  change (((X.baseRingToStructurePresheaf K).app (op U)).hom).Smooth
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv))
      ((X ↘ Spec (CommRingCat.of K)).smooth_appLE
        (isAffineOpen_top _) hU le_top)

section RationalAffinePoint

variable {U : X.Opens} (x : X) (hx : x ∈ U)
  (β : X.presheaf.stalk x →ₐ[K] K)

noncomputable def rationalAffineGermPoint : Γ(X, U) →ₐ[K] K := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  letI := cartierBaseOpenLocalScalarTower (K := K) x hx
  exact β.comp (IsScalarTower.toAlgHom K Γ(X, U) (X.presheaf.stalk x))

theorem rationalAffineGermPoint_ker (hU : IsAffineOpen U) :
    RingHom.ker (rationalAffineGermPoint x hx β).toRingHom =
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have H := congrArg PrimeSpectrum.asIdeal (hU.primeIdealOf_eq_map_closedPoint ⟨x, hx⟩)
  change (RingHom.ker β.toRingHom).comap (X.presheaf.germ U x hx).hom = _
  rw [rationalLocalPoint_ker β]
  exact H.symm

include hx β in
theorem smoothScheme_affineRationalPoint_exists_stalkCoordinates (hU : IsAffineOpen U)
    [Smooth (X ↘ Spec (CommRingCat.of K))] :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  let := cartierBaseOpenLocalScalarTower (K := K) x hx
  let := smoothScheme_affineOpen_smooth (K := K) hU
  let α := rationalAffineGermPoint x hx β
  have hα : RingHom.ker α.toRingHom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    rationalAffineGermPoint_ker x hx β hU
  let : (RingHom.ker α.toRingHom).IsMaximal := rationalPoint_ker_isMaximal α
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker α.toRingHom) := by
    have H := hU.isLocalization_stalk (⟨x, hx⟩ : U)
    simpa only [hα] using H
  exact smoothRationalPoint_exists_localCompletionCoordinates α (X.presheaf.stalk x)

end RationalAffinePoint

theorem smoothScheme_rationalPoint_exists_stalkCoordinates
    [Smooth (X ↘ Spec (CommRingCat.of K))] (x : X)
    (β : X.presheaf.stalk x →ₐ[K] K) :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (⊤ : X.Opens) from Opens.mem_top x) isOpen_univ
  exact smoothScheme_affineRationalPoint_exists_stalkCoordinates x hx β hU

theorem smoothScheme_stalk_isNoetherianRing [Smooth (X ↘ Spec (CommRingCat.of K))]
    (x : X) : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (⊤ : X.Opens) from Opens.mem_top x) isOpen_univ
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  let := smoothScheme_affineOpen_smooth (K := K) hU
  let : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing K Γ(X, U)
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk (⟨x, hx⟩ : U)
  exact IsLocalization.isNoetherianRing
    (M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x) inferInstance

end MixedFujita

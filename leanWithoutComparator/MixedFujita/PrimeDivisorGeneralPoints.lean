/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PrimeDivisorCoordinates
public import MixedFujita.GenericSmoothCharts

/-!
Charts adapted to a prime divisor at its general points (step 6). Let E be the closure of a
point ξ, p a point of E with a K-valued stalk point in an étale chart c, and h a section on the
chart whose germ at p is a nonzero local equation of E: every germ at p vanishing at ξ is a
multiple of h. Coordinate derivatives commute with germs, and some ∂h/∂y_j is not a multiple of h
at p (characteristic zero); it therefore does not vanish at ξ, so ξ lies in the basic open of
∂h/∂y_j. This open set meets E in a nonempty open subset of E, which contains closed points
(Jacobson); at each of them the chart c can be modified so that h becomes the j-th coordinate, and
E is a coordinate hyperplane: ord_E is a monomial test valuation at the general points of E.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- Coordinate derivatives commute with germs. -/
theorem etaleChart_germ_derivation (c : EtaleChart K X n) (p : X) (hp : p ∈ c.U) (j : Fin n)
    (s : Γ(X, c.U)) :
    X.presheaf.germ c.U p hp (etaleCoordinateDerivation c.coords c.formallyEtale j s) =
      etaleCoordinateDerivation (etaleChartStalkCoords c p hp)
        (etaleChartStalkCoords_formallyEtale c p hp) j (X.presheaf.germ c.U p hp s) :=
  (etaleCoordinateDerivation_comp (sectionStalkAlgHom (K := K) c.U p hp) c.coords c.formallyEtale
    (etaleChartStalkCoords_formallyEtale c p hp) j s).symm

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The generic point ξ of E lies in the basic open of some ∂h/∂y_j, if the germ of h at p is a
nonzero local equation of the closure of ξ. -/
theorem etaleChart_exists_basicOpen_genericPoint [CharZero K] (c : EtaleChart K X n) (p : X)
    (hp : p ∈ c.U) (β : X.presheaf.stalk p →ₐ[K] K) [IsNoetherianRing (X.presheaf.stalk p)]
    (h : Γ(X, c.U)) (ξ : X) (hξ : ξ ⤳ p)
    (hh : X.presheaf.germ c.U p hp h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (hh0 : X.presheaf.germ c.U p hp h ≠ 0)
    (hgen : ∀ a : X.presheaf.stalk p, X.presheaf.stalkSpecializes hξ a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) → a ∈ Ideal.span {X.presheaf.germ c.U p hp h}) :
    ∃ j, ξ ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h) := by
  obtain ⟨j, hj⟩ := etaleChart_exists_derivation_notMem_span c p hp β _ hh hh0
  refine ⟨j, ?_⟩
  have hξU : ξ ∈ c.U := hξ.mem_open c.U.isOpen hp
  rw [X.mem_basicOpen _ ξ hξU]
  by_contra hnu
  apply hj
  rw [← etaleChart_germ_derivation]
  apply hgen
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (IsLocalRing.mem_maximalIdeal _).mpr hnu

/-- At the closed points of a nonempty open subset of E the chart can be adapted to E: there are
j and closed points q of E (as close to the generic point as wanted) at which ∂h/∂y_j does not
vanish, so that the modified chart with j-th coordinate h is defined at q. -/
theorem etaleChart_exists_adapted_closedPoint [CharZero K] (c : EtaleChart K X n) (p : X)
    (hp : p ∈ c.U) (β : X.presheaf.stalk p →ₐ[K] K) [IsNoetherianRing (X.presheaf.stalk p)]
    (h : Γ(X, c.U)) (ξ : X) (hξ : ξ ⤳ p)
    (hh : X.presheaf.germ c.U p hp h ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p))
    (hh0 : X.presheaf.germ c.U p hp h ≠ 0)
    (hgen : ∀ a : X.presheaf.stalk p, X.presheaf.stalkSpecializes hξ a ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) → a ∈ Ideal.span {X.presheaf.germ c.U p hp h})
    (O : Set X) (hO : IsOpen O) (hξO : ξ ∈ O) :
    ∃ j, ∃ q : X, IsClosed {q} ∧ q ∈ closure {ξ} ∧ q ∈ O ∧
      q ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h) := by
  obtain ⟨j, hj⟩ := etaleChart_exists_basicOpen_genericPoint c p hp β h ξ hξ hh hh0 hgen
  refine ⟨j, ?_⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  have hlc : IsLocallyClosed (closure {ξ} ∩ (O ∩
      (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h) : Set X))) :=
    (isClosed_closure.isLocallyClosed).inter
      ((hO.inter (X.basicOpen _).isOpen).isLocallyClosed)
  have hne : (closure {ξ} ∩ (O ∩
      (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h) : Set X))).Nonempty :=
    ⟨ξ, subset_closure rfl, hξO, hj⟩
  obtain ⟨q, ⟨hqE, hqO, hqD⟩, hqc⟩ := nonempty_inter_closedPoints hne hlc
  exact ⟨q, mem_closedPoints_iff.mp hqc, hqE, hqO, hqD⟩

end MixedFujita

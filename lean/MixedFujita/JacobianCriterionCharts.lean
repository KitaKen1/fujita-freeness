/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeCanonicalDivisor
public import MixedFujita.CoordinateDivisorValuation
public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
The Jacobian criterion and charts adapted to a divisor (step 6). If A is formally smooth over K
and the differentials of y_1, …, y_n form a basis of Ω[A/K], then y : K[Y] → A is formally étale:
by the Jacobi–Zariski sequence H₁(L_{A/K}) → H₁(L_{A/K[Y]}) → A ⊗ Ω_{K[Y]} → Ω_A → Ω_{A/K[Y]} → 0
the middle map is bijective, so Ω_{A/K[Y]} = 0, and H₁(L_{A/K}) = 0 forces H₁(L_{A/K[Y]}) = 0.
Replacing the j-th étale coordinate x_j by h gives étale coordinates where ∂h/∂x_j is a unit: the
determinant of the new differentials in the old basis is ∂h/∂x_j. On a scheme, an étale chart and
h with ∂h/∂x_j nonzero at p give an étale chart on the basic open of ∂h/∂x_j whose j-th coordinate
is h. If h vanishes at p and is prime in the local ring, the divisor {h = 0} is the coordinate
hyperplane {y_j = 0} of this chart near p, and its divisorial valuation is the monomial test
valuation with weight e_j in the Taylor coordinates of the chart centred at p.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential TensorProduct
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {n : ℕ}

section Algebra

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The Jacobian criterion: over a formally smooth algebra, coordinates whose differentials form
a basis of the Kähler differentials are formally étale. -/
theorem formallyEtale_of_kaehlerBasis [Algebra.FormallySmooth K A]
    (y : MvPolynomial (Fin n) K →ₐ[K] A) (b : Module.Basis (Fin n) A Ω[A⁄K])
    (hb : ∀ i, b i = D K A (y (MvPolynomial.X i))) : y.toRingHom.FormallyEtale := by
  let P := MvPolynomial (Fin n) K
  let _ : Algebra P A := y.toRingHom.toAlgebra
  have : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq fun c => (y.commutes c).symm
  let b₁ : Module.Basis (Fin n) A (A ⊗[P] Ω[P⁄K]) := (mvPolynomialBasis K (Fin n)).baseChange A
  have hmap : ∀ i, mapBaseChange K P A (b₁ i) = b i := by
    intro i
    rw [Module.Basis.baseChange_apply, mapBaseChange_tmul, one_smul, mvPolynomialBasis_apply,
      map_D, hb i]
    rfl
  have hbij : Function.Bijective (mapBaseChange K P A) := by
    have heq : mapBaseChange K P A = (b₁.equiv b (Equiv.refl _)).toLinearMap :=
      b₁.ext fun i => by
        rw [hmap i, LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
    rw [heq]
    exact (b₁.equiv b (Equiv.refl _)).bijective
  have hΩ : Subsingleton Ω[A⁄P] := by
    have key : ∀ ω : Ω[A⁄P], ω = 0 := by
      intro ω
      obtain ⟨ω₁, rfl⟩ := KaehlerDifferential.map_surjective K P A ω
      obtain ⟨t, rfl⟩ := hbij.2 ω₁
      exact (KaehlerDifferential.exact_mapBaseChange_map K P A _).mpr ⟨t, rfl⟩
    exact ⟨fun ω ω' => by rw [key ω, key ω']⟩
  have hH1 : Subsingleton (Algebra.H1Cotangent P A) := by
    have key : ∀ z : Algebra.H1Cotangent P A, z = 0 := by
      intro z
      have hδ : Algebra.H1Cotangent.δ K P A z = 0 := by
        apply hbij.1
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange K P A _).mpr ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ K P A _).mp hδ
      rw [Subsingleton.elim w 0, map_zero]
    exact ⟨fun z z' => by rw [key z, key z']⟩
  change Algebra.FormallyEtale P A
  exact ⟨hΩ, hH1⟩

/-- The determinant of a basis with one vector replaced is the coordinate of the new vector. -/
theorem basis_det_update {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module A M]
    (e : Module.Basis ι A M) (j : ι) (w : M) :
    e.det (Function.update e j w) = e.repr w j := by
  have hsp : ⊤ ≤ Submodule.span A (Set.range e) := by rw [e.span_eq]
  have h1 := e.det_smul_mk_coord_eq_det_update e.linearIndependent hsp j
  have hmk : Module.Basis.mk e.linearIndependent hsp = e :=
    Module.Basis.eq_of_apply_eq fun i => Module.Basis.mk_apply _ _ i
  rw [Module.Basis.det_self, one_smul, hmk] at h1
  have h2 := LinearMap.congr_fun h1 w
  rw [MultilinearMap.toLinearMap_apply] at h2
  rw [← Module.Basis.coord_apply, h2]
  rfl

/-- Replacing the j-th étale coordinate by h with ∂h/∂x_j a unit gives étale coordinates. -/
theorem etaleCoordinates_replace (x : MvPolynomial (Fin n) K →ₐ[K] A)
    (hx : x.toRingHom.FormallyEtale) (j : Fin n) (h : A)
    (hj : IsUnit (etaleCoordinateDerivation x hx j h)) :
    (MvPolynomial.aeval (Function.update (fun i => x (MvPolynomial.X i)) j h) :
      MvPolynomial (Fin n) K →ₐ[K] A).toRingHom.FormallyEtale := by
  have hsm : Algebra.FormallySmooth K A := by
    let _ := x.toRingHom.toAlgebra
    have : IsScalarTower K (MvPolynomial (Fin n) K) A :=
      IsScalarTower.of_algebraMap_eq fun c => (x.commutes c).symm
    have : Algebra.FormallyEtale (MvPolynomial (Fin n) K) A := hx
    exact Algebra.FormallySmooth.comp K (MvPolynomial (Fin n) K) A
  set e := etaleCoordinateBasis x hx with he
  have hdet : e.det (Function.update e j (D K A h)) = etaleCoordinateDerivation x hx j h := by
    rw [basis_det_update]
    rfl
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr (by rw [hdet]; exact hj)
  refine formallyEtale_of_kaehlerBasis _ (Module.Basis.mk hli hsp.ge) fun i => ?_
  rw [Module.Basis.mk_apply, MvPolynomial.aeval_X]
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hij, Function.update_of_ne hij, he, etaleCoordinateBasis_apply]

end Algebra

section Scheme

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- The restriction of sections to the basic open of f, as a K-algebra map. -/
noncomputable def sectionBasicOpenRestrict {U : X.Opens} (f : Γ(X, U)) :
    Γ(X, U) →ₐ[K] Γ(X, X.basicOpen f) where
  toRingHom := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  commutes' k := by
    change (X.presheaf.map (homOfLE (X.basicOpen_le f) : X.basicOpen f ⟶ U).op).hom
        (((X.baseRingToStructurePresheaf K).app (op U)).hom k) =
      ((X.baseRingToStructurePresheaf K).app (op (X.basicOpen f))).hom k
    rw [← CommRingCat.comp_apply, ← (X.baseRingToStructurePresheaf K).naturality]
    rfl

theorem sectionBasicOpenRestrict_formallyEtale {U : X.Opens} (hU : IsAffineOpen U)
    (f : Γ(X, U)) : (sectionBasicOpenRestrict (K := K) f).toRingHom.FormallyEtale := by
  have := hU.isLocalization_basicOpen f
  have : Algebra.FormallyEtale Γ(X, U) Γ(X, X.basicOpen f) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers f)
  exact RingHom.formallyEtale_algebraMap.mpr this

/-- The chart on the basic open of ∂h/∂x_j whose j-th coordinate is h. -/
noncomputable def etaleChartReplace (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h))) :
    EtaleChart K X n where
  U := X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h)
  isAffine := c.isAffine.basicOpen _
  nonempty := hne
  coords := MvPolynomial.aeval (Function.update
    (fun i => sectionBasicOpenRestrict (K := K) (etaleCoordinateDerivation c.coords c.formallyEtale j h)
      (c.coords (MvPolynomial.X i))) j
    (sectionBasicOpenRestrict (K := K) (etaleCoordinateDerivation c.coords c.formallyEtale j h) h))
  formallyEtale := by
    set f := etaleCoordinateDerivation c.coords c.formallyEtale j h
    have hσ := sectionBasicOpenRestrict_formallyEtale (K := K) c.isAffine f
    have hσx := formallyEtale_comp (sectionBasicOpenRestrict (K := K) f) hσ c.coords c.formallyEtale
    refine etaleCoordinates_replace ((sectionBasicOpenRestrict (K := K) f).comp c.coords) hσx j
      (sectionBasicOpenRestrict (K := K) f h) ?_
    rw [etaleCoordinateDerivation_comp (sectionBasicOpenRestrict (K := K) f) c.coords
      c.formallyEtale hσx j h]
    exact RingedSpace.isUnit_res_basicOpen _ f

theorem etaleChartReplace_coords_self (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h))) :
    (etaleChartReplace c j h hne).coords (MvPolynomial.X j) =
      sectionBasicOpenRestrict (K := K) (etaleCoordinateDerivation c.coords c.formallyEtale j h) h := by
  change MvPolynomial.aeval _ (MvPolynomial.X j) = _
  rw [MvPolynomial.aeval_X, Function.update_self]

theorem etaleChartReplace_coords_ne (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h)))
    {i : Fin n} (hij : i ≠ j) :
    (etaleChartReplace c j h hne).coords (MvPolynomial.X i) =
      sectionBasicOpenRestrict (K := K) (etaleCoordinateDerivation c.coords c.formallyEtale j h)
        (c.coords (MvPolynomial.X i)) := by
  change MvPolynomial.aeval _ (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X, Function.update_of_ne hij]

/-- The divisor {h = 0} is a coordinate hyperplane near p and its valuation is a monomial test
valuation: if ∂h/∂x_j does not vanish at p, h vanishes at p and is prime in the local ring, then
in the Taylor coordinates of the replaced chart centred at p the order along (h) is the weighted
order with weight e_j. -/
theorem etaleChartReplace_divisorValuation [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U)) (p : X) (hp : p ∈ c.U)
    (hpj : p ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h))
    (β : X.presheaf.stalk p →ₐ[K] K) (hβ : β (X.presheaf.germ c.U p hp h) = 0)
    [IsDomain (X.presheaf.stalk p)] [IsNoetherianRing (X.presheaf.stalk p)]
    (hprime : Prime (X.presheaf.germ c.U p hp h))
    [(Ideal.span {X.presheaf.germ c.U p hp h}).IsPrime] (S : Type*) [CommRing S]
    [Algebra (X.presheaf.stalk p) S] [IsLocalization.AtPrime S (Ideal.span {X.presheaf.germ c.U p hp h})]
    [IsLocalRing S] (g : X.presheaf.stalk p) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p)) (X.presheaf.stalk p) ≃ₐ[K]
        MvPowerSeries (Fin n) K,
      localAdicOrder S (algebraMap (X.presheaf.stalk p) S g) =
        (e (algebraMap _ (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk p))
          (X.presheaf.stalk p)) g)).weightedOrder (Pi.single j 1) := by
  let c' := etaleChartReplace c j h ⟨⟨p, hpj⟩⟩
  obtain ⟨e, he, -⟩ := etaleChart_exists_taylorCoordinates c' p hpj β
  refine ⟨e, localAdicOrder_localization_eq_weightedOrder e hprime j ?_ S g⟩
  have hgerm : etaleChartStalkCoords c' p hpj (MvPolynomial.X j) = X.presheaf.germ c.U p hp h := by
    change X.presheaf.germ c'.U p hpj (c'.coords (MvPolynomial.X j)) = _
    rw [etaleChartReplace_coords_self]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have hcent := etaleChartCenteredStalkCoords_variable c' p hpj β j
  have hα : rationalAffineGermPoint (U := c'.U) p hpj β (c'.coords (MvPolynomial.X j)) = 0 := by
    change β (X.presheaf.germ c'.U p hpj (c'.coords (MvPolynomial.X j))) = 0
    rw [show X.presheaf.germ c'.U p hpj (c'.coords (MvPolynomial.X j)) =
      etaleChartStalkCoords c' p hpj (MvPolynomial.X j) from rfl, hgerm, hβ]
  rw [hα, map_zero, sub_zero, hgerm] at hcent
  have h1 := he j
  rw [hcent, stalkTaylorExpansion_apply] at h1
  exact h1

end Scheme

end MixedFujita

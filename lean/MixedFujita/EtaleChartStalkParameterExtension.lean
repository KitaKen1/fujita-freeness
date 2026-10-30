/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentCartier
public import Hironaka.Scheme.Snc.EtaleParameters
public import Hironaka.Algebra.Local.Defs

/-!
Vanishing etale coordinate germs extend to a regular system of parameters at
any actual stalk, including nonclosed points of smaller local dimension.
Transport the localized coordinate theorem along the affine stalk isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierBaseOpenAlgebra

/-- Vanishing etale coordinates extend to actual stalk parameters at any point. -/
theorem etaleChart_exists_stalk_regular_parameters
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) :
    let q := (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal
    ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x), IsRegularSystemOfParameters z ∧
      ∃ σ : {a : Fin n // c.coords (MvPolynomial.X a) ∈ q} → Fin m,
        Function.Injective σ ∧ ∀ a, z (σ a) =
          X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a.1)) := by
  let q := (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal
  have hy : (MvPolynomial.aeval (R := K)
      (fun a => c.coords (MvPolynomial.X a))).toRingHom.Etale := by
    have h : MvPolynomial.aeval (R := K) (fun a => c.coords (MvPolynomial.X a)) = c.coords := by
      ext a
      simp
    rw [h]
    letI := c.coords.toRingHom.toAlgebra
    exact etaleChart_coords_etale c
  obtain ⟨hreg, m, z, hz, σ, hinj, hσ⟩ :=
    exists_span_eq_maximalIdeal_of_etale_coordinates (fun a => c.coords (MvPolynomial.X a)) hy q
  letI := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  letI := c.isAffine.isLocalization_stalk ⟨x, hx⟩
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x)
  refine ⟨m, fun i => e (z i), ⟨?_, ?_⟩, σ, hinj, ?_⟩
  · change Ideal.span (Set.range (e.toRingEquiv ∘ z)) = _
    rw [Set.range_comp, ← Ideal.map_span, hz.1, map_ringEquiv_maximalIdeal]
  · exact hz.2.trans (ringKrullDim_eq_of_ringEquiv e.toRingEquiv)
  · intro a
    change e (z (σ a)) = _
    rw [hσ a]
    exact e.commutes _

end MixedFujita

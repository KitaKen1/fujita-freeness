/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveCoherentPresentation

/-! 同じ有限表示の十分大きい全捻りの実切断全射性。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A finite free actual module sheaf is coherent on any scheme. -/
theorem unitBiproduct_isCoherent (X : Scheme.{u}) (k : ℕ) :
    (CohomologyAux.unitBiproduct X k).IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := by
    apply CohomologyAux.isFiniteType_of_finite_sections _
      (fun U : X.affineOpens => U.1) (iSup_affineOpens_eq_top X) (fun U => U.2)
    intro U
    exact CohomologyAux.finite_sections_unitBiproduct k U.1


/-- A fixed constructed negative-twist presentation becomes surjective on
actual global sections after every sufficiently large integer twist. No
vanishing, presentation or cohomology-finiteness premise is supplied. -/
theorem projectivelyEmbedded_coherent_exists_epi_negative_twist_sections_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} {X : Scheme.{u}}
    (e : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion e] (M : X.Modules) [M.IsCoherent] :
    ∃ (m k : ℕ) (π :
      ((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).twist
        (CohomologyAux.unitBiproduct X k) (-(m : ℤ)) ⟶ M), Epi π ∧
      ∃ n₀ : ℤ, ∀ n ≥ n₀, Function.Surjective (Scheme.Modules.Hom.app
        (((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).twistMap n π) ⊤) := by
  let L := (projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e
  obtain ⟨m, k, π, hπ⟩ := projectivelyEmbedded_coherent_exists_epi_negative_twist e M
  let := hπ
  have := polynomialProjectiveToBase_isProper (r + 1) A
  let : IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveToBase (r + 1) A)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian e
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (CohomologyAux.unitBiproduct X k).IsCoherent := unitBiproduct_isCoherent X k
  have hS : (ShortComplex.kernelSequence π).ShortExact := CohomologyAux.shortExact_kernelSequence π
  let : (ShortComplex.kernelSequence π).X₁.IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_kernel π
  let : (ShortComplex.kernelSequence π).X₂.IsCoherent := by
    change (L.twist (CohomologyAux.unitBiproduct X k) (-(m : ℤ))).IsCoherent
    infer_instance
  let : (ShortComplex.kernelSequence π).X₁.IsCoherent :=
    CohomologyAux.isCoherent_X₁_of_shortExact hS
  obtain ⟨n₀, hn₀⟩ := projectivelyEmbedded_actual_coherent_serreVanishing e
    (ShortComplex.kernelSequence π).X₁
  refine ⟨m, k, π, hπ, n₀, fun n hn => ?_⟩
  have hSt := Scheme.LineBundle.shortExact_map_twistFunctor L n hS
  have hvan : Subsingleton (Scheme.Modules.Cohomology (L.twist (kernel π) n) 1) := hn₀ n hn 0
  intro s
  exact Scheme.Modules.sections_surjective hSt hvan s

end MixedFujita

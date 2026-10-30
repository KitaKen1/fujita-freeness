/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedImmersionModuleCounit
public import MixedFujita.SGATwistPullbackIso

/-! 射影閉部分スキームの連接層の実有限表示。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every actual coherent sheaf on a closed projective subscheme is a quotient
of the pulled-back finite sum of negative hyperplane powers. The presentation
and its epimorphism are constructed, rather than supplied as a hypothesis. -/
theorem projectivelyEmbedded_coherent_exists_epi_pulled_negative_twist
    {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} {X : Scheme.{u}}
    (e : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion e] (M : X.Modules) [M.IsCoherent] :
    ∃ (m k : ℕ) (π : (Scheme.Modules.pullback e).obj
      ((projectiveSpace.twistingBundle (Fin (r + 1)) A).twist
        (CohomologyAux.unitBiproduct
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) k) (-(m : ℤ))) ⟶ M),
      Epi π := by
  obtain ⟨m, k, π, hπ⟩ := projectiveSpace.exists_epi_twist
    (projectiveSpace.IsStdFinite.pushforward e M)
  let := hπ
  let : (Scheme.Modules.pullback e).IsLeftAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction e).isLeftAdjoint
  have hmap : Epi ((Scheme.Modules.pullback e).map π) :=
    (Scheme.Modules.pullback e).map_epi π
  have hc : Epi ((Scheme.Modules.pullbackPushforwardAdjunction e).counit.app M) :=
    closedImmersion_module_counit_epi e M
  exact ⟨m, k, (Scheme.Modules.pullback e).map π ≫
    (Scheme.Modules.pullbackPushforwardAdjunction e).counit.app M, inferInstance⟩


/-- The negative-twist finite presentation is intrinsic to the pulled hyperplane
bundle on the actual projective subscheme; no ambient module remains in the domain. -/
theorem projectivelyEmbedded_coherent_exists_epi_negative_twist
    {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} {X : Scheme.{u}}
    (e : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion e] (M : X.Modules) [M.IsCoherent] :
    ∃ (m k : ℕ) (π :
      ((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).twist
        (CohomologyAux.unitBiproduct X k) (-(m : ℤ)) ⟶ M), Epi π := by
  obtain ⟨m, k, π, hπ⟩ := projectivelyEmbedded_coherent_exists_epi_pulled_negative_twist e M
  let := hπ
  exact ⟨m, k, (sgaTwistUnitBiproductPullbackIso
    (projectiveSpace.twistingBundle (Fin (r + 1)) A) e (-(m : ℤ)) k).inv ≫ π, inferInstance⟩

end MixedFujita

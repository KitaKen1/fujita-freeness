/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACartierTwistPowers
public import MixedFujita.ProperCartierCohomology
public import MixedFujita.ClosedImmersionCohomology

/-! Transfer proved SGA Serre vanishing through the actual projection formula, closed-immersion cohomology and scalar-compatible comparisons. For an actual projective closed immersion over a noetherian ring, coherent twists and actual tensor products vanish in every positive degree beyond one threshold. On an integral source construct one fixed actual Cartier representative H of the pulled hyperplane line and obtain eventual vanishing for every D+jH. Arbitrary CartierIsAmpleProj divisors still require their embedding/polarization dictionary; Kodaira and Kawamata--Viehweg vanishing remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
namespace MixedFujita
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
noncomputable def actualCohomologyLinearEquivOfIso {X : Scheme.{u}}
    {M N : X.Modules} (a : M ≅ N) (q : ℕ) :
    Scheme.Modules.Cohomology M q ≃ₗ[Γ(X, ⊤)] Scheme.Modules.Cohomology N q :=
  LinearEquiv.ofLinearMap (Scheme.Modules.cohomologyMapLinear a.hom q)
    (Scheme.Modules.cohomologyMapLinear a.inv q)
    (by rw [← Scheme.Modules.cohomologyMapLinear_comp, a.inv_hom_id,
      Scheme.Modules.cohomologyMapLinear_id])
    (by rw [← Scheme.Modules.cohomologyMapLinear_comp, a.hom_inv_id,
      Scheme.Modules.cohomologyMapLinear_id])

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}
  {X : Scheme.{u}}
  (e : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  [IsClosedImmersion e]

theorem projectivelyEmbedded_actual_coherent_serreVanishing
    (M : X.Modules) [M.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology
        (((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).twist M n) (q + 1)) := by
  obtain ⟨n₀, hn₀⟩ := projectiveSpace.exists_H_twist_subsingleton
    (projectiveSpace.IsStdFinite.pushforward e M)
  refine ⟨n₀, fun n hn q => ?_⟩
  let L := projectiveSpace.twistingBundle (Fin (r + 1)) A
  letI := hn₀ n hn q
  letI : Subsingleton (Scheme.Modules.Cohomology
      (L.twist ((Scheme.Modules.pushforward e).obj M) n) (q + 1)) :=
    (sgaCohomologyLinearEquiv _ (q + 1)).symm.subsingleton
  letI : Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward e).obj ((L.pullback e).twist M n)) (q + 1)) :=
    (actualCohomologyLinearEquivOfIso (L.twistPushforwardIso e M n) (q + 1)).subsingleton
  exact (closedImmersionCohomologyAddEquiv e ((L.pullback e).twist M n) (q + 1)).symm.subsingleton

theorem projectivelyEmbedded_actual_tensor_serreVanishing
    (M : X.Modules) [M.IsCoherent] :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology
        ((((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).toModules n) ⊗ M)
        (q + 1)) := by
  obtain ⟨n₀, hn₀⟩ := projectivelyEmbedded_actual_coherent_serreVanishing e M
  refine ⟨n₀, fun n hn q => ?_⟩
  letI := hn₀ n hn q
  exact (actualCohomologyLinearEquivOfIso
    (sgaTwistTensorIso _ M n) (q + 1)).subsingleton

variable [IsIntegral X]

theorem projectivelyEmbedded_cartier_tensor_serreVanishing_of_one_iso
    (H : CartierDivisor X)
    (hH : ((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).toModules 1 ≅ H.sheaf)
    (M : X.Modules) [M.IsCoherent] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology ((j • H).sheaf ⊗ M) (q + 1)) := by
  obtain ⟨n₀, hn₀⟩ := projectivelyEmbedded_actual_tensor_serreVanishing e M
  refine ⟨n₀.toNat, fun j hj q => ?_⟩
  have hj' : n₀ ≤ (j : ℤ) := by omega
  letI := hn₀ j hj' q
  exact (actualCohomologyLinearEquivOfIso
    (tensorIso (sgaLineBundleNatPowerCartierIso _ H hH j) (Iso.refl M))
    (q + 1)).symm.subsingleton

theorem projectivelyEmbedded_cartier_serreVanishing_of_one_iso
    (H : CartierDivisor X)
    (hH : ((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).toModules 1 ≅ H.sheaf)
    (D : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (D + j • H).sheaf (q + 1)) := by
  letI := D.isInvertible_sheaf
  letI := invertible_module_isCoherent D.sheaf
  obtain ⟨n₀, hn₀⟩ := projectivelyEmbedded_actual_coherent_serreVanishing e D.sheaf
  refine ⟨n₀.toNat, fun j hj q => ?_⟩
  have hj' : n₀ ≤ (j : ℤ) := by omega
  letI := hn₀ j hj' q
  exact (actualCohomologyLinearEquivOfIso
    (sgaLineBundleCartierTwistIso _ H hH D j) (q + 1)).symm.subsingleton

theorem projectivelyEmbedded_exists_fixed_cartier_serre_polarization :
    ∃ H : CartierDivisor X,
      Nonempty (((projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e).toModules 1 ≅ H.sheaf) ∧
      ∀ D : CartierDivisor X, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
        Subsingleton (Scheme.Modules.Cohomology (D + j • H).sheaf (q + 1)) := by
  let L := (projectiveSpace.twistingBundle (Fin (r + 1)) A).pullback e
  exact ⟨sgaLineBundleCartierDivisor L, ⟨sgaLineBundleCartierIso L⟩,
    fun D => projectivelyEmbedded_cartier_serreVanishing_of_one_iso e _ (sgaLineBundleCartierIso L) D⟩

end MixedFujita

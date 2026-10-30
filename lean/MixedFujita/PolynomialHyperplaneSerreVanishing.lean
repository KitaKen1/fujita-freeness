/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialSGAFrameComparison

/-! Apply actual Cartier projection formula on the ambient projective space and the existing homogeneous-Cartier sheaf pullback for arbitrary morphisms. Serre vanishing therefore holds for the specified actual hyperplane Cartier divisor of any integral projectively embedded source over a noetherian domain, without a dominance assumption. Higher degree is uniform beyond one twist threshold. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
open TauCeti.AlgebraicGeometry
universe u

theorem polynomialProjective_nonzero_avoids_genericPoint
    {R : Type u} [CommRing R] [IsDomain R] {n : ℕ}
    [IsIntegral (polynomialProjectiveScheme n R)] (k : Fin n)
    (g : MvPolynomial (Fin n) R) (hg : g ≠ 0) :
    g ∉ (genericPoint (polynomialProjectiveScheme n R)).asHomogeneousIdeal := by
  let V := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) g
  letI : Nonempty V := ⟨⟨polynomialProjectiveZeroPoint R k, by
    change g ∉ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin n) R))
    intro h
    have h' : g ∈ (⊥ : Ideal (MvPolynomial (Fin n) R)) := h
    exact hg (Ideal.mem_bot.mp h')⟩⟩
  exact integral_genericPoint_mem_nonempty_open V

theorem projectivelyEmbedded_cartier_tensor_serreVanishing_of_ambient_iso
    {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
    [IsIntegral (polynomialProjectiveScheme (r + 1) R)]
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme (r + 1) R) [IsClosedImmersion e]
    (J : CartierDivisor (polynomialProjectiveScheme (r + 1) R)) (H : CartierDivisor X)
    (a : (projectiveSpace.twistingBundle (Fin (r + 1)) R).toModules 1 ≅ J.sheaf)
    (b : (Scheme.Modules.pullback e).obj J.sheaf ≅ H.sheaf)
    (M : X.Modules) [M.IsCoherent] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology ((j • H).sheaf ⊗ M) (q + 1)) := by
  let L := projectiveSpace.twistingBundle (Fin (r + 1)) R
  obtain ⟨n₀, hn₀⟩ := projectiveSpace.exists_H_twist_subsingleton
    (projectiveSpace.IsStdFinite.pushforward e M)
  refine ⟨n₀.toNat, fun j hj q => ?_⟩
  have hj' : n₀ ≤ (j : ℤ) := by omega
  letI := hn₀ j hj' q
  letI : Subsingleton (Scheme.Modules.Cohomology
      (L.twist ((Scheme.Modules.pushforward e).obj M) j) (q + 1)) :=
    (sgaCohomologyLinearEquiv _ (q + 1)).symm.subsingleton
  let c : L.twist ((Scheme.Modules.pushforward e).obj M) j ≅
      (Scheme.Modules.pushforward e).obj ((j • H).sheaf ⊗ M) :=
    (sgaTwistTensorIso L _ j).symm ≪≫
      tensorIso (sgaLineBundleNatPowerCartierIso L J a j) (Iso.refl _) ≪≫
      cartierProjectionFormulaIso (j • J) e M ≪≫
      (Scheme.Modules.pushforward e).mapIso
        (tensorIso (cartierPullbackGradedIso J e H b j) (Iso.refl M))
  letI : Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward e).obj ((j • H).sheaf ⊗ M)) (q + 1)) :=
    (actualCohomologyLinearEquivOfIso c (q + 1)).symm.subsingleton
  exact (closedImmersionCohomologyAddEquiv e ((j • H).sheaf ⊗ M) (q + 1)).symm.subsingleton

theorem projectiveHyperplane_tensor_serreVanishing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {r : ℕ}
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme (r + 1) R) [IsClosedImmersion e]
    (g : MvPolynomial (Fin (r + 1)) R) (hg : g.IsHomogeneous 1)
    (hgX : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (M : X.Modules) [M.IsCoherent] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology
        ((j • projectiveHyperplaneCartier e g hg hgX).sheaf ⊗ M) (q + 1)) := by
  let P := polynomialProjectiveScheme (r + 1) R
  letI : IsIntegral P := polynomialProjectiveScheme_isIntegral R (0 : Fin (r + 1))
  have hg0 : g ≠ 0 := by
    intro h
    apply hgX
    rw [h]
    exact (e (genericPoint X)).asHomogeneousIdeal.zero_mem
  have hgP := polynomialProjective_nonzero_avoids_genericPoint (0 : Fin (r + 1)) g hg0
  let J := projectiveHyperplaneCartier (𝟙 P) g hg hgP
  let b : (Scheme.Modules.pullback e).obj J.sheaf ≅
      (projectiveHyperplaneCartier e g hg hgX).sheaf := by
    simpa only [Category.comp_id] using
      projectiveHomogeneousCartierPullbackIso (𝟙 P) e 1 g hg one_pos hgP hgX
  exact projectivelyEmbedded_cartier_tensor_serreVanishing_of_ambient_iso e J _
    (polynomialHyperplaneSGAModuleIso g hg hgP).symm b M

theorem projectiveHyperplane_cartier_serreVanishing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme n R) [IsClosedImmersion e]
    (g : MvPolynomial (Fin n) R) (hg : g.IsHomogeneous 1)
    (hgX : g ∉ (e (genericPoint X)).asHomogeneousIdeal) (D : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology
        (D + j • projectiveHyperplaneCartier e g hg hgX).sheaf (q + 1)) := by
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := polynomialProjective_exists_coordinate_chart n R (e (genericPoint X))
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  letI := D.isInvertible_sheaf
  letI := invertible_module_isCoherent D.sheaf
  obtain ⟨j₀, hj₀⟩ := projectiveHyperplane_tensor_serreVanishing e g hg hgX D.sheaf
  refine ⟨j₀, fun j hj q => ?_⟩
  letI := hj₀ j hj q
  exact (actualCohomologyLinearEquivOfIso
    (cartierTensorSheafIso (j • projectiveHyperplaneCartier e g hg hgX) D ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (add_comm _ D))) (q + 1)).symm.subsingleton

end MixedFujita

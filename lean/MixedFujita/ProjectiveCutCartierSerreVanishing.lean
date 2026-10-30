/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PulledLineBundlePowerIsomorphisms
public import MixedFujita.ActualCartierSerreVanishing

/-! 非被約切断上の正の超平面冪から全剰余類の実Serre消滅。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- On an actual possibly NONREDUCED closed projective source, a single
hyperplane isomorphism for the pulled Cartier direction supplies Serre
vanishing for every fixed affine twist and ALL positive cohomology degrees. -/
theorem projective_cut_pulled_affine_cartier_serreVanishing
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    (p : Y ⟶ X) (H E : CartierDivisor X) (r : ℕ)
    (e : Y ⟶ polynomialProjectiveScheme (r + 1) K) [IsClosedImmersion e]
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅
      ((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules 1) :
    ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j → ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj (E + j • H).sheaf) (q + 1)) := by
  let : IsProper (polynomialProjectiveToBase (r + 1) K) := polynomialProjectiveToBase_isProper (r + 1) K
  let : IsLocallyNoetherian (polynomialProjectiveScheme (r + 1) K) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveToBase (r + 1) K)
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian e
  let P := (Scheme.Modules.pullback p).obj E.sheaf
  let : SheafOfModules.isInvertible Y P := cartierPullbackSheaf_isInvertible E p
  let : P.IsCoherent := invertible_module_isCoherent _
  obtain ⟨j₀, hj₀⟩ := projectivelyEmbedded_actual_coherent_serreVanishing e P
  refine ⟨j₀.toNat, ?_⟩
  intro j hj q
  let := hj₀ j (by omega) q
  exact (actualCohomologyLinearEquivOfIso
    (cartierPulledSGAAffinePowerIso p H E _ a j) (q + 1)).subsingleton


/-- A positive power of the original Cartier direction being an actual
hyperplane on the cut supplies eventual vanishing for ALL original powers.
The finitely many residue thresholds are constructed internally. -/
theorem projective_cut_positive_power_eventually_cartier_cohomology_vanish
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    (p : Y ⟶ X) (G E : CartierDivisor X) (d : ℕ) (hd : 0 < d) (r : ℕ)
    (e : Y ⟶ polynomialProjectiveScheme (r + 1) K) [IsClosedImmersion e]
    (a : (Scheme.Modules.pullback p).obj (d • G).sheaf ≅
      ((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules 1) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj (E + m • G).sheaf) (q + 1)) := by
  choose j₀ hj₀ using fun b : Fin d =>
    projective_cut_pulled_affine_cartier_serreVanishing K p (d • G) (E + b.val • G) r e a
  let B := Finset.univ.sup j₀
  refine ⟨B * d, ?_⟩
  intro m hm q
  let b : Fin d := ⟨m % d, Nat.mod_lt m hd⟩
  have hj : j₀ b ≤ m / d :=
    (Finset.le_sup (f := j₀) (Finset.mem_univ b)).trans
      ((Nat.le_div_iff_mul_le hd).mpr hm)
  have he : (E + b.val • G) + (m / d) • (d • G) = E + m • G := by
    rw [add_assoc, smul_smul, ← add_nsmul]
    exact congrArg (fun k => E + k • G) (by simpa only [b, Nat.mul_comm] using Nat.mod_add_div m d)
  have h := hj₀ b (m / d) hj q
  exact he ▸ h

end MixedFujita

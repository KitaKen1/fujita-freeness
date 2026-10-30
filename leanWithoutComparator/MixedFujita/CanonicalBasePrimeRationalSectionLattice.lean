/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasePrimeCartierLattice
public import MixedFujita.CartierRationalUnitSections
public import MixedFujita.CanonicalBasePrimeRoundupIntegerBound

/-!
Internally construct one actual SNC source and roundup whose actual nearby
section lattice, for every base Cartier twist and every nonzero base rational
function, is determined by the canonical discriminant roundup. The normalized
effective reference divisor is supplied; the tested divisors and functions
have no support, effectivity, or order sign restriction. No whole-sheaf
extension or reflexivity is inferred from this codimension-one dictionary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (η : CodimensionOnePoint Y)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
  (H : CartierDivisor Y) (hH : H.IsEffective) (hHη : cartierCoefficient H (η : Y) = 1)

include hH hHη

/-- One internally constructed actual roundup computes all Cartier twists and
all nonzero rational base functions by the canonical discriminant coefficient. -/
theorem exists_snc_roundup_canonical_base_prime_cartier_and_rational_lattice :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (E : CartierDivisor T),
      E.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
        ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      (∀ L : CartierDivisor Y,
        (∃ U : Y.Opens, (η : Y) ∈ U ∧
          Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
            (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U)) ∈
              (E + cartierPullback (ρ ≫ g) L).sections ((ρ ≫ g) ⁻¹ᵁ U)) ↔
          0 ≤ cartierCoefficient L (η : Y) +
            ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉) ∧
      ∀ u : Y.functionFieldˣ,
        (∃ U : Y.Opens, (η : Y) ∈ U ∧
          Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
            ((dominantFunctionFieldMap (ρ ≫ g)).hom (u : Y.functionField))) ((ρ ≫ g) ⁻¹ᵁ U)
            (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
              (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U))) ∈ E.sections ((ρ ≫ g) ⁻¹ᵁ U)) ↔
          0 ≤ Y.ord (u : Y.functionField) (η : Y) +
            ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉ := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, E, heff, hE, htest⟩ :=
    exists_snc_roundup_canonical_base_prime_integer_bound g hnormY η c f d hd D hklt H hH hHη
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  letI := hnormY (η : Y)
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hL := base_prime_cartier_neighborhood_lattice_of_integer_cutoff hnormT (ρ ≫ g) η
    H hH hHη E heff _ htest
  refine ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, E, heff, hE, hL, ?_⟩
  intro u
  let v : T.functionFieldˣ := Units.map (dominantFunctionFieldMap (ρ ≫ g)).hom.toMonoidHom u
  have hmem (U : Y.Opens) :
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
        ((dominantFunctionFieldMap (ρ ≫ g)).hom (u : Y.functionField))) ((ρ ≫ g) ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
          (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U))) ∈ E.sections ((ρ ≫ g) ⁻¹ᵁ U) ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
        (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U)) ∈
          (E + cartierPullback (ρ ≫ g) (principalCartierDivisor Y u)).sections
            ((ρ ≫ g) ⁻¹ᵁ U) := by
    rw [cartierPullback_principal]
    exact cartier_rational_unit_mem_sections_iff_unit_of_add_principal E v _
  have hprincipal := hL (principalCartierDivisor Y u)
  rw [cartierCoefficient_principal] at hprincipal
  refine Iff.trans ?_ hprincipal
  exact exists_congr (fun U : Y.Opens => and_congr_right (fun _ => hmem U))

end MixedFujita

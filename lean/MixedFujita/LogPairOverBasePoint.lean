/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalThresholdLogCanonical

/-!
All-model discrepancy predicates at a specified point of a base. A test prime
is relevant when its image specializes to that base point. These predicates
retain actual proper smooth birational tests; no finite-model criterion is
built into their definitions. Restriction to an actual open subscheme is a
separate geometric dictionary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- All-model klt for test primes whose base images specialize to the given point. -/
def LogPairIsKltOverBasePoint (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cT : EtaleChart K T n)
    (t : T), Order.coheight t = 1 → η ∈ closure ({(ρ ≫ g) t} : Set Y) →
      -(d : ℤ) < cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t

/-- The analogous non-strict all-model log-canonical condition. -/
def LogPairIsLogCanonicalOverBasePoint (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))] (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (cT : EtaleChart K T n)
    (t : T), Order.coheight t = 1 → η ∈ closure ({(ρ ≫ g) t} : Set Y) →
      -(d : ℤ) ≤ cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t

theorem logPairIsKlt_overBasePoint (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (h : LogPairIsKlt c f d D) :
    LogPairIsKltOverBasePoint g η c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht _
  exact h T ρ hρ cT t ht

theorem logPairIsLogCanonical_overBasePoint (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (h : LogPairIsLogCanonical c f d D) :
    LogPairIsLogCanonicalOverBasePoint g η c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht _
  exact h T ρ hρ cT t ht

theorem logPairIsKltOverBasePoint_logCanonical (g : X ⟶ Y) (η : Y)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (h : LogPairIsKltOverBasePoint g η c f d D) :
    LogPairIsLogCanonicalOverBasePoint g η c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht hη
  exact (h T ρ hρ cT t ht hη).le

theorem logPairIsKlt_iff_forall_basePoint (g : X ⟶ Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsKlt c f d D ↔ ∀ η, LogPairIsKltOverBasePoint g η c f d D := by
  constructor
  · exact fun h η => logPairIsKlt_overBasePoint g η c f d D h
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht
    exact h ((ρ ≫ g) t) T ρ hρ cT t ht (subset_closure (by simp))

theorem logPairIsLogCanonical_iff_forall_basePoint (g : X ⟶ Y) (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsLogCanonical c f d D ↔
      ∀ η, LogPairIsLogCanonicalOverBasePoint g η c f d D := by
  constructor
  · exact fun h η => logPairIsLogCanonical_overBasePoint g η c f d D h
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht
    exact h ((ρ ≫ g) t) T ρ hρ cT t ht (subset_closure (by simp))

/-- Klt at a point implies the condition at every generization of that point. -/
theorem logPairIsKltOverBasePoint_of_specializes (g : X ⟶ Y) {η η' : Y}
    (hη : η' ⤳ η) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (h : LogPairIsKltOverBasePoint g η c f d D) :
    LogPairIsKltOverBasePoint g η' c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht htη
  exact h T ρ hρ cT t ht
    (specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr htη).trans hη))

theorem logPairIsLogCanonicalOverBasePoint_of_specializes (g : X ⟶ Y) {η η' : Y}
    (hη : η' ⤳ η) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (h : LogPairIsLogCanonicalOverBasePoint g η c f d D) :
    LogPairIsLogCanonicalOverBasePoint g η' c f d D := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht htη
  exact h T ρ hρ cT t ht
    (specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr htη).trans hη))

end MixedFujita

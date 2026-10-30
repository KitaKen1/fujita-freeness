/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.CrepantBertiniPerturbationDescent
public import MixedFujita.CrepantAvoidingPerturbationDescent
public import MixedFujita.ArbitrarilySmallKltPerturbations
public import MixedFujita.FixedDivisorSmallKltPerturbations
public import MixedFujita.RationalAmpleKltPerturbations

/-!
Perturbations of klt pairs without a supplied model (steps 7, 8 and 15). The perturbation theorems
for a klt pair on an integral scheme X of finite type and separated over a field of characteristic
zero were proved from a given proper simple normal crossing model of the pair. Such a model exists,
also jointly with finitely many further Cartier divisors, so the model is no longer a hypothesis:
general members of a globally generated system, with finitely many points avoided and with
arbitrarily small coefficient; a fixed Cartier divisor with arbitrarily small coefficient; and
effective representatives of a rational multiple of an ample class.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A general member of a globally generated system, with coefficient k/d for k < d, keeps a klt
pair on a normal X klt. -/
theorem logPairIsKlt_exists_source_perturbation
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (k : ℕ) (hk : k < d) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      LogPairIsKlt c f d (D + k • cartierSectionZeroDivisor H s hs) := by
  have hXN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_source_perturbation_of_crepant_snc_model ρ hρ hnorm c f d D hklt cT
    H hH ξ hinj hcoh hsnc hsupp k hk

/-- The same with finitely many points of X avoided by the member. -/
theorem logPairIsKlt_exists_source_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (k : ℕ) (hk : k < d) (Z : Set X) (hZ : Z.Finite) :
    ∃ (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0),
      LogPairIsKlt c f d (D + k • cartierSectionZeroDivisor H s hs) ∧
        (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  have hXN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_source_perturbation_avoiding_of_crepant_snc_model ρ hρ hnorm c f d D
    hklt cT H hH ξ hinj hcoh hsnc hsupp k hk Z hZ

/-- A general member of a globally generated system with arbitrarily small coefficient 1/(m d),
avoiding finitely many points, keeps a klt pair on a normal X klt. -/
theorem logPairIsKlt_exists_small_source_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (Z : Set X) (hZ : Z.Finite) (ε : ℚ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0), 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  have hXN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_arbitrarily_small_source_perturbation_avoiding ρ hρ hnorm c f d hd D
    hklt cT H hH ξ hinj hcoh hsnc hsupp Z hZ ε hε

/-- A fixed Cartier divisor G with arbitrarily small coefficient 1/(m d) keeps a klt pair klt. -/
theorem logPairIsKlt_exists_small_fixed_divisor_perturbation
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧ LogPairIsKlt c f (m * d) (m • D + G) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hGsupp⟩ := exists_proper_snc_model_with c f d D (fun _ : Unit => G)
  exact logPairIsKlt_exists_arbitrarily_small_fixed_divisor_perturbation ρ hρ c f d hd D G hklt
    cT ξ hinj hcoh hsnc hsupp (hGsupp ()) ε hε

/-- An effective representative of the class (d/q) A of an ample A, with arbitrarily small
coefficient and avoiding finitely many points, keeps a klt pair on a normal X klt. -/
theorem logPairIsKlt_exists_rational_ample_perturbation
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ε : ℚ) (hε : 0 < ε) (Z : Set X) (hZ : Z.Finite) :
    ∃ (m r : ℕ) (s : Γ((r • A).sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      q • (m • D + cartierSectionZeroDivisor (r • A) s hs) =
        m • (q • D + d • A) +
          principalCartierDivisor X (cartierSectionUnit (r • A) s hs ^ q) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus (r • A) s) := by
  have hXN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, v, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_rational_ample_perturbation_avoiding ρ hρ hnorm c f d hd D hklt cT
    ξ hinj hcoh hsnc hsupp A hA q hq N ε hε Z hZ

section Effective

variable [IsLocallyNoetherian X]

/-- The perturbation by a general member with arbitrarily small coefficient also keeps the
boundary effective. -/
theorem logPairIsKlt_exists_small_effective_source_perturbation_avoiding
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (heff : LogPairBoundaryEffective c f d D)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (Z : Set X) (hZ : Z.Finite) (ε : ℚ) (hε : 0 < ε) :
    ∃ (m : ℕ) (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0), 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧
      1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor H s hs) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus H s) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_arbitrarily_small_effective_source_perturbation_avoiding ρ hρ hnorm
    c f d hd D hklt heff cT H hH ξ hinj hcoh hsnc hsupp Z hZ ε hε

/-- A fixed effective Cartier divisor with arbitrarily small coefficient keeps the pair klt and
its boundary effective. -/
theorem logPairIsKlt_exists_small_fixed_effective_divisor_perturbation
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (heff : LogPairBoundaryEffective c f d D) (hG : G.IsEffective) (ε : ℚ) (hε : 0 < ε) :
    ∃ m : ℕ, 2 ≤ m ∧ 0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d) (m • D + G) ∧
      LogPairIsKlt c f (m * d) (m • D + G) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hGsupp⟩ := exists_proper_snc_model_with c f d D (fun _ : Unit => G)
  exact logPairIsKlt_exists_arbitrarily_small_fixed_effective_divisor_perturbation ρ hρ c f d hd
    D G hklt heff hG cT ξ hinj hcoh hsnc hsupp (hGsupp ()) ε hε

/-- An effective representative of the class (d/q) A of an ample A, with arbitrarily small
coefficient and avoiding finitely many points, keeps the pair klt and its boundary effective. -/
theorem logPairIsKlt_exists_effective_rational_ample_perturbation
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) (heff : LogPairBoundaryEffective c f d D)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ε : ℚ) (hε : 0 < ε) (Z : Set X) (hZ : Z.Finite) :
    ∃ (m r : ℕ) (s : Γ((r • A).sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairBoundaryEffective c f (m * d)
        (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      LogPairIsKlt c f (m * d) (m • D + cartierSectionZeroDivisor (r • A) s hs) ∧
      q • (m • D + cartierSectionZeroDivisor (r • A) s hs) =
        m • (q • D + d • A) +
          principalCartierDivisor X (cartierSectionUnit (r • A) s hs ^ q) ∧
      (∀ x ∈ Z, x ∉ cartierSectionZeroLocus (r • A) s) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, v, ξ, hinj, hcoh, hsnc,
    hsupp⟩ := exists_proper_snc_model c f d D
  exact logPairIsKlt_exists_effective_rational_ample_perturbation_avoiding ρ hρ hnorm c f d hd D
    hklt heff cT ξ hinj hcoh hsnc hsupp A hA q hq N ε hε Z hZ

end Effective

end MixedFujita

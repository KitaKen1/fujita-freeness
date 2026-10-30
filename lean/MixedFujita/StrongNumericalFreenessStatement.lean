/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedFujitaStatement
public import MixedFujita.CartierBigDefinition

/-!
The statement of S-NF (step 1). For a point η of X, the closure of η is an irreducible closed
subset W, and a global section of D vanishes on W exactly when its local coefficient at η lies in
the maximal ideal; this does not depend on the local equation. The dimension of the quotient by
these sections is the dimension of the image of the sections of D in the sections on W. At the
generic point no nonzero section vanishes, so the image is everything. For ample A the
restriction of the sections of j A to W is onto for large j (Serre vanishing), so the asymptotic
d! · dim/j^d of the image is A^d · W; the hypothesis A^{dim W} · W ≥ (n + 1)^{dim W} of S-NF,
with equality allowed and W = X included, is therefore stated as a lower bound for these
restricted dimensions: for every ε > 0 eventually dim ≥ ((n + 1)^d - ε) j^d/d!. This is the form
in which the restricted sections enter the proof (the inequality (13)). S-NF then states that
K_X + A + N is globally generated for a nef divisor N.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

section Restricted

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The global sections of D vanishing on the closure of η: their local coefficient at η lies in
the maximal ideal. -/
noncomputable def cartierSectionsVanishingAt (D : CartierDivisor X) (η : X) :
    Submodule K Γ(D.sheaf, ⊤) :=
  (Submodule.comap (cartierLocalCoefficient D η (Classical.choose (D.exists_isLocalEquationAt η))
    (Classical.choose_spec (D.exists_isLocalEquationAt η)))
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk η)).restrictScalars Γ(X, ⊤))).restrictScalars K

variable {K} in
/-- Vanishing at η does not depend on the local equation. -/
theorem mem_cartierSectionsVanishingAt_iff (D : CartierDivisor X) (η : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt η f) (s : Γ(D.sheaf, ⊤)) :
    s ∈ cartierSectionsVanishingAt K D η ↔
      cartierLocalCoefficient D η f hf s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D η
    (Classical.choose (D.exists_isLocalEquationAt η)) f
    (Classical.choose_spec (D.exists_isLocalEquationAt η)) hf
  change cartierLocalCoefficient D η _ _ s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ↔ _
  rw [hv s]
  constructor
  · intro h
    have h' := Ideal.mul_mem_left (IsLocalRing.maximalIdeal (X.presheaf.stalk η))
      ((v⁻¹ : (X.presheaf.stalk η)ˣ) : X.presheaf.stalk η) h
    rwa [← mul_assoc, Units.inv_mul, one_mul] at h'
  · exact Ideal.mul_mem_left _ _

/-- The dimension of the image of the sections of D in the sections on the closure of η. -/
noncomputable def cartierRestrictedDim (D : CartierDivisor X) (η : X) : ℕ :=
  Module.finrank K (Γ(D.sheaf, ⊤) ⧸ cartierSectionsVanishingAt K D η)

variable {K} in
/-- No nonzero section vanishes at the generic point. -/
theorem cartierSectionsVanishingAt_genericPoint (D : CartierDivisor X) :
    cartierSectionsVanishingAt K D (genericPoint X) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  have h : cartierLocalCoefficient D (genericPoint X)
      (Classical.choose (D.exists_isLocalEquationAt (genericPoint X)))
      (Classical.choose_spec (D.exists_isLocalEquationAt (genericPoint X))) s ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) := hs
  have hbot : IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot (R := X.functionField)
  rw [hbot, Ideal.mem_bot] at h
  have h0 : s = 0 := cartierLocalCoefficient_injective D (genericPoint X) _ _
    (h.trans (map_zero _).symm)
  rw [h0]
  exact Submodule.zero_mem _

variable {K} in
/-- On W = X the restricted dimension is h^0(D). -/
theorem cartierRestrictedDim_genericPoint (D : CartierDivisor X) :
    cartierRestrictedDim K D (genericPoint X) = Module.finrank K Γ(D.sheaf, ⊤) := by
  unfold cartierRestrictedDim
  exact (Submodule.quotEquivOfEqBot _ (cartierSectionsVanishingAt_genericPoint D)).finrank_eq

end Restricted

attribute [local instance] cartierBaseOpenAlgebra

/-- S-NF: on a smooth projective variety of dimension n ≥ 1 over an uncountable algebraically
closed field of characteristic zero, let A be ample and N nef. If for every positive-dimensional
irreducible closed subset W, the closure of a point η, the sections of j A restricted to W have
dimension at least ((n + 1)^d - ε) j^d/d! for large j and every ε > 0, d = dim W (that is,
A^d · W ≥ (n + 1)^d, equality allowed, W = X included), then K_X + A + N is globally generated. -/
def StrongNumericalFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A N : CartierDivisor X), CartierIsAmpleProj K A → CartierIsNef K N →
      (∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
          ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤ cartierRestrictedDim K (j • A) η) →
      CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + A + N)

end MixedFujita

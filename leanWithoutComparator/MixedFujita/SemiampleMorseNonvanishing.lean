/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveGeneratedMorseNonvanishing
public import MixedFujita.MixedMorseHomogeneity
public import MixedFujita.GlobalSectionsOfPushforwardIso
public import MixedFujita.AmpleDivisibleGlobalGeneration

/-! 任意無限体・特異proper整源の元ample−semiampleの弱いMorse非消滅。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Weak algebraic Morse nonvanishing for an original ample divisor minus
any original semiample divisor. Effective generation and the nonzero section
are constructed internally; this works on singular proper integral sources. -/
theorem proper_ample_sub_semiample_exists_nonzero_of_mixed_inequality
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (H G : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (hG : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • G))
    (hnum : (n + 1 : ℤ) * cartierMixedEulerDifference K (G :: List.replicate n H) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) H) 0) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : Γ((k • (H - G)).sheaf, ⊤), s ≠ 0 := by
  obtain ⟨q, hq, hqgen⟩ := hG
  obtain ⟨f, hf⟩ := cartierIsGloballyGenerated_exists_effective_principal_shift hqgen
  let G' := q • G + principalCartierDivisor X f
  have hgen : CartierIsGloballyGenerated G' := cartierIsGloballyGenerated_principal_shift _ f hqgen
  have hscaled := proper_mixed_morse_inequality_nsmul K n hdim H G hnum q hq
  have hnum' : (n + 1 : ℤ) * cartierMixedEulerDifference K (G' :: List.replicate n (q • H)) 0 <
      cartierMixedEulerDifference K (List.replicate (n + 1) (q • H)) 0 := by
    simpa only [G', cartierMixedEulerDifference_direction_principal] using hscaled
  obtain ⟨m, hm, hsections⟩ :=
    proper_ample_sub_effective_generated_eventually_nonzero_of_mixed_inequality
      K n hdim (q • H) G' (cartierIsAmpleProj_nsmul hH hq) hf hgen hnum'
  obtain ⟨s, hs⟩ := hsections m le_rfl
  have he : m • (q • H - G') = (m * q) • (H - G) + principalCartierDivisor X ((f⁻¹) ^ m) := by
    simp only [G', principalCartierDivisor_power, principalCartierDivisor_inv,
      smul_sub, nsmul_add, smul_smul, smul_neg]
    abel
  let a : (m • (q • H - G')).sheaf ≅ ((m * q) • (H - G)).sheaf :=
    eqToIso (congrArg CartierDivisor.sheaf he) ≪≫ cartierSheafPrincipalShiftIso _ _
  let e := moduleIsoGlobalSectionsBaseLinearEquiv K a
  refine ⟨m * q, Nat.mul_pos hm hq, e s, ?_⟩
  intro hz
  exact hs (e.injective (hz.trans e.map_zero.symm))

end MixedFujita

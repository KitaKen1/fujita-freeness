/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierVanishingTransfer
public import MixedFujita.CocycleCartierDivisor

/-!
Vanishing on the generic fibre from a cocycle on the model (step 10, R4-7).

Let `X` be integral, proper, flat and separated over a noetherian domain `A`, with an affine cover
`V_0, …, V_N` and a cocycle `w` of units normalized at `V_0` (check 529). The cocycle defines a
Cartier divisor on `X` and, pulled back, one on the closed fibre over `A_𝔪/𝔪` (check 529). If every
divisor on the closed fibre with the pulled-back local equations has vanishing higher cohomology
(check 554), then so has every divisor on the fibre over a field containing `A` whose local
equations have the pulled-back cocycle as transition functions
(`subsingleton_cohomology_of_modelCocycle`, check 553).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of A))]

/-- **Vanishing on the fibre over a field from the closed fibre, for divisors given by a cocycle on
the model.** -/
theorem subsingleton_cohomology_of_modelCocycle [IsProper (X ↘ Spec (CommRingCat.of A))]
    [Flat (X ↘ Spec (CommRingCat.of A))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {N : ℕ} (V : Fin (N + 1) → X.Opens) [∀ i, Nonempty (V i)] (hV : ∀ i, IsAffineOpen (V i))
    (hcov : ⨆ i, V i = ⊤)
    (hneX : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (N + 1)), Nonempty (TopCat.Presheaf.cechOpen V x))
    (w : ∀ i j, Γ(X, V i ⊓ V j)ˣ) (hw : IsCocycleZero V w)
    (𝔪 : Ideal A) [𝔪.IsMaximal]
    {Yk : Scheme.{u}} [IsIntegral Yk] [Yk.Over (Spec (CommRingCat.of 𝔪.ResidueField))]
    {gk : Yk ⟶ X}
    (Hk : IsPullback gk (Yk ↘ Spec (CommRingCat.of 𝔪.ResidueField)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A 𝔪.ResidueField))))
    [IsAffineHom gk] [IsAffineHom (pullback.diagonal (terminal.from Yk))]
    [∀ i, Nonempty (gk ⁻¹ᵁ V i)]
    (hneYk : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (N + 1)),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gk ⁻¹ᵁ V i) x))
    (hvan : ∀ Qk : CartierDivisor Yk, (∀ i, ∀ z ∈ gk ⁻¹ᵁ V i,
        Qk.IsLocalEquationAt z (cocycleEquation (fun k => gk ⁻¹ᵁ V k) (pullbackCocycle V gk w) i)) →
      ∀ j, 1 ≤ j → Subsingleton (Scheme.Modules.Cohomology Qk.sheaf j))
    (K : Type u) [Field K] [Algebra A K] (hK : Function.Injective (algebraMap A K))
    {YK : Scheme.{u}} [IsIntegral YK] [YK.Over (Spec (CommRingCat.of K))] {gK : YK ⟶ X}
    (HK : IsPullback gK (YK ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of A))
      (Spec.map (CommRingCat.ofHom (algebraMap A K))))
    [IsAffineHom gK] [IsAffineHom (pullback.diagonal (terminal.from YK))]
    (hneYK : ∀ {m : ℕ} (x : Fin (m + 1) → Fin (N + 1)),
      Nonempty (TopCat.Presheaf.cechOpen (fun i => gK ⁻¹ᵁ V i) x))
    (QK : CartierDivisor YK) (gYK : Fin (N + 1) → YK.functionFieldˣ)
    (hgYK : ∀ i, ∀ z ∈ gK ⁻¹ᵁ V i, QK.IsLocalEquationAt z (gYK i))
    (huK : ∀ i j, ∀ (_ : Nonempty (gK ⁻¹ᵁ V i ⊓ gK ⁻¹ᵁ V j : YK.Opens)),
      YK.germToFunctionField (gK ⁻¹ᵁ V i ⊓ gK ⁻¹ᵁ V j)
          (baseChangeTransition V (fun i j => (w i j : Γ(X, V i ⊓ V j))) i j) * gYK j = gYK i)
    {j : ℕ} (hj : 1 ≤ j) : Subsingleton (Scheme.Modules.Cohomology QK.sheaf j) := by
  obtain ⟨DX, hDX⟩ := exists_cartierDivisor_of_cocycle V w hw (by rw [← hcov])
  have hcovk : iSup (fun k => gk ⁻¹ᵁ V k) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  obtain ⟨Dk, hDk⟩ := exists_cartierDivisor_of_cocycle (fun k => gk ⁻¹ᵁ V k)
    (pullbackCocycle V gk w) (pullbackCocycle_spec V gk w hw) hcovk
  exact subsingleton_cohomology_of_residueField_of_injective V hV hcov hneX DX
    (cocycleEquation V w) hDX (fun i j => (w i j : Γ(X, V i ⊓ V j))) (cocycle_huX V w hw) 𝔪 Hk
    hneYk Dk _ hDk (cocycle_huY V gk w hw) (hvan Dk hDk) K hK HK hneYK QK gYK hgYK huK hj

end MixedFujita

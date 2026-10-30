/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.AmpleTwistVeryAmple
public import MixedFujita.EtaleChartDimension

/-!
The section embedding criterion can be checked using any actual finite presentation of the
coordinate ring of a nonvanishing open. It suffices that each algebra generator occurs as a
rational ratio of two members of the given global section family. The open need not come from
a closed immersion into an already chosen projective space.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] cartierBaseOpenAlgebra

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

omit [IsIntegral X] in
/-- Constants in the actual open-section algebra are restricted scheme-base constants. -/
theorem cartierBaseOpenAlgebra_algebraMap (U : X.Opens) (c : K) :
    algebraMap K Γ(X, U) c =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (schemeBaseScalars K X c) := by
  change ((X.baseRingToStructurePresheaf K).app (op U)) c = _
  rw [Scheme.baseRingToStructurePresheaf_app, schemeBaseScalars_apply]
  rfl

/-- A surjective finite polynomial presentation whose generators occur among section ratios
implies the actual ratio map is surjective. Equality of the opens is enough; no transport of
the presentation or assumed identification of its functions is needed. -/
theorem eval₂Hom_cartierSectionRatio_surjective_of_generators
    (D : CartierDivisor X) {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤))
    (q₀ : Fin M) (h₀ : t q₀ ≠ 0) (U : X.Opens) [Nonempty U]
    (hU : cartierSectionNonvanishingOpen D (t q₀) = U)
    {m : ℕ} (f : MvPolynomial (Fin m) K →ₐ[K] Γ(X, U)) (hf : Function.Surjective f)
    (hgen : ∀ l : Fin m, ∃ q : Fin M,
      (cartierSectionRational D (t q₀))⁻¹ * cartierSectionRational D (t q) =
        X.germToFunctionField U (f (MvPolynomial.X l))) :
    Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top :
        cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (fun q => cartierSectionRatio D (t q₀) h₀ (t q))) := by
  classical
  have := (cartierSectionNonvanishingOpen_nonempty_iff D (t q₀)).mpr h₀
  let V := cartierSectionNonvanishingOpen D (t q₀)
  let Φ := MvPolynomial.eval₂Hom
    ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
    (fun q => cartierSectionRatio D (t q₀) h₀ (t q))
  choose q hq using hgen
  have hpoly (p : MvPolynomial (Fin m) K) :
      X.germToFunctionField V (Φ (MvPolynomial.rename q p)) =
        X.germToFunctionField U (f p) := by
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.rename_C, show f (MvPolynomial.C c) = algebraMap K Γ(X, U) c from
        f.commutes c, cartierBaseOpenAlgebra_algebraMap U c]
      dsimp only [Φ]
      rw [MvPolynomial.eval₂Hom_C]
      change X.germToFunctionField V
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (schemeBaseScalars K X c)) = _
      rw [germToFunctionField_restrict X, germToFunctionField_restrict X]
    | add p r hp hr => simp only [map_add, hp, hr]
    | mul_X p l hp =>
      simp only [map_mul, MvPolynomial.rename_X, hp]
      congr 1
      dsimp only [Φ]
      rw [MvPolynomial.eval₂Hom_X']
      exact (cartierSectionRatio_germToFunctionField D (t q₀) h₀ (t (q l))).trans (hq l)
  intro a
  obtain ⟨p, hp⟩ := hf (X.presheaf.map (homOfLE hU.symm.le).op a)
  refine ⟨MvPolynomial.rename q p, ?_⟩
  apply X.germToFunctionField_injective V
  rw [hpoly, hp, germToFunctionField_restrict X]

end MixedFujita

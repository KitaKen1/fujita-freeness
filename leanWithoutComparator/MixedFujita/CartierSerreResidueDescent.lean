/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierSerreVanishing

/-! A single actual Cartier sheaf isomorphism constructs all natural-multiple and additive-twist sheaf isomorphisms. Eventual vanishing along a positive multiple descends to all twists by taking a maximum of the finitely many residue-class thresholds. No cohomology input is introduced into the final ample theorem. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def cartierNaturalMultiplesSheafIsoOfIso
    (H J : CartierDivisor X) (a : H.sheaf ≅ J.sheaf) (j : ℕ) :
    (j • H).sheaf ≅ (j • J).sheaf :=
  (cartierSGANatPowerIso H j).symm ≪≫
    sgaLineBundleNatPowerCartierIso (cartierSGALineBundle H) J
      ((cartierSGAModuleIso H).symm ≪≫ a) j

noncomputable def cartierAddNaturalMultiplesSheafIsoOfIso
    (D H J : CartierDivisor X) (a : H.sheaf ≅ J.sheaf) (j : ℕ) :
    (D + j • H).sheaf ≅ (D + j • J).sheaf :=
  (cartierTensorSheafIso D (j • H)).symm ≪≫
    tensorIso (Iso.refl D.sheaf) (cartierNaturalMultiplesSheafIsoOfIso H J a j) ≪≫
    cartierTensorSheafIso D (j • J)

theorem cartier_serreVanishing_of_positive_multiple
    (H : CartierDivisor X) (m : ℕ) (hm : 0 < m)
    (h : ∀ D : CartierDivisor X, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (D + j • (m • H)).sheaf (q + 1)))
    (D : CartierDivisor X) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (D + n • H).sheaf (q + 1)) := by
  classical
  choose B hB using fun i : Fin m => h (D + i.val • H)
  let b := Finset.univ.sup B
  refine ⟨b * m, fun n hn q => ?_⟩
  let i : Fin m := ⟨n % m, Nat.mod_lt n hm⟩
  have hBb : B i ≤ b := Finset.le_sup (Finset.mem_univ i)
  have hbq : b ≤ n / m := (Nat.le_div_iff_mul_le hm).mpr hn
  have hv := hB i (n / m) (hBb.trans hbq) q
  have he : D + n • H = (D + i.val • H) + (n / m) • (m • H) := by
    change D + n • H = (D + (n % m) • H) + (n / m) • (m • H)
    rw [smul_smul, add_assoc, ← add_nsmul, Nat.mul_comm (n / m) m, Nat.mod_add_div]
  rw [he]
  exact hv

end MixedFujita

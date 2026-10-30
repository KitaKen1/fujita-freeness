/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinSaturatedSectionDescent
public import MixedFujita.ProjectiveChartSectionExtension
public import MixedFujita.CartierSectionPullbackAvoidance

/-!
Powers of actual sections saturate their generating opens over one fixed Stein target. If
mD ~ g*H with m positive, descend the m-th power of each section of D after the actual principal
shift. The power has the same nonvanishing open, so that open is the inverse image of the
nonvanishing open of the descended section. Ordinary global generation then supplies actual
Cartier descent by gluing ratios. From eventual freeness, use a large divisible degree Lm and
the next degree Lm+1 on that same target and subtract to descend D itself.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Multiplying a rational section by the principal-shift unit preserves its actual generating
open, with both regular sections specified explicitly. -/
theorem cartierSectionNonvanishingOpen_principal_shift_of_rational
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (φ : X.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor X φ).sheaf, ⊤)) (t : Γ(D.sheaf, ⊤))
    (hr : cartierSectionRational D t = (φ : X.functionField) * cartierSectionRational _ s) :
    cartierSectionNonvanishingOpen D t =
      cartierSectionNonvanishingOpen (D + principalCartierDivisor X φ) s := by
  ext x
  change x ∈ cartierSectionNonvanishingOpen D t ↔
    x ∈ cartierSectionNonvanishingOpen (D + principalCartierDivisor X φ) s
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  have hφ := hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x φ)
  have hcoeff : cartierLocalCoefficient D x f hf t =
      cartierLocalCoefficient (D + principalCartierDivisor X φ) x (f * φ) hφ s := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image, hr, Units.val_mul]
    ring
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x f hf,
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x (f * φ) hφ, hcoeff]

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [IsDominant g]
  (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)

include happ

/-- A descended positive multiple makes every actual section's generating open saturated. -/
theorem stein_section_nonvanishing_saturated_of_multiple_descent
    (D : CartierDivisor X) {m : ℕ} (hm : 0 < m) (H : CartierDivisor Y) (φ : X.functionFieldˣ)
    (hD : m • D = cartierPullback g H + principalCartierDivisor X φ)
    (s : Γ(D.sheaf, ⊤)) :
    ∃ U : Y.Opens, cartierSectionNonvanishingOpen D s = g ⁻¹ᵁ U := by
  let sp := cartierSectionPower D s m
  let sc := cartierSectionCast hD sp
  let t : Γ((cartierPullback g H).sheaf, ⊤) :=
    CartierDivisor.sectionMk _ (cartierPrincipalShift_mem (cartierPullback g H) φ sc)
  have ht : cartierSectionRational (cartierPullback g H) t =
      (φ : X.functionField) * cartierSectionRational _ sc :=
    cartierSectionRational_sectionMk _ _ _
  obtain ⟨a, ha⟩ := cartierDominantPullbackSection_surjective_of_open_app_surjective g
    (fun U => (happ U).2) H t
  refine ⟨cartierSectionNonvanishingOpen H a, ?_⟩
  calc
    cartierSectionNonvanishingOpen D s = cartierSectionNonvanishingOpen (m • D) sp :=
      (cartierSectionPower_nonvanishingOpen D s hm).symm
    _ = cartierSectionNonvanishingOpen (cartierPullback g H + principalCartierDivisor X φ) sc :=
      (cartierSectionNonvanishingOpen_cast hD sp).symm
    _ = cartierSectionNonvanishingOpen (cartierPullback g H) t :=
      (cartierSectionNonvanishingOpen_principal_shift_of_rational _ φ sc t ht).symm
    _ = g ⁻¹ᵁ cartierSectionNonvanishingOpen H a := by
      rw [← ha]
      ext x
      exact cartierDominantPullbackSection_nonvanishing_iff g H a x

/-- A free divisor descends to the same Stein target as any one of its positive multiples. -/
theorem stein_exists_cartier_descent_of_generated_multiple_descent
    (hsurj : Function.Surjective g) (D : CartierDivisor X) (hD : CartierIsGloballyGenerated D)
    {m : ℕ} (hm : 0 < m) (H : CartierDivisor Y) (φ : X.functionFieldˣ)
    (hmD : m • D = cartierPullback g H + principalCartierDivisor X φ) :
    ∃ (A : CartierDivisor Y) (ψ : X.functionFieldˣ),
      D = cartierPullback g A + principalCartierDivisor X ψ :=
  stein_exists_cartier_descent_of_saturated_generation g happ hsurj D hD
    (stein_section_nonvanishing_saturated_of_multiple_descent g happ D hm H φ hmD)

/-- Large consecutive free degrees on the same target descend D itself. The original chosen
free degree m need not exceed the eventual-freeness threshold. -/
theorem stein_exists_cartier_descent_of_eventual_generation
    (hsurj : Function.Surjective g) (D : CartierDivisor X)
    (hfree : ∃ M : ℕ, ∀ k : ℕ, M ≤ k → CartierIsGloballyGenerated (k • D))
    {m : ℕ} (hm : 0 < m) (H : CartierDivisor Y) (φ : X.functionFieldˣ)
    (hmD : m • D = cartierPullback g H + principalCartierDivisor X φ) :
    ∃ (A : CartierDivisor Y) (ψ : X.functionFieldˣ),
      D = cartierPullback g A + principalCartierDivisor X ψ := by
  obtain ⟨M, hM⟩ := hfree
  let L := M + 1
  let k := L * m + 1
  have hlarge : M ≤ k := by
    have h := Nat.le_mul_of_pos_right L hm
    dsimp [k, L] at *
    omega
  have hmk : m • (k • D) = cartierPullback g (k • H) + principalCartierDivisor X (φ ^ k) := by
    rw [show m • (k • D) = k • (m • D) from smul_comm m k D, hmD, nsmul_add,
      ← cartierPullback_nsmul, ← principalCartierDivisor_power]
  obtain ⟨A, ψ, hA⟩ := stein_exists_cartier_descent_of_generated_multiple_descent g happ hsurj
    (k • D) (hM k hlarge) hm (k • H) (φ ^ k) hmk
  have hLm : (L * m) • D = cartierPullback g (L • H) + principalCartierDivisor X (φ ^ L) := by
    rw [mul_nsmul', hmD, nsmul_add, ← cartierPullback_nsmul, ← principalCartierDivisor_power]
  have hdiff : D = k • D - (L * m) • D := by
    dsimp [k]
    rw [add_nsmul, one_nsmul]
    abel
  refine ⟨A - L • H, ψ * (φ ^ L)⁻¹, ?_⟩
  rw [hdiff, hA, hLm, cartierPullback_sub, principalCartierDivisor_mul, principalCartierDivisor_inv]
  abel

end MixedFujita

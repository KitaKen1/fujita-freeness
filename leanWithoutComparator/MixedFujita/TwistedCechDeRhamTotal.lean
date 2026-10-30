/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedDeRhamCech
public import Mathlib.Algebra.Homology.TotalComplex

/-!
The Čech–de Rham double complex and its total complex (step 10).

Mathlib's total complexes need signs for the vertical differential (`ComplexShape.TensorSigns`),
provided for `down ℕ` and `up ℤ`; we give them for `up ℕ` with `ε i = (-1)^i`
(`upNatTensorSigns`), so that `TotalComplexShape (up ℕ) (up ℕ) (up ℕ)` is available.

In characteristic `p`, for a finite family of open subsets `𝒰` the SGA Čech complexes of the
sheaves `Ω^b_X(p • D)`, with the de Rham differentials between them (check-420), form a double
complex (`twistedCechDeRhamBicomplex`, its `b`-th row is the Čech complex of `Ω^b_X(p • D)`), whose
total complex (`twistedCechDeRhamTotal`) computes, for an affine cover, the hypercohomology of the
twisted de Rham complex `Ω^•_X(p • D)` (`twistedHypercohomology`). This is the complex on which the
Deligne–Illusie inequality of check-422 is to be proved: its row filtration bounds the
hypercohomology by the Čech cohomology of the `Ω^b_X(p • D)`, and the Deligne–Illusie map identifies
it with that of the `Ω^b_X(D)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The signs `ε i = (-1)^i` for total complexes of `ℕ`-indexed cochain complexes. -/
instance upNatTensorSigns : (ComplexShape.up ℕ).TensorSigns where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one]

theorem upNat_ε (i : ℕ) : (ComplexShape.up ℕ).ε i = (-1 : ℤˣ) ^ i := rfl

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

/-- **The Čech–de Rham double complex** of `Ω^•_X(p • D)` for a finite family of open subsets: the
`b`-th row is the Čech complex of `Ω^b_X(p • D)`, the vertical maps are the de Rham
differentials. -/
noncomputable def twistedCechDeRhamBicomplex (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of
    (fun b => TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K (p • D) b).presheaf)
    (fun b => twistedFormsCechDiff p c₀ hcover D b 𝒰)
    (fun b => twistedFormsCechDiff_comp p c₀ hcover D b 𝒰)

theorem twistedCechDeRhamBicomplex_X (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (b : ℕ) :
    (twistedCechDeRhamBicomplex p c₀ hcover D 𝒰).X b =
      TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K (p • D) b).presheaf :=
  rfl

theorem twistedCechDeRhamBicomplex_d (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (b : ℕ) :
    (twistedCechDeRhamBicomplex p c₀ hcover D 𝒰).d b (b + 1) =
      twistedFormsCechDiff p c₀ hcover D b 𝒰 := by
  unfold twistedCechDeRhamBicomplex
  exact CochainComplex.of_d
    (fun b => TopCat.Presheaf.cechComplex 𝒰 (twistedFormsSheaf K (p • D) b).presheaf)
    (fun b => twistedFormsCechDiff p c₀ hcover D b 𝒰) b

/-- **The total complex of the Čech–de Rham double complex.** -/
noncomputable def twistedCechDeRhamTotal (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) : CochainComplex AddCommGrpCat.{u} ℕ :=
  (twistedCechDeRhamBicomplex p c₀ hcover D 𝒰).total (ComplexShape.up ℕ)

/-- **The hypercohomology of `Ω^•_X(p • D)`** computed with the family `𝒰`, in total degree `m`. -/
noncomputable def twistedHypercohomology (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (m : ℕ) : AddCommGrpCat.{u} :=
  (twistedCechDeRhamTotal p c₀ hcover D 𝒰).homology m

end MixedFujita

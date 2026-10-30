/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IteratedCone
public import MixedFujita.LinearCechDeRham
public import MixedFujita.TwistedFormsCechComparison
public import MixedFujita.DeligneIllusieVanishingReduction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
The Hodge-to-de Rham bound for the Čech–de Rham complex (step 10).

Over a finite field, finite-dimensional vector spaces are compared by counting elements
(`Nat.card V = |K| ^ dim V`), so an additive bijection preserves the dimension
(`finite_finrank_eq_of_addEquiv`); this replaces `K`-linearity checks of comparison maps. The
`K`-linear Čech complex of check 428 has SGA's Čech complex as underlying complex of groups
(`cechComplexLinearForgetIso`), so their homologies agree additively
(`cechComplexLinearHomologyAddEquiv`), and by SGA's comparison theorem (check 427) the `K`-linear
Čech cohomology of `Ω^b(E)` on a finite affine cover has the dimension of the sheaf cohomology
(`finrank_cechComplexLinear_twistedForms_homology`).

The iterated cone of check 434 over the rows `Č(Ω^b(p • D))`, `b ≤ n`, with the de Rham
differential as vertical maps is the Čech–de Rham total complex (`cechDeRhamCone`), and
`dim H^m(cechDeRhamCone) ≤ Σ_{b ≤ n} h^{m-b}(Ω^b(p • D))` (`finrank_cechDeRhamCone_homology_le`),
the right-hand side of the Deligne–Illusie inequality (`twistedHodgeCount K (p • D) n m`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

section FiniteField

variable {K : Type u} [Field K] [Finite K]

/-- **Over a finite field an additive bijection preserves the dimension.** -/
theorem finite_finrank_eq_of_addEquiv {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K N] (e : M ≃+ N) :
    Module.Finite K M ∧ Module.finrank K M = Module.finrank K N := by
  have : Finite N := Module.finite_of_finite K
  have : Finite M := Finite.of_equiv N e.toEquiv.symm
  have hM : Module.Finite K M := Module.Finite.of_finite
  refine ⟨hM, ?_⟩
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := M)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := N)
  have h3 : Nat.card M = Nat.card N := Nat.card_congr e.toEquiv
  have hK : 1 < Nat.card K := Finite.one_lt_card
  exact pow_right_injective₀ (by omega) (by omega) (h1.symm.trans (h3.trans h2))

end FiniteField

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra sectionsBaseModule

variable (K) in
/-- The `K`-linear Čech complex has SGA's Čech complex as underlying complex of groups. -/
noncomputable def cechComplexLinearForgetIso (M : X.Modules) {N : ℕ} (𝒰 : Fin N → X.Opens) :
    ((forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (cechComplexLinear K M 𝒰) ≅ TopCat.Presheaf.cechComplex 𝒰 M.presheaf :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    refine AddCommGrpCat.ext fun c => ?_
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    refine (TopCat.Presheaf.cechComplex_d_apply (U := 𝒰) (P := M.presheaf) (n := i)
      (c := c)).trans ?_
    change _ = ((cechComplexLinear K M 𝒰).d i (i + 1)).hom c
    rw [cechComplexLinear_d]
    rfl)

variable (K) in
/-- The homology of the `K`-linear Čech complex is additively SGA's Čech cohomology. -/
noncomputable def cechComplexLinearHomologyAddEquiv (M : X.Modules) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (q : ℕ) :
    (cechComplexLinear K M 𝒰).homology q ≃+ (TopCat.Presheaf.cechComplex 𝒰 M.presheaf).homology q :=
  ((((cechComplexLinear K M 𝒰).sc q).mapHomologyIso
      (forget₂ (ModuleCat.{u} K) AddCommGrpCat.{u})).symm ≪≫
    HomologicalComplex.homologyMapIso (cechComplexLinearForgetIso K M 𝒰) q).addCommGroupIsoToAddEquiv

variable [IsIntegral X] {n : ℕ}

/-- **The `K`-linear Čech cohomology of `Ω^b(E)` has the dimension of the sheaf cohomology** over a
finite field, for a finite affine open cover of a proper scheme with affine diagonal. -/
theorem finrank_cechComplexLinear_twistedForms_homology [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) (q : ℕ) :
    FiniteDimensional K ((cechComplexLinear K (twistedFormsSheaf K E b) 𝒰).homology q) ∧
      Module.finrank K ((cechComplexLinear K (twistedFormsSheaf K E b) 𝒰).homology q) =
        Module.finrank K
          (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K E b) q) := by
  obtain ⟨e⟩ := twistedFormsSheaf_nonempty_cechHomologyAddEquiv hcover E b 𝒰 h𝒰 hcov q
  have := twistedFormsSheaf_cohomology_finite hcover E b q
  exact finite_finrank_eq_of_addEquiv ((cechComplexLinearHomologyAddEquiv K _ 𝒰 q).trans e)

variable (K) in
/-- **The Čech–de Rham total complex** of `Ω^•(p • D)` in de Rham degrees `≤ n`, as the iterated cone
of the rows `Č(Ω^b(p • D))` along the de Rham differential. -/
noncomputable def cechDeRhamCone (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) : CochainComplex (ModuleCat.{u} K) ℕ :=
  iteratedCone (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
    (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
    (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n 0

/-- **Hodge-to-de Rham bound:** `dim H^m(Čech–de Rham) ≤ Σ_{b ≤ n} h^{m-b}(Ω^b(p • D))`, the
right-hand side of the Deligne–Illusie inequality, over a finite field. -/
theorem finrank_cechDeRhamCone_homology_le [Finite K] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (D : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i))
    (hcov : ⨆ i, 𝒰 i = ⊤) (m : ℕ) :
    FiniteDimensional K ((cechDeRhamCone K p c₀ hcover D 𝒰).homology m) ∧
      Module.finrank K ((cechDeRhamCone K p c₀ hcover D 𝒰).homology m) ≤
        twistedHodgeCount K (p • D) n m := by
  obtain ⟨h1, h2⟩ := finrank_iteratedCone_homology_le
    (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
    (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
    (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰)
    (fun b q => (finrank_cechComplexLinear_twistedForms_homology hcover (p • D) b 𝒰 h𝒰 hcov q).1)
    n 0 m
  refine ⟨h1, h2.trans ?_⟩
  rw [coneFiltrationBound, twistedHodgeCount, Nat.sub_zero, zero_add]
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases hb : b ≤ m
  · simp only [hb, ↓reduceIte]
    rw [zero_add]
    exact (finrank_cechComplexLinear_twistedForms_homology hcover (p • D) b 𝒰 h𝒰 hcov
      (m - b)).2.le
  · simp only [hb, ↓reduceIte]
    exact Nat.zero_le _

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SheafCechOneLocalVanishing
public import MixedFujita.SGACohomologyComparison
public import SGA.Foundations.Cohomology.Pushforward

/-!
First cohomology on an open part from vanishing of twists on the whole space (step 9, relative
vanishing from global vanishing).

Let `ψ_m : F_m → P` be morphisms of presheaves of abelian groups on a space, and `U` a finite
family of opens. Suppose `H¹(⋃ U, F_m) = 0` for all large `m`, each `ψ_m` is injective on the
triple intersections, and every section of `P` on a double intersection comes from `F_m` for all
large `m`. Then the Čech complex of `P` for `U` is exact in degree one
(`cech_exactAt_one_of_twisted_approximation`): a cocycle of `P` lifts to a cochain of one `F_m`
(finitely many components), the lift is a cocycle by injectivity, a coboundary by the vanishing,
and its image is a coboundary of `P`.

For a morphism of schemes `ι : Y → X` and `P` the direct image of a module `M` on `Y`, the Čech
complex for `U` is that of `M` for `ι⁻¹ U`; with `H¹` vanishing on the members `ι⁻¹ Uᵢ` this gives
`H¹(Y, M) = 0` (`scheme_H1_subsingleton_of_twisted_approximation`). This is the cohomological core
of the passage from Kawamata–Viehweg vanishing on a compactification `T̄` to the vanishing on the
open model `T = T̄ ∖ D`: there `F_m = 𝒪_T̄(C + m D)` and `P` is the direct image of `𝒪_T(C)`, and a
rational function regular off `D` on an affine chart where `D = div s` acquires at most a bounded
pole along `D`, so it is a section of `𝒪(C + m D)` for large `m`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TopCat.Presheaf TopCat.Sheaf
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Čech exactness in degree one of a presheaf that is approximated by presheaves with vanishing
first cohomology: injective on triple intersections, eventually surjective on double
intersections. -/
theorem cech_exactAt_one_of_twisted_approximation {X : TopCat.{u}}
    [HasExt.{u} (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (F : ℕ → CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) (ψ : ∀ m, (F m).obj ⟶ P)
    {n : ℕ} (U : Fin n → Opens X) (m₀ : ℕ)
    (hvan : ∀ m, m₀ ≤ m → Subsingleton ((F m).H' 1 (⨆ i, U i)))
    (hinj : ∀ (m : ℕ) (x : Fin 3 → Fin n),
      Function.Injective ((ψ m).app (op (cechOpen U x))).hom)
    (hsurj : ∀ (x : Fin 2 → Fin n) (s : P.obj (op (cechOpen U x))),
      ∃ m₁, ∀ m, m₁ ≤ m → s ∈ Set.range ((ψ m).app (op (cechOpen U x))).hom) :
    (cechComplex U P).ExactAt 1 := by
  classical
  rw [cechComplex_exactAt_succ_iff U P 0]
  intro c hc
  choose m₁ hm₁ using fun x : Fin 2 → Fin n => hsurj x (c x)
  let m := max m₀ (Finset.univ.sup m₁)
  have hm : ∀ x, m₁ x ≤ m := fun x =>
    le_max_of_le_right (Finset.le_sup (f := m₁) (Finset.mem_univ x))
  choose c' hc' using fun x : Fin 2 → Fin n => hm₁ x m (hm x)
  have hcc : cechCochainMap U (ψ m) 1 c' = c := funext fun x => hc' x
  have hdc' : cechD U (F m).obj 1 c' = 0 := by
    funext y
    apply hinj m y
    have h := congrFun (cechD_cechCochainMap U (ψ m) c') y
    rw [hcc, hc, cechCochainMap_apply] at h
    simp only [Pi.zero_apply] at h ⊢
    rw [map_zero]
    exact h.symm
  have hexact := sheaf_cech_exactAt_one_of_H1_subsingleton (F m) U (hvan m (le_max_left _ _))
  rw [cechComplex_exactAt_succ_iff U (F m).obj 0] at hexact
  obtain ⟨b', hb'⟩ := hexact c' hdc'
  exact ⟨cechCochainMap U (ψ m) 0 b', by rw [cechD_cechCochainMap, hb', hcc]⟩

/-- First cohomology of a module on `Y` vanishes if, for a finite cover `U` of `X` by opens with
`H¹` vanishing on the preimages, the direct image along `ι : Y → X` is approximated in the sense
of `cech_exactAt_one_of_twisted_approximation` by modules on `X` with vanishing `H¹`. -/
theorem scheme_H1_subsingleton_of_twisted_approximation {X Y : Scheme.{u}} (ι : Y ⟶ X)
    (M : Y.Modules) (F : ℕ → X.Modules)
    (ψ : ∀ m, (F m).presheaf ⟶ ((Scheme.Modules.pushforward ι).obj M).presheaf)
    {n : ℕ} (U : Fin n → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (hlocal : ∀ i, Subsingleton (Modules.cohomologyOn M 1 (ι ⁻¹ᵁ U i))) (m₀ : ℕ)
    (hvan : ∀ m, m₀ ≤ m → Subsingleton (Scheme.Modules.Cohomology (F m) 1))
    (hinj : ∀ (m : ℕ) (x : Fin 3 → Fin n),
      Function.Injective ((ψ m).app (op (cechOpen U x))).hom)
    (hsurj : ∀ (x : Fin 2 → Fin n)
      (s : ((Scheme.Modules.pushforward ι).obj M).presheaf.obj (op (cechOpen U x))),
      ∃ m₁, ∀ m, m₁ ≤ m → s ∈ Set.range ((ψ m).app (op (cechOpen U x))).hom) :
    Subsingleton (Scheme.Modules.Cohomology M 1) := by
  have hvan' : ∀ m, m₀ ≤ m → Subsingleton ((F m).toAbSheaf.H' 1 (⨆ i, U i)) := by
    intro m hm
    rw [hcover]
    let : Subsingleton (Scheme.Modules.Cohomology (F m) 1) := hvan m hm
    exact (sgaCohomologyLinearEquiv (F m) 1).toEquiv.subsingleton
  have hexact : (cechComplex U ((Scheme.Modules.pushforward ι).obj M).presheaf).ExactAt 1 :=
    cech_exactAt_one_of_twisted_approximation (fun m => (F m).toAbSheaf) _ ψ U m₀ hvan' hinj
      hsurj
  let : Subsingleton ((cechComplex U ((Scheme.Modules.pushforward ι).obj M).presheaf).homology 1) :=
    AddCommGrpCat.subsingleton_of_isZero hexact.isZero_homology
  let : Subsingleton ((cechComplex (fun i => ι ⁻¹ᵁ U i) M.presheaf).homology 1) :=
    (CohomologyAux.cechHomologyPushforwardAddEquiv ι M U 1).symm.subsingleton
  have hcech : (cechComplex (fun i => ι ⁻¹ᵁ U i) M.presheaf).ExactAt 1 :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
      (AddCommGrpCat.isZero_of_subsingleton _)
  have hM := sheaf_H1_subsingleton_of_cech_one_and_member_H1 M.toAbSheaf
    (fun i => ι ⁻¹ᵁ U i) hlocal hcech
  have hsource : (⨆ i, ι ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcover, Scheme.Hom.preimage_top]
  rw [hsource] at hM
  let : Subsingleton (M.H 1) := hM
  exact (sgaCohomologyLinearEquiv M 1).symm.subsingleton

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAdjunctionNaturality
public import MixedFujita.CartierResidueEquationCompatibility
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Etale.Kaehler

/-! 局所化した実主商と単元変更の留数整合性。 check-278：可換な実商環図式で制限された周囲微分加群の実写像を構成し、純テンソル式・余法生成元・商微分との可換性を証明。OpenAI由来の外積の係数変更APIと楔積の生成性を再利用し、正規化した局所標準随伴および逆向き留数写像の自然性を証明。実際の局所化では、元の正則主商から局所化後の正則性・全射性・核・微分基底・滑らかさを内部供給し、局所化と方程式の単元変更を同時に許す正規化留数の整合性まで構成。大域の層同型・標準Cartier因子との比較・元lc中心の数値随伴は引き続き残る。 -/

@[expose] public section
set_option autoImplicit false
-- The related lemmas deliberately share one compatible ring-square context.
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
open OAI.ReverseLogKodaira.DifferentialBaseChange
namespace MixedFujita

variable {K A B S C : Type*} [CommRing K] [CommRing A] [CommRing B]
  [CommRing S] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K S] [Algebra K C]
  [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
  [IsScalarTower K A B] [IsScalarTower K A S] [IsScalarTower K A C]
  [IsScalarTower K B C] [IsScalarTower K S C]
  [IsScalarTower A B C] [IsScalarTower A S C]


/-- A genuine localization of a regular principal quotient automatically
retains its regular equation, quotient surjectivity and exact kernel ideal. -/
theorem regular_principal_quotient_localization_data
    (M : Submonoid A) [IsLocalization M S]
    [IsLocalization (M.map (algebraMap A B)) C]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g}) :
    (∀ s : S, s * algebraMap A S g = 0 → s = 0) ∧
      Function.Surjective (algebraMap S C) ∧
      RingHom.ker (algebraMap S C) = Ideal.span {algebraMap A S g} := by
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) C := by
    simpa only [Algebra.algebraMapSubmonoid] using
      (inferInstance : IsLocalization (M.map (algebraMap A B)) C)
  have hmap : algebraMap S C = IsLocalization.map C (algebraMap A B) M.le_comap_map :=
    IsLocalization.algebraMap_eq_map_map_submonoid (R := A) (S := B)
      (Rₘ := S) (Sₘ := C) (M := M)
  refine ⟨?_, ?_, ?_⟩
  · exact mem_nonZeroDivisors_iff_right.mp
      (IsLocalization.nonZeroDivisors_le_comap (S := S) M
        (mem_nonZeroDivisors_iff_right.mpr hg))
  · rw [hmap]
    exact IsLocalization.map_surjective_of_surjective
      (M := M) (S := S) (Q := C) (g := algebraMap A B) hsurj
  · rw [hmap, IsLocalization.ker_map (M := M) (S := S) C (algebraMap A B) rfl,
      hker, Ideal.map_span]
    simp only [Set.image_singleton]


/-- Actual localized smooth Cartier quotient charts inherit BOTH normalized
residue isomorphisms and their naturality square from the ORIGINAL quotient.
No localized kernel, regularity, differential basis, smoothness, residue map,
or compatibility certificate has to be supplied. -/
theorem localized_smooth_principal_quotient_exists_natural_residues
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (M : Submonoid A) [IsLocalization M S]
    [IsLocalization (M.map (algebraMap A B)) C]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) :
    ∃ (e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]))
      (e' : (⋀[C]^r Ω[C⁄K]) ≃ₗ[C] ⋀[C]^(1 + r) (C ⊗[S] Ω[S⁄K])),
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z)) ∧
      (∀ z : Fin r → C ⊗[S] Ω[S⁄K],
        e' (exteriorPower.ιMulti C r (mapBaseChange K S C ∘ z)) =
          exteriorPower.ιMulti C (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : C) ⊗ₜ[S] D K S (algebraMap A S g)) z)) ∧
      (e'.symm.toLinearMap.restrictScalars B).comp
          (exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (A := A) (S := S)) (1 + r)) =
        (exteriorDifferentialMap K K B C r).comp e.symm.toLinearMap := by
  let : Algebra.FormallySmooth A S := Algebra.FormallySmooth.of_isLocalization M
  let : Algebra.FormallySmooth K S := Algebra.FormallySmooth.comp K A S
  let : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.of_isLocalization (M.map (algebraMap A B))
  let : Algebra.FormallySmooth K C := Algebra.FormallySmooth.comp K B C
  let c' : Module.Basis (Fin r) C Ω[C⁄K] := (isBaseChange_of_formallyEtale K B C).basis c
  obtain ⟨hg', hsurj', hker'⟩ := regular_principal_quotient_localization_data (S := S) (C := C) M g hg hsurj hker
  exact smooth_principal_quotient_exists_natural_residues g hg hsurj hker
    hg' hsurj' hker' r c c'


/-- Actual local Cartier residue transition, allowing BOTH restriction to a
localization and replacement of the restricted equation by a unit multiple.
All residue maps and localized quotient data are constructed internally. -/
theorem localized_smooth_cartier_residue_equation_transition
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (M : Submonoid A) [IsLocalization M S]
    [IsLocalization (M.map (algebraMap A B)) C]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) (u : Sˣ) :
    ∃ (e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]))
      (e' : (⋀[C]^r Ω[C⁄K]) ≃ₗ[C] ⋀[C]^(1 + r) (C ⊗[S] Ω[S⁄K])),
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z)) ∧
      (∀ z : Fin r → C ⊗[S] Ω[S⁄K],
        e' (exteriorPower.ιMulti C r (mapBaseChange K S C ∘ z)) =
          exteriorPower.ιMulti C (1 + r)
            (Fin.append (fun _ : Fin 1 =>
              (1 : C) ⊗ₜ[S] D K S (↑u * algebraMap A S g)) z)) ∧
      ∀ w, e'.symm (algebraMap S C ↑u •
          exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (A := A) (S := S))
            (1 + r) w) = (exteriorDifferentialMap K K B C r) (e.symm w) := by
  let : Algebra.FormallySmooth A S := Algebra.FormallySmooth.of_isLocalization M
  let : Algebra.FormallySmooth K S := Algebra.FormallySmooth.comp K A S
  let : Algebra.FormallyEtale B C :=
    Algebra.FormallyEtale.of_isLocalization (M.map (algebraMap A B))
  let : Algebra.FormallySmooth K C := Algebra.FormallySmooth.comp K B C
  let c' : Module.Basis (Fin r) C Ω[C⁄K] := (isBaseChange_of_formallyEtale K B C).basis c
  obtain ⟨hg', hsurj', hker'⟩ := regular_principal_quotient_localization_data
    (S := S) (C := C) M g hg hsurj hker
  obtain ⟨e, e₀, he, he₀, hnat⟩ := localized_smooth_principal_quotient_exists_natural_residues
    (S := S) (C := C) M g hg hsurj hker r c
  obtain ⟨e₀', e', he₀', he', hunit⟩ := smooth_principal_quotient_exists_unit_compatible_residues
    (algebraMap A S g) hg' hsurj' hker' r c' u
  have hident : e₀' = e₀ := by
    apply LinearEquiv.toLinearMap_injective
    exact exteriorPower_linearMap_ext_of_surjective (mapBaseChange K S C)
      (mapBaseChange_surjective K S C hsurj') r e₀'.toLinearMap e₀.toLinearMap
      (fun z => (he₀' z).trans (he₀ z).symm)
  subst e₀'
  refine ⟨e, e', he, he', fun w => ?_⟩
  rw [hunit]
  exact LinearMap.congr_fun hnat w

end MixedFujita

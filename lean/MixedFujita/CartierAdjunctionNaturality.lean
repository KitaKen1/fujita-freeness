/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PrincipalQuotientDifferentialChange

/-! 局所標準随伴と留数の実図式自然性。 check-278：可換な実商環図式で制限された周囲微分加群の実写像を構成し、純テンソル式・余法生成元・商微分との可換性を証明。OpenAI由来の外積の係数変更APIと楔積の生成性を再利用し、正規化した局所標準随伴および逆向き留数写像の自然性を証明。実際の局所化では、元の正則主商から局所化後の正則性・全射性・核・微分基底・滑らかさを内部供給し、局所化と方程式の単元変更を同時に許す正規化留数の整合性まで構成。大域の層同型・標準Cartier因子との比較・元lc中心の数値随伴は引き続き残る。 -/

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


/-- Normalized Cartier adjunction commutes with actual chart changes.
This needs no étaleness or flatness of the change; it includes restrictions. -/
theorem principal_quotient_canonical_adjunction_naturality
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]))
    (e' : (⋀[C]^r Ω[C⁄K]) ≃ₗ[C] ⋀[C]^(1 + r) (C ⊗[S] Ω[S⁄K]))
    (he : ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
      e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
        exteriorPower.ιMulti B (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z))
    (he' : ∀ z : Fin r → C ⊗[S] Ω[S⁄K],
      e' (exteriorPower.ιMulti C r (mapBaseChange K S C ∘ z)) =
        exteriorPower.ιMulti C (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : C) ⊗ₜ[S] D K S (algebraMap A S g)) z)) :
    (exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (A := A) (S := S)) (1 + r)).comp
        e.toLinearMap =
      (e'.toLinearMap.restrictScalars B).comp (exteriorDifferentialMap K K B C r) := by
  apply exteriorPower_linearMap_ext_of_surjective (mapBaseChange K A B)
    (mapBaseChange_surjective K A B hsurj) r
  intro z
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [he, exteriorScalarMap_wedge]
  change _ = e' (exteriorScalarMap B C _ _ (KaehlerDifferential.map K K B C) r
    (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)))
  rw [exteriorScalarMap_wedge]
  have hq : KaehlerDifferential.map K K B C ∘ mapBaseChange K A B ∘ z =
      mapBaseChange K S C ∘ principalQuotientDifferentialChange (A := A) (S := S) ∘ z := by
    funext i
    exact (LinearMap.congr_fun (principalQuotientDifferentialChange_quotient_square
      (K := K) (A := A) (B := B) (S := S) (C := C)) (z i)).symm
  rw [hq, he']
  congr 1
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Function.comp_apply, Fin.append_left,
      principalQuotientDifferentialChange_conormal]
  · simp only [Function.comp_apply, Fin.append_right]


/-- Inverse local residue maps commute with the same genuine chart changes. -/
theorem principal_quotient_residue_naturality
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]))
    (e' : (⋀[C]^r Ω[C⁄K]) ≃ₗ[C] ⋀[C]^(1 + r) (C ⊗[S] Ω[S⁄K]))
    (he : ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
      e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
        exteriorPower.ιMulti B (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z))
    (he' : ∀ z : Fin r → C ⊗[S] Ω[S⁄K],
      e' (exteriorPower.ιMulti C r (mapBaseChange K S C ∘ z)) =
        exteriorPower.ιMulti C (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : C) ⊗ₜ[S] D K S (algebraMap A S g)) z)) :
    (e'.symm.toLinearMap.restrictScalars B).comp
        (exteriorScalarMap B C _ _ (principalQuotientDifferentialChange (A := A) (S := S)) (1 + r)) =
      (exteriorDifferentialMap K K B C r).comp e.symm.toLinearMap := by
  apply LinearMap.ext
  intro w
  apply e'.injective
  change e' (e'.symm _) = e' ((exteriorDifferentialMap K K B C r) (e.symm w))
  rw [e'.apply_symm_apply]
  have h := LinearMap.congr_fun
    (principal_quotient_canonical_adjunction_naturality g hsurj r e e' he he') (e.symm w)
  simpa only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, e.apply_symm_apply] using h


/-- Original regular smooth quotient-chart data construct BOTH adjunction
isomorphisms and the naturality square internally, without input residue
maps or a compatibility certificate. -/
theorem smooth_principal_quotient_exists_natural_residues
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    [Algebra.FormallySmooth K S] [Algebra.FormallySmooth K C]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (hg' : ∀ s : S, s * algebraMap A S g = 0 → s = 0)
    (hsurj' : Function.Surjective (algebraMap S C))
    (hker' : RingHom.ker (algebraMap S C) = Ideal.span {algebraMap A S g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) (c' : Module.Basis (Fin r) C Ω[C⁄K]) :
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
  obtain ⟨e, he⟩ := smooth_principal_quotient_canonical_adjunction g hg hsurj hker r c
  obtain ⟨e', he'⟩ := smooth_principal_quotient_canonical_adjunction
    (algebraMap A S g) hg' hsurj' hker' r c'
  exact ⟨e, e', he, he', principal_quotient_residue_naturality g hsurj r e e' he he'⟩

end MixedFujita

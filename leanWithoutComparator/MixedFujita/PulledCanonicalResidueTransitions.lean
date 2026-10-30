/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalResidueFrameUnits

/-! 実標準frameのJacobian変換とCartier方程式変更。 check-279：有限自由加群の実外積基底変更同型と、その楔積公式・補助基底からの独立性を構成。元の正則な滑らかな主商から、実際の周囲標準加群の引き戻し B⊗∧Ω_A と商標準加群 ∧Ω_B の間の正規化留数同型を内部構成し、実標準形式の生成元を単元倍の生成元へ送ることを証明。周囲と商の両方の基底を変える際のJacobian単元式、および方程式g→ugに対する分子の単元変更則を、この実引き戻し加群上で証明。実スキームの標準Cartier表示との同定・大域層貼合せ・元lc中心の数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita


/-- Actual ambient canonical frame changes act by the actual Jacobian
determinant under any B-linear residue map on the pulled-back top exterior line. -/
theorem pulled_canonical_residue_ambient_frame_change
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    {n : ℕ} (b b' : Module.Basis (Fin n) A M)
    (R : (B ⊗[A] (⋀[A]^n M)) →ₗ[B] N) :
    R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n b') =
      algebraMap A B (b.det b') • R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A n b) := by
  rw [alternating_basis_formula b (exteriorPower.ιMulti A n) b',
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [← Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_eq_smul_one_tmul, map_smul]


/-- Two genuine changes of canonical frames give an explicit unit transition
for residue coefficients: the ambient Jacobian and inverse target Jacobian
are supplied by the ACTUAL bases, not assumed transition certificates. -/
theorem pulled_canonical_residue_two_frame_transition
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    {m n : ℕ} (b b' : Module.Basis (Fin m) A M)
    (c c' : Module.Basis (Fin n) B N)
    (R : (B ⊗[A] (⋀[A]^m M)) →ₗ[B] ⋀[B]^n N)
    (u : Bˣ) (hu : R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A m b) =
      (u : B) • exteriorPower.ιMulti B n c) :
    ∃ v : Bˣ, (v : B) = algebraMap A B (b.det b') * ↑u * c'.det c ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A m b') =
        (v : B) • exteriorPower.ιMulti B n c' := by
  let v := Units.map (algebraMap A B) (Module.Basis.isUnit_det b b').unit * u *
    (Module.Basis.isUnit_det c' c).unit
  have hv : (v : B) = algebraMap A B (b.det b') * ↑u * c'.det c := by
    simp only [v, Units.val_mul, Units.coe_map, IsUnit.unit_spec]
    rfl
  refine ⟨v, hv, ?_⟩
  rw [pulled_canonical_residue_ambient_frame_change, hu,
    alternating_basis_formula c' (exteriorPower.ιMulti B n) c,
    smul_smul, smul_smul, hv, mul_assoc]


/-- The ACTUAL pulled-back canonical modules retain the Cartier equation
transition law: changing g to u*g scales the numerator by the same unit.
Both normalized residue maps are constructed from the original quotient. -/
theorem smooth_principal_quotient_pulled_canonical_residue_unit_change
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (b : Module.Basis (Fin (1 + r)) A Ω[A⁄K])
    (c : Module.Basis (Fin r) B Ω[B⁄K]) (u : Aˣ) :
    ∃ R R' : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K],
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        R ((finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)).symm
          (exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z))) =
          exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) ∧
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        R' ((finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)).symm
          (exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A (↑u * g)) z))) =
          exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) ∧
      ∀ w, R' (algebraMap A B ↑u • w) = R w := by
  obtain ⟨e, e', he, he', hunit⟩ :=
    smooth_principal_quotient_exists_unit_compatible_residues g hg hsurj hker r c u
  let F := finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)
  let R := F.trans e.symm
  let R' := F.trans e'.symm
  refine ⟨R, R', ?_, ?_, ?_⟩
  · intro z
    change e.symm (F (F.symm _)) = _
    rw [F.apply_symm_apply]
    apply e.injective
    rw [e.apply_symm_apply, he]
  · intro z
    change e'.symm (F (F.symm _)) = _
    rw [F.apply_symm_apply]
    apply e'.injective
    rw [e'.apply_symm_apply, he']
  · intro w
    change e'.symm (F (algebraMap A B ↑u • w)) = e.symm (F w)
    rw [map_smul, hunit]

end MixedFujita

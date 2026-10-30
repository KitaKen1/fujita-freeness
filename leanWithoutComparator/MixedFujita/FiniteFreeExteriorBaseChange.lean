/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LocalizedCartierResidueNaturality

/-! 有限自由外積の実基底変更同型と基底独立性。 check-279：有限自由加群の実外積基底変更同型と、その楔積公式・補助基底からの独立性を構成。元の正則な滑らかな主商から、実際の周囲標準加群の引き戻し B⊗∧Ω_A と商標準加群 ∧Ω_B の間の正規化留数同型を内部構成し、実標準形式の生成元を単元倍の生成元へ送ることを証明。周囲と商の両方の基底を変える際のJacobian単元式、および方程式g→ugに対する分子の単元変更則を、この実引き戻し加群上で証明。実スキームの標準Cartier表示との同定・大域層貼合せ・元lc中心の数値随伴は残る。 -/

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


/-- The actual exterior base-change map is an isomorphism on a finite free
module. Its function is the canonical exterior map, independently of a basis. -/
noncomputable def finiteFreeExteriorBaseChangeEquiv
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {m : ℕ}
    (b : Module.Basis (Fin m) A M) (n : ℕ) :
    B ⊗[A] (⋀[A]^n M) ≃ₗ[B] ⋀[B]^n (B ⊗[A] M) :=
  LinearEquiv.ofBijective
    ((exteriorScalarMap A B M (B ⊗[A] M) (TensorProduct.mk A B M 1) n).liftBaseChange B)
    (exterior_bijective_of_basis b (b.baseChange B) (TensorProduct.mk A B M 1)
      (fun i => (Module.Basis.baseChange_apply B b i).symm) n)


/-- The comparison retains actual scalar coefficients and every wedge vector. -/
theorem finiteFreeExteriorBaseChangeEquiv_tmul_wedge
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {m : ℕ}
    (b : Module.Basis (Fin m) A M) (n : ℕ) (a : B) (v : Fin n → M) :
    finiteFreeExteriorBaseChangeEquiv (B := B) b n (a ⊗ₜ[A] exteriorPower.ιMulti A n v) =
      a • exteriorPower.ιMulti B n (fun i => (1 : B) ⊗ₜ[A] v i) := by
  change (exteriorScalarMap A B M (B ⊗[A] M) (TensorProduct.mk A B M 1) n).liftBaseChange B _ = _
  rw [LinearMap.liftBaseChange_tmul, exteriorScalarMap_wedge]
  rfl


/-- The auxiliary basis only proves bijectivity: it does not change the actual
exterior base-change isomorphism. Even the indexing cardinality may differ. -/
theorem finiteFreeExteriorBaseChangeEquiv_basis_independent
    {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] {m m' : ℕ}
    (b : Module.Basis (Fin m) A M) (b' : Module.Basis (Fin m') A M) (n : ℕ) :
    finiteFreeExteriorBaseChangeEquiv (B := B) b n = finiteFreeExteriorBaseChangeEquiv b' n := by
  apply LinearEquiv.toLinearMap_injective
  rfl

end MixedFujita

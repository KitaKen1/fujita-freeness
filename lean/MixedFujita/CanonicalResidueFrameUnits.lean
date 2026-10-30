/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteFreeExteriorBaseChange

/-! 実引き戻し標準加群の正規化留数とframe単元性。 check-279：有限自由加群の実外積基底変更同型と、その楔積公式・補助基底からの独立性を構成。元の正則な滑らかな主商から、実際の周囲標準加群の引き戻し B⊗∧Ω_A と商標準加群 ∧Ω_B の間の正規化留数同型を内部構成し、実標準形式の生成元を単元倍の生成元へ送ることを証明。周囲と商の両方の基底を変える際のJacobian単元式、および方程式g→ugに対する分子の単元変更則を、この実引き戻し加群上で証明。実スキームの標準Cartier表示との同定・大域層貼合せ・元lc中心の数値随伴は残る。 -/

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


/-- A genuine linear automorphism of a ring's rank-one module sends its
standard generator to a unit; the inverse automorphism supplies its inverse. -/
theorem linearEquiv_ring_one_isUnit {R : Type*} [CommRing R] (e : R ≃ₗ[R] R) :
    IsUnit (e 1) := by
  have he (a : R) : e a = a * e 1 := by
    calc
      e a = e (a • (1 : R)) := by rw [smul_eq_mul, mul_one]
      _ = a • e 1 := e.map_smul a 1
      _ = a * e 1 := rfl
  have hmul : e.symm 1 * e 1 = 1 := by rw [← he, e.apply_symm_apply]
  exact ⟨⟨e 1, e.symm 1, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩


/-- A genuine isomorphism between the two top exterior lines carries the
ambient basis wedge to a UNIT multiple of the target basis wedge. -/
theorem exteriorLine_equiv_basis_wedge_unit
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {m n : ℕ}
    (b : Module.Basis (Fin m) R M) (c : Module.Basis (Fin n) R N)
    (e : (⋀[R]^m M) ≃ₗ[R] ⋀[R]^n N) :
    ∃ u : Rˣ, e (exteriorPower.ιMulti R m b) =
      (u : R) • exteriorPower.ιMulti R n c := by
  let a := ((determinantCoordinate b).symm.trans e).trans (determinantCoordinate c)
  have ha : a 1 = determinantCoordinate c (e (exteriorPower.ιMulti R m b)) := by
    change determinantCoordinate c (e ((determinantCoordinate b).symm 1)) = _
    congr 2
    apply (determinantCoordinate b).injective
    rw [LinearEquiv.apply_symm_apply, determinantCoordinate_wedge, Module.Basis.det_self]
  obtain ⟨u, hu⟩ := linearEquiv_ring_one_isUnit a
  refine ⟨u, ?_⟩
  apply (determinantCoordinate c).injective
  rw [map_smul, determinantCoordinate_wedge, Module.Basis.det_self, smul_eq_mul, mul_one]
  exact ha.symm.trans hu.symm


/-- Original smooth regular principal quotient data construct an isomorphism
from the ACTUAL pulled-back ambient canonical module to the quotient canonical
module, with normalized residue formula and a unit coefficient on actual frames. -/
theorem smooth_principal_quotient_pulled_canonical_residue_frame
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (b : Module.Basis (Fin (1 + r)) A Ω[A⁄K])
    (c : Module.Basis (Fin r) B Ω[B⁄K]) :
    ∃ R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K],
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        R ((finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)).symm
          (exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z))) =
          exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      ∃ u : Bˣ, R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r) b) =
        (u : B) • exteriorPower.ιMulti B r c := by
  obtain ⟨e, he⟩ := smooth_principal_quotient_canonical_adjunction g hg hsurj hker r c
  let R := (finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)).trans e.symm
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z
    change e.symm ((finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)) _) = _
    rw [LinearEquiv.apply_symm_apply]
    apply e.injective
    rw [e.apply_symm_apply, he]
  · intro z
    change e.symm (finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r) _) = _
    rw [finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
    apply e.injective
    rw [e.apply_symm_apply]
    let w : Fin r → B ⊗[A] Ω[A⁄K] := fun i => (1 : B) ⊗ₜ[A] z i
    have hq : KaehlerDifferential.map K K A B ∘ z = mapBaseChange K A B ∘ w := by
      funext i
      simp only [Function.comp_apply, w, mapBaseChange_tmul, one_smul]
    rw [hq, he]
    congr 1
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, w]
  · obtain ⟨u, hu⟩ := exteriorLine_equiv_basis_wedge_unit (b.baseChange B) c e.symm
    refine ⟨u, ?_⟩
    change e.symm (finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r) _) = _
    rw [finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
    have hb : (fun i => (1 : B) ⊗ₜ[A] b i) = (b.baseChange B : Fin (1 + r) → _) := by
      funext i
      exact (Module.Basis.baseChange_apply B b i).symm
    rw [hb]
    exact hu

end MixedFujita

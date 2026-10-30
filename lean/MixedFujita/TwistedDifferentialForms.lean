/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DifferentialFormsCoherent

/-!
The twisted sheaves `Ω^b_X(D)` (step 10).

For a Cartier divisor `D` on an integral scheme `X` over `K`, the forms with poles bounded by `D` are
the rational `b`-forms `ω` such that `f • ω` is regular at `x` for every point `x` and every local
equation `f` of `D` at `x` (`twistedFormsSections`); as for TauCeti's `𝒪_X(D) ⊆ 𝒦_X`, one local
equation at each point suffices (`smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt`, since two
local equations differ by a unit of the local ring). They form a subsheaf of modules of the rational
forms (`twistedFormsSubmodule`), the sheaf `Ω^b_X(D)` (`twistedFormsSheaf`), with `Ω^b_X(0) = Ω^b_X`
(`twistedFormsSections_zero`).

In characteristic `p`, if `g` is a local equation of `D` then `g ^ p` is one of `p • D`
(`isLocalEquationAt_nsmul_pow`) and `d(g ^ p ω) = g ^ p dω` (`rationalFormsDiff_smul_pow_char`), so the
de Rham differential preserves the forms with poles bounded by `p • D`
(`rationalFormsDiff_mem_twisted`): the de Rham complex twisted by a Frobenius pullback
`Ω^•_X(p • D)` (`twistedFormsDiff`, with `d ∘ d = 0`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- **Regularity of `f • ω` does not depend on the local equation `f`.** -/
theorem smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt {D : CartierDivisor X} {x : X}
    {f g : X.functionFieldˣ} (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) {b : ℕ}
    (ω : RationalForms K X b) :
    (f : X.functionField) • ω ∈ LinearMap.range (stalkFormsMap K b x) ↔
      (g : X.functionField) • ω ∈ LinearMap.range (stalkFormsMap K b x) := by
  obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hg
  have hu' : algebraMap (X.presheaf.stalk x) X.functionField ↑u⁻¹ * f = g := by
    rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  constructor
  · intro h
    rw [← hu', mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ h
  · intro h
    rw [← hu, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ h

variable (K) in
/-- The rational `b`-forms on `U` with poles bounded by `D`. -/
noncomputable def twistedFormsSections (D : CartierDivisor X) (b : ℕ) (U : X.Opens) :
    Submodule Γ(X, U) Γ(rationalFormsSheaf K X b, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), D.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) • rationalFormsSectionsEquiv K b U s ∈
      LinearMap.range (stalkFormsMap K b x)}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, smul_add]
    exact Submodule.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro r s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [rationalFormsSectionsEquiv_smul, smul_comm,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx r, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hs x hx f hf)

/-- One local equation at each point suffices. -/
theorem mem_twistedFormsSections_iff_exists {D : CartierDivisor X} {b : ℕ} {U : X.Opens}
    (s : Γ(rationalFormsSheaf K X b, U)) :
    s ∈ twistedFormsSections K D b U ↔ ∀ (x : X) (hx : x ∈ U), ∃ f : X.functionFieldˣ,
      D.IsLocalEquationAt x f ∧ haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) • rationalFormsSectionsEquiv K b U s ∈
          LinearMap.range (stalkFormsMap K b x) := by
  constructor
  · intro hs x hx
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    exact ⟨f, hf, hs x hx f hf⟩
  · intro hs x hx g hg
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf, hmem⟩ := hs x hx
    exact (smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf hg _).mp hmem

variable (K) in
/-- **The sheaf `Ω^b_X(D)`** as a subsheaf of modules of the rational `b`-forms. -/
noncomputable def twistedFormsSubmodule (D : CartierDivisor X) (b : ℕ) :
    (rationalFormsSheaf K X b).Submodule where
  obj U := twistedFormsSections K D b U.unop
  map {U V} i := fun s hs x hx f hf => by
    have : Nonempty V.unop := ⟨⟨x, hx⟩⟩
    have : Nonempty U.unop := ⟨⟨x, i.unop.le hx⟩⟩
    have h := rationalFormsSectionsEquiv_map K b i.unop s
    change (f : X.functionField) • rationalFormsSectionsEquiv K b V.unop
      ((rationalFormsSheaf K X b).presheaf.map i.unop.op s) ∈ _
    rw [h]
    exact hs x (i.unop.le hx) f hf
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFormsSheaf K X b).presheaf.map i.op s ∈ twistedFormsSections K D b V := hi
    rw [← rationalFormsSectionsEquiv_map K b i s]
    exact hi' x hxV f hf

variable (K) in
/-- **The sheaf `Ω^b_X(D)` of `b`-forms with poles bounded by `D`.** -/
noncomputable def twistedFormsSheaf (D : CartierDivisor X) (b : ℕ) : X.Modules :=
  (twistedFormsSubmodule K D b).toSheafOfModules

/-- `Ω^b_X(0) = Ω^b_X`. -/
theorem twistedFormsSections_zero (b : ℕ) (U : X.Opens) :
    twistedFormsSections K (0 : CartierDivisor X) b U = regularFormsSections K b U := by
  ext s
  constructor
  · intro hs x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    have h := hs x hx 1 (CartierDivisor.isLocalEquationAt_zero x)
    rwa [Units.val_one, one_smul] at h
  · intro hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf
      (CartierDivisor.isLocalEquationAt_zero x), Units.val_one, one_smul]
    exact hs x hx

/-- A power of a local equation of `D` is a local equation of the multiple of `D`. -/
theorem isLocalEquationAt_nsmul_pow {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) (m : ℕ) : (m • D).IsLocalEquationAt x (f ^ m) := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    exact CartierDivisor.isLocalEquationAt_zero x
  | succ m ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hf

/-- **In characteristic `p`, `d(g ^ p ω) = g ^ p dω`.** -/
theorem rationalFormsDiff_smul_pow_char (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n) (b : ℕ)
    (g : X.functionField) (ω : RationalForms K X b) :
    rationalFormsDiff c₀ b (g ^ p • ω) = g ^ p • rationalFormsDiff c₀ b ω := by
  apply Subtype.ext
  rw [rationalFormsDiff_coe, Submodule.coe_smul, Submodule.coe_smul, rationalFormsDiff_coe,
    rationalDeRhamDiff, kaehlerDeRhamDiff_smul, kaehlerD_pow_char (K := K) p g, map_zero,
    zero_mul, zero_add]

/-- **The de Rham differential preserves the forms with poles bounded by `p • D`.** -/
theorem rationalFormsDiff_mem_twisted (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {b : ℕ} (x : X)
    (ω : RationalForms K X b)
    (hω : ∀ f : X.functionFieldˣ, (p • D).IsLocalEquationAt x f →
      (f : X.functionField) • ω ∈ LinearMap.range (stalkFormsMap K b x))
    (f : X.functionFieldˣ) (hf : (p • D).IsLocalEquationAt x f) :
    (f : X.functionField) • rationalFormsDiff c₀ b ω ∈
      LinearMap.range (stalkFormsMap K (b + 1) x) := by
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt x
  have hgp := isLocalEquationAt_nsmul_pow hg p
  rw [smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf hgp, Units.val_pow_eq_pow_val,
    ← rationalFormsDiff_smul_pow_char p c₀ b]
  refine rationalFormsDiff_mem_range_stalkFormsMap c₀ hcover x _ ?_
  have h := hω (g ^ p) hgp
  rwa [Units.val_pow_eq_pow_val] at h

/-- **The de Rham differential of `Ω^•_X(p • D)`** on a nonempty open subset. -/
noncomputable def twistedFormsDiff (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) [Nonempty U] :
    twistedFormsSections K (p • D) b U →+ twistedFormsSections K (p • D) (b + 1) U where
  toFun s := ⟨(rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s)), fun x hx f hf => by
    rw [AddEquiv.apply_symm_apply]
    exact rationalFormsDiff_mem_twisted p c₀ hcover D x _ (s.2 x hx) f hf⟩
  map_zero' := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U 0)) = 0
    rw [map_zero, map_zero, map_zero])
  map_add' s t := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
        (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U (s + t))) =
      (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s)) +
        (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U t))
    rw [map_add, map_add, map_add])

theorem rationalFormsSectionsEquiv_twistedFormsDiff (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) [Nonempty U] (s : twistedFormsSections K (p • D) b U) :
    rationalFormsSectionsEquiv K (b + 1) U (twistedFormsDiff p c₀ hcover D b U s) =
      rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s) :=
  AddEquiv.apply_symm_apply (rationalFormsSectionsEquiv K (b + 1) U) _

/-- `d ∘ d = 0` on `Ω^•_X(p • D)`. -/
theorem twistedFormsDiff_comp (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) (b : ℕ)
    (U : X.Opens) [Nonempty U] (s : twistedFormsSections K (p • D) b U) :
    twistedFormsDiff p c₀ hcover D (b + 1) U (twistedFormsDiff p c₀ hcover D b U s) = 0 := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (b + 2) U).injective
  rw [rationalFormsSectionsEquiv_twistedFormsDiff, rationalFormsSectionsEquiv_twistedFormsDiff,
    rationalFormsDiff_comp, Submodule.coe_zero, map_zero]

end MixedFujita

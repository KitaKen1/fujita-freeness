/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Dimension inequality for homology (step 10, the dimension count of Deligne–Illusie).

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of complexes of vector spaces, the homology
sequence `H(X₁) → H(X₂) → H(X₃)` is exact in the middle (Mathlib), so if `H_i(X₁)` and `H_i(X₃)` are
finite-dimensional then so is `H_i(X₂)`, and `dim H_i(X₂) ≤ dim H_i(X₁) + dim H_i(X₃)`
(`finrank_homology_le_of_shortExact`). Applied along the filtration of the Čech–de Rham total
complex by de Rham degree, this gives `dim H^m(Tot) ≤ Σ_{i+j=m} h^j(Ω^i ⊗ L)`, the inequality used by
Deligne–Illusie to deduce Kodaira–Akizuki–Nakano vanishing from the decomposition.
-/

@[expose] public section

open CategoryTheory

namespace MixedFujita

universe u v

section LinearAlgebra

variable {k : Type u} [Field k] {A B C : Type v} [AddCommGroup A] [Module k A] [AddCommGroup B]
  [Module k B] [AddCommGroup C] [Module k C]

/-- In an exact sequence `A → B → C` with `A` and `C` finite-dimensional, `B` is
finite-dimensional. -/
theorem finiteDimensional_of_range_eq_ker (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : LinearMap.range f = LinearMap.ker g) [FiniteDimensional k A] [FiniteDimensional k C] :
    FiniteDimensional k B := by
  have h1 : ((⊤ : Submodule k B).map g).FG := IsNoetherian.noetherian _
  have h2 : ((⊤ : Submodule k B) ⊓ LinearMap.ker g).FG := by
    rw [top_inf_eq, ← h, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map f
  exact Module.finite_def.mpr (Submodule.fg_of_fg_map_of_fg_inf_ker g h1 h2)

/-- In an exact sequence `A → B → C` of finite-dimensional spaces, `dim B ≤ dim A + dim C`. -/
theorem finrank_le_of_range_eq_ker (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : LinearMap.range f = LinearMap.ker g) [FiniteDimensional k A] [FiniteDimensional k C] :
    Module.finrank k B ≤ Module.finrank k A + Module.finrank k C := by
  have := finiteDimensional_of_range_eq_ker f g h
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : Module.finrank k (LinearMap.ker g) ≤ Module.finrank k A := by
    rw [← h]
    exact LinearMap.finrank_range_le f
  have h3 : Module.finrank k (LinearMap.range g) ≤ Module.finrank k C := Submodule.finrank_le _
  omega

end LinearAlgebra

section Homology

variable {k : Type u} [Field k] {ι : Type*} {c : ComplexShape ι}

/-- **Dimension inequality for a short exact sequence of complexes.** -/
theorem finrank_homology_le_of_shortExact
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} k) c)} (hS : S.ShortExact) (i : ι)
    [FiniteDimensional k (S.X₁.homology i)] [FiniteDimensional k (S.X₃.homology i)] :
    FiniteDimensional k (S.X₂.homology i) ∧
      Module.finrank k (S.X₂.homology i) ≤
        Module.finrank k (S.X₁.homology i) + Module.finrank k (S.X₃.homology i) := by
  have hex : LinearMap.range (HomologicalComplex.homologyMap S.f i).hom =
      LinearMap.ker (HomologicalComplex.homologyMap S.g i).hom :=
    (hS.homology_exact₂ i).moduleCat_range_eq_ker
  exact ⟨finiteDimensional_of_range_eq_ker _ _ hex, finrank_le_of_range_eq_ker _ _ hex⟩

/-- If the outer complexes of a short exact sequence have zero homology in degree `i`, so has the
middle one. -/
theorem homology_subsingleton_of_shortExact
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} k) c)} (hS : S.ShortExact) (i : ι)
    (h₁ : Subsingleton (S.X₁.homology i)) (h₃ : Subsingleton (S.X₃.homology i)) :
    Subsingleton (S.X₂.homology i) := by
  have hex : LinearMap.range (HomologicalComplex.homologyMap S.f i).hom =
      LinearMap.ker (HomologicalComplex.homologyMap S.g i).hom :=
    (hS.homology_exact₂ i).moduleCat_range_eq_ker
  have key : ∀ z : S.X₂.homology i, z = 0 := by
    intro z
    have hz : z ∈ LinearMap.ker (HomologicalComplex.homologyMap S.g i).hom := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    rw [← hex] at hz
    obtain ⟨a, rfl⟩ := hz
    rw [Subsingleton.elim a 0, map_zero]
  exact ⟨fun x x' => by rw [key x, key x']⟩

end Homology

end MixedFujita

/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import SGA.Foundations.Cohomology.Modules
public import LeanPool.GrothendieckVanishing

/-!
Grothendieck's vanishing theorem for modules over the structure sheaf (step 10, infrastructure).
The cohomology of a module over the structure sheaf of a scheme, as defined in the vendored SGA
foundations, is the cohomology of its underlying sheaf of abelian groups. The vendored theorem of
Grothendieck (Hartshorne III.2.7) says that on a Noetherian topological space the cohomology of a
sheaf of abelian groups vanishes in degrees above the Krull dimension of the space. Hence on a
scheme with Noetherian underlying space the cohomology of every module over the structure sheaf
vanishes above the dimension; no quasi-coherence is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

universe u

/-- On a scheme whose underlying space is Noetherian, the cohomology of a module over the structure
sheaf vanishes in every degree above the Krull dimension of the space. -/
theorem moduleCohomology_subsingleton_of_topologicalKrullDim_lt {X : Scheme.{u}}
    [NoetherianSpace X] (M : X.Modules) (n : ℕ) (hn : topologicalKrullDim X < n) :
    Subsingleton (M.H n) := by
  have hX : NoetherianSpace X.toTopCat := ‹NoetherianSpace X›
  have h : Subsingleton (Sheaf.H M.toAbSheaf n) :=
    @GrothendieckVanishing X.toTopCat hX n hn M.toAbSheaf
  exact (Scheme.Modules.H.addEquivSheafH M n).toEquiv.subsingleton

/-- The same for the cohomology over the whole space written with the coefficient ring: the
vanishing holds for the positive-degree cohomology above a natural-number bound on the
dimension. -/
theorem moduleCohomology_subsingleton_of_topologicalKrullDim_le {X : Scheme.{u}}
    [NoetherianSpace X] (M : X.Modules) {d : ℕ} (hd : topologicalKrullDim X ≤ d) (n : ℕ)
    (hn : d < n) : Subsingleton (M.H n) :=
  moduleCohomology_subsingleton_of_topologicalKrullDim_lt M n
    (lt_of_le_of_lt hd (by exact_mod_cast hn))

end MixedFujita

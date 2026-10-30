/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import SGA.Foundations.Cohomology.Serre

/-! 実有限自由全射の大域1の像からcanonical有限生成族。 See reports/check-259-ample-ideal-generators-natural-corrections.json for the verified scope. All sufficiently high ORIGINAL ample Cartier twists of any actual coherent module are quotients of finite free sheaves, in every residue class. Actual noninvertible ideal modules are internally coherent and get finite canonical actual global generators. The canonical ideal inclusion pulls back to ZERO on its own actual closed subscheme by the actual adjunction mate. Arbitrary module tensor and NATURAL section restriction preserve this zero; finite ideal corrections preserve exact natural restriction and nonzero restricted sections even for nonreduced closed subschemes. Comparison of the finite ambient Cartier image family with center-exterior basepointfreeness, exterior LC/Bertini, ambient non-LC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000


/-- A map from the actual structure sheaf is the canonical homOfSection of its
image of the GLOBAL unit. This public identity avoids any opaque private frame
or sheafification comparison. -/
theorem unit_hom_eq_homOfSection_global_one
    {X : Scheme.{u}} {M : X.Modules} (φ : CohomologyAux.unitModule X ⟶ M) :
    CohomologyAux.homOfSection M (Scheme.Modules.Hom.app φ ⊤ (1 : Γ(X, ⊤))) = φ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  change Γ(X, U) at r
  rw [CohomologyAux.homOfSection_app]
  rw [← CohomologyAux.hom_app_presheaf_map φ (homOfLE le_top : U ⟶ ⊤)]
  change r • Scheme.Modules.Hom.app φ U (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op 1) = _
  rw [map_one]
  have h := Scheme.Modules.Hom.app_smul φ r (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one] using h.symm


/-- Any actual finite-free epimorphism is the canonical epimorphism of an
explicit finite family of actual GLOBAL sections, obtained from the images of
its actual unit basis. No supplied local or global generation is required. -/
theorem finite_free_epi_exists_canonical_global_generators
    {X : Scheme.{u}} {M : X.Modules} (k : ℕ)
    (π : CohomologyAux.unitBiproduct X k ⟶ M) [Epi π] :
    ∃ g : Fin k → Γ(M, ⊤), Epi (biproduct.desc (fun i => CohomologyAux.homOfSection M (g i))) := by
  let g (i : Fin k) := Scheme.Modules.Hom.app
    (biproduct.ι (fun _ : Fin k => CohomologyAux.unitModule X) i ≫ π) ⊤ (1 : Γ(X, ⊤))
  have heq : biproduct.desc (fun i => CohomologyAux.homOfSection M (g i)) = π := by
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.ι_desc]
    exact unit_hom_eq_homOfSection_global_one _
  exact ⟨g, heq ▸ inferInstance⟩

end MixedFujita

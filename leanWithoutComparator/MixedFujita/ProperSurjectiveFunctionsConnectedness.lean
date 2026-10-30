/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under MIT license as described in vendor/SlopdeGeometrieAlgebrique-LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors, Kenta Kitamura
-/
module
public import SGA.Foundations.Cohomology.ZariskiConnectedness

/-!
Proper fibres are preconnected when functions on affine inverse images descend
surjectively. Adapt the separating-section proof of the pinned SGA theorem
CohomologyAux.isPreconnected_preimage_singleton_of_isAffine: its final step
uses only surjectivity, so injectivity and nonempty fibres are unnecessary.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite
open AlgebraicGeometry.CohomologyAux
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Affine-open function surjectivity survives restriction to that open. -/
theorem morphismRestrict_appTop_surjective_of_affine
    (hf : ∀ V : Y.Opens, IsAffineOpen V → Function.Surjective (f.app V))
    (U : Y.Opens) (hU : IsAffineOpen U) : Function.Surjective (f ∣_ U).appTop := by
  rw [morphismRestrict_appTop]
  apply Function.Surjective.comp
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).2
  apply hf
  simpa only [Scheme.Opens.ι_image_top] using hU

/-- Properness and surjective affine function pullbacks imply preconnected fibres.
An empty fibre is allowed; no closed-image factorization or reducedness is needed. -/
theorem proper_affine_fibre_preconnected_of_function_surjective [IsAffine Y] [IsLocallyNoetherian Y]
    [IsProper f] (hf : ∀ V : Y.Opens, IsAffineOpen V → Function.Surjective (f.app V)) (y : Y) :
    _root_.IsPreconnected (f ⁻¹' {y}) := by
  rw [isPreconnected_closed_iff]
  intro G₁ G₂ hG₁ hG₂ hF ⟨x₁, hx₁F, hx₁G⟩ ⟨x₂, hx₂F, hx₂G⟩
  by_contra hne
  have hdF : ∀ x, f x = y → x ∈ G₁ → x ∉ G₂ := fun x hx h₁ h₂ ↦ hne ⟨x, hx, h₁, h₂⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  -- the bad loci, closed and not meeting the fibre
  set C := G₁ ∩ G₂ ∩ f ⁻¹' closure {y}
  have hC : IsClosed C := (hG₁.inter hG₂).inter (isClosed_closure.preimage f.continuous)
  have hyC : y ∉ f '' C := fun ⟨c, hc, hcy⟩ ↦ hdF c hcy hc.1.1 hc.1.2
  set T := (G₁ ∪ G₂)ᶜ
  have hT : IsOpen T := (hG₁.union hG₂).isOpen_compl
  have hTF : ∀ x ∈ T, f x ≠ y := fun x hx hxy ↦ hx (hF hxy)
  have hyB := not_mem_image_closure f.continuous y hT hTF
  let N : Y.Opens := ⟨(f '' C ∪ f '' closure (f ⁻¹' closure {y} ∩ T))ᶜ,
    ((f.isClosedMap _ hC).union (f.isClosedMap _ isClosed_closure)).isOpen_compl⟩
  have hyN : y ∈ N := fun h ↦ h.elim hyC hyB
  obtain ⟨_, ⟨s, rfl⟩, hys, hsN⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen Y) hyN
  -- restrict to the basic open `V = D(s)`
  set V := Y.basicOpen s
  have hVaff : IsAffineOpen V := (isAffineOpen_top Y).basicOpen s
  have : IsAffine V.toScheme := hVaff
  have : IsNoetherianRing Γ(V.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian (X := V.toScheme) ⟨⊤, isAffineOpen_top _⟩
  let g := f ∣_ V
  let y' : V.toScheme := ⟨y, hys⟩
  let I := pointIdeal (X := V.toScheme) (U := ⊤) (x := y') trivial
  have hI : ∀ a, a ∈ I ↔ y' ∉ V.toScheme.basicOpen a := fun a ↦ mem_pointIdeal _ a
  -- points of `X_V` over `V(I)` lie over the closure of `y`, inside `N`
  have hW : ∀ x' : (f ⁻¹ᵁ V).toScheme, (∀ a ∈ I, g x' ∉ V.toScheme.basicOpen a) →
      f x'.1 ∈ closure {y} ∧ f x'.1 ∈ N := by
    intro x' hx'
    have hcl : g x' ∈ closure {y'} := by
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨_, ⟨b, rfl⟩, hxb, hbo⟩ :=
        Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen V.toScheme)
          (show g x' ∈ (⟨o, ho⟩ : Opens _) from hxo)
      by_cases hyb : y' ∈ V.toScheme.basicOpen b
      · exact ⟨y', hbo hyb, rfl⟩
      · exact absurd hxb (hx' b ((hI b).mpr hyb))
    have h1 : f x'.1 = (g x').1 := (morphismRestrict_base_coe f V x').symm
    refine ⟨?_, hsN ?_⟩
    · rw [h1]
      have := image_closure_subset_closure_image V.ι.continuous ⟨g x', hcl, rfl⟩
      rwa [Set.image_singleton] at this
    · rw [h1]
      exact (g x').2
  let G₁' : Set (f ⁻¹ᵁ V).toScheme := (f ⁻¹ᵁ V).ι ⁻¹' G₁
  let G₂' : Set (f ⁻¹ᵁ V).toScheme := (f ⁻¹ᵁ V).ι ⁻¹' G₂
  obtain ⟨a, ha₁, ha₂⟩ := exists_section_separating' g I G₁' G₂'
    (hG₁.preimage (f ⁻¹ᵁ V).ι.continuous) (hG₂.preimage (f ⁻¹ᵁ V).ι.continuous)
    (fun x' hx' ↦ by
      obtain ⟨hcl, hN⟩ := hW x' hx'
      by_contra h
      refine hN (Or.inr ⟨x'.1, subset_closure ⟨hcl, fun h' ↦ h ?_⟩, rfl⟩)
      exact h'.imp id id)
    (fun x' hx' h₁ h₂ ↦ by
      obtain ⟨hcl, hN⟩ := hW x' hx'
      exact hN (Or.inl ⟨x'.1, ⟨⟨h₁, h₂⟩, hcl⟩, rfl⟩))
  -- the two points of the fibre
  have hxV : ∀ x, f x = y → x ∈ f ⁻¹ᵁ V := fun x hx ↦ by
    change f x ∈ V
    rw [hx]
    exact hys
  have hgx : ∀ x (hx : f x = y), g ⟨x, hxV x hx⟩ = y' := fun x hx ↦
    Subtype.ext ((morphismRestrict_base_coe f V _).trans hx)
  have hWx : ∀ x (hx : f x = y), ∀ b ∈ I, g ⟨x, hxV x hx⟩ ∉ V.toScheme.basicOpen b :=
    fun x hx b hb ↦ by rw [hgx x hx]; exact (hI b).mp hb
  have h₁ := ha₁ ⟨x₁, hxV x₁ hx₁F⟩ (hWx x₁ hx₁F) hx₁G
  have h₂ := ha₂ ⟨x₂, hxV x₂ hx₂F⟩ (hWx x₂ hx₂F) hx₂G
  -- `a` comes from `V`
  obtain ⟨b, rfl⟩ := morphismRestrict_appTop_surjective_of_affine f hf V hVaff a
  have e : (f ⁻¹ᵁ V).toScheme.basicOpen (g.appTop b) = g ⁻¹ᵁ V.toScheme.basicOpen b :=
    (Scheme.preimage_basicOpen g b).symm
  rw [e] at h₁ h₂
  change g _ ∈ V.toScheme.basicOpen b at h₁
  change g _ ∉ V.toScheme.basicOpen b at h₂
  rw [hgx x₁ hx₁F] at h₁
  rw [hgx x₂ hx₂F] at h₂
  exact h₂ h₁

end MixedFujita

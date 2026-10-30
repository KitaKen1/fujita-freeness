/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANaturalSectionModuleDictionary
public import MixedFujita.CartierRepresentationFrameUnits

/-! 実Cartier同型・自然次数SGA切断が個々の非消滅開を厳密に保存。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A global section with unit coefficient in any actual rank-one module
frame remains nonvanishing after an actual Cartier presentation, and conversely. -/
theorem cartierPresentedSection_mem_nonvanishing_iff_frame_unit
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (D : CartierDivisor X)
    (a : M ≅ D.sheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (x : X) (hx : x ∈ U) (s : Γ(M, ⊤)) :
    x ∈ cartierSectionNonvanishingOpen D (Scheme.Modules.Hom.app a.hom ⊤ s) ↔
      IsUnit (moduleOverFrameGlobalCoefficientGerm M U e x hx s) := by
  obtain ⟨V, hVU, hxV, f, hf, v, hv⟩ := cartierRepresentationFrameUnits_neighborhood M D a U e x hx
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient D _ x f
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxV), hv s]
  exact Units.isUnit_units_mul v _


/-- The natural-degree SGA section has exactly the nonvanishing open of
its actual global Cartier section in any actual module presentation. -/
theorem sgaNaturalSectionToCartier_nonvanishingOpen
    {X : Scheme.{u}} [IsIntegral X] (L : X.LineBundle) (n : ℕ)
    (D : CartierDivisor X) (a : L.toModules (n : ℤ) ≅ D.sheaf) (s : L.sections n) :
    cartierSectionNonvanishingOpen D (Scheme.Modules.Hom.app a.hom ⊤ (sgaNaturalSectionToModule L n s)) =
      L.nonvanishingLocus s := by
  ext x
  change x ∈ cartierSectionNonvanishingOpen D (Scheme.Modules.Hom.app a.hom ⊤ (sgaNaturalSectionToModule L n s)) ↔ x ∈ L.nonvanishingLocus s
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [L.iSup_eq_top]; exact Opens.mem_top _)
  rw [cartierPresentedSection_mem_nonvanishing_iff_frame_unit (L.toModules (n : ℤ)) D a (L.U k)
    (sgaLineBundleOverFrameIso L n k) x hk]
  unfold moduleOverFrameGlobalCoefficientGerm
  rw [sgaNaturalSectionToModule_frame_coefficient]
  constructor
  · intro h
    exact (L.mem_nonvanishingLocus s).mpr ⟨k, (X.mem_basicOpen _ x hk).mpr h⟩
  · intro h
    obtain ⟨l, hl⟩ := (L.mem_nonvanishingLocus s).mp h
    have hxl : x ∈ L.U l := (X.basicOpen_le _) hl
    have hs := s.property k l
    have hg := congrArg (X.presheaf.germ (L.U k ⊓ L.U l) x ⟨hk, hxl⟩) hs
    rw [map_mul, map_pow, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply] at hg
    rw [hg]
    exact (((L.g k l).isUnit.map (X.presheaf.germ (L.U k ⊓ L.U l) x ⟨hk, hxl⟩).hom).pow n).mul
      ((X.mem_basicOpen _ x hxl).mp hl)


/-- Actual Cartier sheaf isomorphisms preserve individual section
nonvanishing opens, not merely global-generation predicates. -/
theorem cartierSectionNonvanishingOpen_iso {X : Scheme.{u}} [IsIntegral X]
    (D E : CartierDivisor X) (a : D.sheaf ≅ E.sheaf) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionNonvanishingOpen E (Scheme.Modules.Hom.app a.hom ⊤ s) =
      cartierSectionNonvanishingOpen D s := by
  ext x
  change x ∈ cartierSectionNonvanishingOpen E (Scheme.Modules.Hom.app a.hom ⊤ s) ↔
    x ∈ cartierSectionNonvanishingOpen D s
  let C := cartierEquationOpenCover D
  let : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
  rw [cartierPresentedSection_mem_nonvanishing_iff_frame_unit D.sheaf E a (C.U x)
    (cartierOpenFrameIso D (C.U x) (C.equation x) (C.equation_eq x)) x (C.mem x) s,
    moduleOverFrameGlobalCoefficientGerm_cartier]
  exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x _ _).symm

end MixedFujita

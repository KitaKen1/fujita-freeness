/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveEquationCartier

/-!
Actual chart equations on a projectively mapped source. Their nonvanishing
opens are the intersection of the coordinate chart and the homogeneous
nonvanishing open. Avoiding the actual generic point of an integral source
therefore supplies nonzero local equations, without a Bertini input.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {n : ℕ} {R : Type u} [CommRing R]

theorem projectiveHomogeneousEquation_basicOpen (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d) :
    (polynomialProjectiveScheme n R).basicOpen (projectiveHomogeneousEquation R k d f hf) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) f := by
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)
  let e := Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
  have h := congrArg (fun W => e.hom ⁻¹ᵁ W)
    (Proj.awayι_preimage_basicOpen (𝒜 := MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one hf hd)
  simp only [← Scheme.Hom.comp_preimage, Proj.awayι, e, Iso.hom_inv_id_assoc] at h
  rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, Scheme.Hom.comp_preimage,
    SpecMap_preimage_basicOpen, Scheme.Opens.toSpecΓ_preimage_basicOpen] at h
  have hz : HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X R k) hf =
      HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) R)
        (MvPolynomial.isHomogeneous_X R k) d f (by simpa using hf) := by
    simp only [HomogeneousLocalization.Away.isLocalizationElem, pow_one]
  rw [hz] at h
  change U.ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) f =
    U.ι ⁻¹ᵁ (polynomialProjectiveScheme n R).basicOpen
      (projectiveHomogeneousEquation R k d f hf) at h
  have hi := congrArg (fun W => U.ι ''ᵁ W) h
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr (Scheme.basicOpen_le _ _)] at hi
  exact hi.symm

variable {Y : Scheme.{u}} (e : Y ⟶ polynomialProjectiveScheme n R)

noncomputable def projectivePullbackCoordinateOpen (k : Fin n) : Y.Opens :=
  e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)

noncomputable def projectivePullbackHomogeneousEquation (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    Γ(Y, projectivePullbackCoordinateOpen e k) :=
  e.app _ (projectiveHomogeneousEquation R k d f hf)

theorem projectivePullbackHomogeneousEquation_basicOpen (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d) :
    Y.basicOpen (projectivePullbackHomogeneousEquation e k d f hf) =
      projectivePullbackCoordinateOpen e k ⊓
        e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) f := by
  rw [projectivePullbackHomogeneousEquation, ← Scheme.preimage_basicOpen,
    projectiveHomogeneousEquation_basicOpen k d f hf hd, Scheme.Hom.preimage_inf]
  rfl

theorem projectivePullbackCoordinateOpen_cover :
    (⨆ k : Fin n, projectivePullbackCoordinateOpen e k) = ⊤ := by
  simp only [projectivePullbackCoordinateOpen, ← Scheme.Hom.preimage_iSup,
    polynomialProjective_coordinate_opens_cover n R, Scheme.Hom.preimage_top]

theorem projectivePullbackHomogeneousEquation_overlap (k j : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    ∃ w : Γ(Y, projectivePullbackCoordinateOpen e k ⊓
        projectivePullbackCoordinateOpen e j)ˣ,
      Y.presheaf.map (homOfLE inf_le_left).op
          (projectivePullbackHomogeneousEquation e k d f hf) =
        (w : Γ(Y, projectivePullbackCoordinateOpen e k ⊓
          projectivePullbackCoordinateOpen e j)) *
          Y.presheaf.map (homOfLE inf_le_right).op
            (projectivePullbackHomogeneousEquation e j d f hf) := by
  obtain ⟨w, hw⟩ := projectiveHomogeneousEquation_overlap R k j d f hf
  let U := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) ⊓
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)
  refine ⟨Units.map (e.app U).hom.toMonoidHom w, ?_⟩
  have h := congrArg (e.app U) hw
  rw [(e.app U).hom.map_mul] at h
  have hk := ConcreteCategory.congr_hom
    (e.naturality (homOfLE (show U ≤ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) from inf_le_left)).op)
      (projectiveHomogeneousEquation R k d f hf)
  have hj := ConcreteCategory.congr_hom
    (e.naturality (homOfLE (show U ≤ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j) from inf_le_right)).op)
      (projectiveHomogeneousEquation R j d f hf)
  dsimp only [CommRingCat.hom_comp, RingHom.comp_apply] at hk hj
  exact hk.symm.trans (h.trans (congrArg (fun a => (e.app U w) * a) hj))

noncomputable def projectivePullbackNonemptyCoordinateOpen
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) : Y.Opens :=
  projectivePullbackCoordinateOpen e k.val

instance (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    Nonempty (projectivePullbackNonemptyCoordinateOpen e k) := k.property

theorem projectivePullbackNonemptyCoordinateOpen_cover :
    (⨆ k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)},
      projectivePullbackNonemptyCoordinateOpen e k) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n R (e y)
  exact Opens.mem_iSup.mpr ⟨⟨k, ⟨⟨y, hk⟩⟩⟩, hk⟩

variable [IsIntegral Y]

theorem integral_genericPoint_mem_nonempty_open (U : Y.Opens) [Nonempty U] :
    genericPoint Y ∈ U := by
  obtain ⟨y, hy⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty U)
  exact (genericPoint_specializes y).mem_open U.isOpen hy

theorem projectivePullbackHomogeneousEquation_ne_zero
    (k : Fin n) [Nonempty (projectivePullbackCoordinateOpen e k)] (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hgeneric : (f : MvPolynomial (Fin n) R) ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    projectivePullbackHomogeneousEquation e k d f hf ≠ 0 := by
  have hmem : genericPoint Y ∈ Y.basicOpen
      (projectivePullbackHomogeneousEquation e k d f hf) := by
    rw [projectivePullbackHomogeneousEquation_basicOpen e k d f hf hd]
    exact ⟨integral_genericPoint_mem_nonempty_open _, hgeneric⟩
  intro h
  rw [h, Scheme.basicOpen_zero] at hmem
  exact hmem

theorem projectivePullbackHomogeneousEquation_germ_regular
    (k : Fin n) [Nonempty (projectivePullbackCoordinateOpen e k)] (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hgeneric : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)
    (y : Y) (hy : y ∈ projectivePullbackCoordinateOpen e k) :
    Y.presheaf.germ _ y hy (projectivePullbackHomogeneousEquation e k d f hf) ∈
      nonZeroDivisors (Y.presheaf.stalk y) :=
  regularEquation_germ_mem_nonZeroDivisors Y _ _
    (projectivePullbackHomogeneousEquation_ne_zero e k d f hf hd hgeneric) y hy

end MixedFujita

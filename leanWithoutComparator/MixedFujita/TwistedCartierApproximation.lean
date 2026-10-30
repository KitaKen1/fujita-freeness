/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedLimitCechVanishing
public import MixedFujita.ExceptionalCartierSections
public import MixedFujita.BirationalLocalExtension
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.ProperTwoAffineCurveCohomology

/-!
Sections of a Cartier divisor pulled back along a dominant morphism, on every open (step 9).

For a dominant morphism `ι : Y → X` of integral schemes and a Cartier divisor `E` on `X`, a section
of `𝒪_X(E)` over a nonempty open `W` is a rational function `g` with `f g` regular at every point of
`W`, for the local equations `f` of `E`; its image `ι^* g` in `K(Y)` is a section of `𝒪_Y(ι^* E)`
over `ι⁻¹ W` (`cartierPullback_mem_sections_on_open`). Over the empty open both sheaves have only
the zero section. These maps form a morphism of presheaves from `𝒪_X(E)` to the direct image of
`𝒪_Y(ι^* E)` (`cartierPullbackSectionsMap`), injective on every open
(`cartierPullbackSectionsMap_injective`). It is the comparison map of the twisted Čech
approximation (`scheme_H1_subsingleton_of_twisted_approximation`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

theorem eq_bot_of_not_nonempty {X : Scheme.{u}} {W : X.Opens} (h : ¬ Nonempty W) : W = ⊥ := by
  ext x
  simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  exact fun hx => h ⟨⟨x, hx⟩⟩

theorem preimage_eq_bot_of_not_nonempty {X Y : Scheme.{u}} (ι : Y ⟶ X) {W : X.Opens}
    (h : ¬ Nonempty W) : ι ⁻¹ᵁ W = ⊥ := by
  rw [eq_bot_of_not_nonempty h, Scheme.Hom.preimage_bot]

section Sections

variable {X : Scheme.{u}} [IsIntegral X]

/-- Two sections of a Cartier divisor over a nonempty open with the same rational function are
equal. -/
theorem cartierSection_ext {E : CartierDivisor X} {W : X.Opens} [Nonempty W]
    {a b : Γ(E.sheaf, W)}
    (h : rationalFunctionsEquiv (X := X) W (Scheme.Modules.Hom.app E.sheafι W a) =
      rationalFunctionsEquiv (X := X) W (Scheme.Modules.Hom.app E.sheafι W b)) : a = b :=
  CartierDivisor.sheafι_app_injective E W ((rationalFunctionsEquiv (X := X) W).injective h)

/-- A Cartier divisor has only the zero section over the empty open. -/
theorem cartierSection_subsingleton_of_eq_bot (E : CartierDivisor X) {W : X.Opens}
    (hW : W = ⊥) : Subsingleton Γ(E.sheaf, W) := by
  haveI := subsingleton_rationalFunctions (X := X) W hW
  exact ⟨fun a b => CartierDivisor.sheafι_app_injective E W (Subsingleton.elim _ _)⟩

end Sections

section PullbackMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (ι : Y ⟶ X) [IsDominant ι]

open Classical in
/-- The section of `𝒪_Y(E')` over `ι⁻¹ W` with the pulled-back rational function of a section of
`𝒪_X(E)` over `W`, for `E' = ι^* E` (zero over the empty open). -/
noncomputable def cartierPullbackSectionsFun (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') (W : X.Opens) (s : Γ(E.sheaf, W)) :
    Γ(E'.sheaf, ι ⁻¹ᵁ W) :=
  if h : Nonempty W then
    haveI := h
    haveI := dominant_preimage_nonempty ι W
    CartierDivisor.sectionMk
      ((rationalFunctionsEquiv (X := Y) (ι ⁻¹ᵁ W)).symm
        ((dominantFunctionFieldMap ι).hom (rationalFunctionsEquiv (X := X) W
          (Scheme.Modules.Hom.app E.sheafι W s))))
      (hE ▸ cartierPullback_mem_sections_on_open ι E W _ (by
        rw [LinearEquiv.symm_apply_apply]
        exact E.sheafι_app_mem W s))
  else 0

theorem cartierPullbackSectionsFun_rational (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') (W : X.Opens) [Nonempty W] [Nonempty (ι ⁻¹ᵁ W)]
    (s : Γ(E.sheaf, W)) :
    rationalFunctionsEquiv (X := Y) (ι ⁻¹ᵁ W)
        (Scheme.Modules.Hom.app E'.sheafι (ι ⁻¹ᵁ W) (cartierPullbackSectionsFun ι E E' hE W s)) =
      (dominantFunctionFieldMap ι).hom
        (rationalFunctionsEquiv (X := X) W (Scheme.Modules.Hom.app E.sheafι W s)) := by
  unfold cartierPullbackSectionsFun
  rw [dite_eq_left ‹Nonempty W›, CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

/-- The pulled-back sections as an additive map. -/
noncomputable def cartierPullbackSectionsHom (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') (W : X.Opens) :
    Γ(E.sheaf, W) →+ Γ(E'.sheaf, ι ⁻¹ᵁ W) where
  toFun := cartierPullbackSectionsFun ι E E' hE W
  map_zero' := by
    by_cases h : Nonempty W
    · haveI := dominant_preimage_nonempty ι W
      apply cartierSection_ext
      rw [cartierPullbackSectionsFun_rational, map_zero, map_zero, map_zero, map_zero, map_zero]
    · haveI := cartierSection_subsingleton_of_eq_bot E' (preimage_eq_bot_of_not_nonempty ι h)
      exact Subsingleton.elim _ _
  map_add' s t := by
    by_cases h : Nonempty W
    · haveI := dominant_preimage_nonempty ι W
      apply cartierSection_ext
      rw [map_add, map_add, cartierPullbackSectionsFun_rational, cartierPullbackSectionsFun_rational,
        cartierPullbackSectionsFun_rational, map_add, map_add, map_add]
    · haveI := cartierSection_subsingleton_of_eq_bot E' (preimage_eq_bot_of_not_nonempty ι h)
      exact Subsingleton.elim _ _

/-- The pulled-back sections form a morphism of presheaves to the direct image. -/
noncomputable def cartierPullbackSectionsMap (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') :
    E.sheaf.presheaf ⟶ ((Scheme.Modules.pushforward ι).obj E'.sheaf).presheaf where
  app W := AddCommGrpCat.ofHom (cartierPullbackSectionsHom ι E E' hE W.unop)
  naturality := by
    rintro ⟨W⟩ ⟨W'⟩ ⟨j⟩
    ext s
    change cartierPullbackSectionsFun ι E E' hE W' (E.sheaf.presheaf.map j.op s) =
      E'.sheaf.presheaf.map ((Opens.map ι.base).map j).op
        (cartierPullbackSectionsFun ι E E' hE W s)
    by_cases h : Nonempty W'
    · have : Nonempty W := ⟨⟨h.some.1, j.le h.some.2⟩⟩
      have := dominant_preimage_nonempty ι W
      have := dominant_preimage_nonempty ι W'
      apply cartierSection_ext
      have hY := E'.sheafι.mapPresheaf.naturality_apply ((Opens.map ι.base).map j).op
        (cartierPullbackSectionsFun ι E E' hE W s)
      have hX := E.sheafι.mapPresheaf.naturality_apply j.op s
      change Scheme.Modules.Hom.app E'.sheafι (ι ⁻¹ᵁ W')
          (E'.sheaf.presheaf.map ((Opens.map ι.base).map j).op
            (cartierPullbackSectionsFun ι E E' hE W s)) =
        (rationalFunctions Y).presheaf.map ((Opens.map ι.base).map j).op
          (Scheme.Modules.Hom.app E'.sheafι (ι ⁻¹ᵁ W)
            (cartierPullbackSectionsFun ι E E' hE W s)) at hY
      change Scheme.Modules.Hom.app E.sheafι W' (E.sheaf.presheaf.map j.op s) =
        (rationalFunctions X).presheaf.map j.op (Scheme.Modules.Hom.app E.sheafι W s) at hX
      rw [cartierPullbackSectionsFun_rational, hX, rationalFunctionsEquiv_map, hY,
        rationalFunctionsEquiv_map, cartierPullbackSectionsFun_rational]
    · haveI := cartierSection_subsingleton_of_eq_bot E' (preimage_eq_bot_of_not_nonempty ι h)
      exact Subsingleton.elim _ _

theorem cartierPullbackSectionsMap_app (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') (W : X.Opens) (s : Γ(E.sheaf, W)) :
    ((cartierPullbackSectionsMap ι E E' hE).app (op W)).hom s =
      cartierPullbackSectionsFun ι E E' hE W s := rfl

/-- The pulled-back sections map is injective on every open. -/
theorem cartierPullbackSectionsMap_injective (E : CartierDivisor X) (E' : CartierDivisor Y)
    (hE : cartierPullback ι E = E') (W : X.Opens) :
    Function.Injective ((cartierPullbackSectionsMap ι E E' hE).app (op W)).hom := by
  intro s t hst
  rw [cartierPullbackSectionsMap_app, cartierPullbackSectionsMap_app] at hst
  by_cases h : Nonempty W
  · haveI := dominant_preimage_nonempty ι W
    apply cartierSection_ext
    have h' := congrArg (fun a => rationalFunctionsEquiv (X := Y) (ι ⁻¹ᵁ W)
      (Scheme.Modules.Hom.app E'.sheafι (ι ⁻¹ᵁ W) a)) hst
    simp only [cartierPullbackSectionsFun_rational] at h'
    exact (dominantFunctionFieldMap ι).hom.injective h'
  · haveI := cartierSection_subsingleton_of_eq_bot E (eq_bot_of_not_nonempty h)
    exact Subsingleton.elim _ _

end PullbackMap


section BoundedPoles

variable {X : Scheme.{u}} [IsIntegral X]

/-- A local equation of a multiple of a Cartier divisor is the power of a local equation. -/
theorem isLocalEquationAt_nsmul {D : CartierDivisor X} {x : X} {f : X.functionFieldˣ}
    (hf : D.IsLocalEquationAt x f) (k : ℕ) : (k • D).IsLocalEquationAt x (f ^ k) := by
  induction k with
  | zero => simpa using CartierDivisor.isLocalEquationAt_zero x
  | succ k ih =>
    rw [succ_nsmul, pow_succ]
    exact ih.mul hf

/-- A rational function regular on the basic open of `s` in an affine open `W` becomes regular on
`W` after multiplication by a power of `s`. -/
theorem exists_germ_eq_mul_pow_of_forall_mem_range {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] (s : Γ(X, W)) [Nonempty (X.basicOpen s)] {g : X.functionField}
    (hg : ∀ x ∈ X.basicOpen s, g ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ (b : Γ(X, W)) (k : ℕ), X.germToFunctionField W b = g * X.germToFunctionField W s ^ k := by
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range (U := X.basicOpen s) hg
  letI : Algebra Γ(X, W) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  haveI := hW.isLocalization_basicOpen s
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers s) a
  refine ⟨b, k, ?_⟩
  have h := congrArg (X.germToFunctionField (X.basicOpen s)) hb
  simp only [map_mul, map_pow] at h
  change X.germToFunctionField (X.basicOpen s) a *
      X.germToFunctionField (X.basicOpen s) (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) ^ k =
    X.germToFunctionField (X.basicOpen s) (X.presheaf.map (homOfLE (X.basicOpen_le s)).op b) at h
  rw [germToFunctionField_restrict, germToFunctionField_restrict, ha] at h
  exact h.symm

/-- On an affine open `W` where `C` has the equation `c` and `D` the regular equation `s`, a
rational function `h` with `c h` regular on `D(s)` is a section of `𝒪(C + k D)` over `W` for some
`k`. -/
theorem exists_mem_sections_add_nsmul {C D : CartierDivisor X} {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] (c : X.functionFieldˣ) (hc : ∀ x ∈ W, C.IsLocalEquationAt x c)
    (s : Γ(X, W)) (u : X.functionFieldˣ) (hu : ∀ x ∈ W, D.IsLocalEquationAt x u)
    (hsu : (u : X.functionField) = X.germToFunctionField W s) [Nonempty (X.basicOpen s)]
    {h : X.functionField}
    (hh : ∀ x ∈ X.basicOpen s,
      (c : X.functionField) * h ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ k : ℕ, (rationalFunctionsEquiv (X := X) W).symm h ∈ (C + k • D).sections W := by
  obtain ⟨b, k, hb⟩ := exists_germ_eq_mul_pow_of_forall_mem_range hW s hh
  refine ⟨k, CartierDivisor.mem_sections_iff_exists.mpr fun x hx => ⟨c * u ^ k,
    (hc x hx).mul (isLocalEquationAt_nsmul (hu x hx) k), ?_⟩⟩
  rw [LinearEquiv.apply_symm_apply, Units.val_mul, Units.val_pow_eq_pow_val, hsu,
    mul_right_comm, ← hb, ← X.algebraMap_germ_eq_germToFunctionField hx]
  exact RingHom.mem_range_self _ _

end BoundedPoles

section Surjective

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (ι : Y ⟶ X) [IsOpenImmersion ι]
  [IsDominant ι]

/-- The rational function of a section of the pulled-back divisor over `ι⁻¹ W`, transported to `X`,
times a local equation of `C` on `W`, is regular at every point of `W` in the image of `ι`. -/
theorem mul_mem_range_of_cartierPullback_sections (C : CartierDivisor X) {W : X.Opens}
    [Nonempty W] [Nonempty (ι ⁻¹ᵁ W)] (c : X.functionFieldˣ)
    (hc : ∀ x ∈ W, C.IsLocalEquationAt x c) (σ : Γ((cartierPullback ι C).sheaf, ι ⁻¹ᵁ W))
    {h : X.functionField}
    (hh : (dominantFunctionFieldMap ι).hom h = rationalFunctionsEquiv (X := Y) (ι ⁻¹ᵁ W)
      (Scheme.Modules.Hom.app (cartierPullback ι C).sheafι (ι ⁻¹ᵁ W) σ))
    (y : Y) (hy : y ∈ ι ⁻¹ᵁ W) :
    (c : X.functionField) * h ∈ (algebraMap (X.presheaf.stalk (ι y)) X.functionField).range := by
  have hmem := CartierDivisor.sheafι_app_mem (cartierPullback ι C) (ι ⁻¹ᵁ W) σ
  have hloc := cartierPullback_isLocalEquationAt ι C y (hc (ι y) hy)
  obtain ⟨b, hb⟩ := (CartierDivisor.mem_sections.mp hmem) y hy _ hloc
  rw [← hh, Units.coe_map] at hb
  have hbij : Function.Bijective (ι.stalkMap y) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  obtain ⟨a, rfl⟩ := hbij.2 b
  refine ⟨a, (dominantFunctionFieldMap ι).hom.injective ?_⟩
  rw [dominantFunctionFieldMap_algebraMap, hb, map_mul]
  rfl

end Surjective

section Twisted

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (ι : Y ⟶ X) [IsOpenImmersion ι]
  [IsDominant ι]

theorem nsmul_isEffective_of_isEffective {D : CartierDivisor X} (hD : D.IsEffective) (k : ℕ) :
    (k • D).IsEffective := by
  induction k with
  | zero => simpa only [zero_nsmul] using CartierDivisor.isEffective_zero (X := X)
  | succ k ih => simpa only [succ_nsmul] using ih.add hD

/-- The pulled-back sections maps from the twists `𝒪(C + m D)`, for a divisor `D` with trivial
pullback. -/
noncomputable def twistedPullbackSectionsMap (C D : CartierDivisor X)
    (hD0 : cartierPullback ι D = 0) (m : ℕ) :
    (C + m • D).sheaf.presheaf ⟶
      ((Scheme.Modules.pushforward ι).obj (cartierPullback ι C).sheaf).presheaf :=
  cartierPullbackSectionsMap ι (C + m • D) (cartierPullback ι C)
    (by rw [cartierPullback_add, cartierPullback_nsmul, hD0, nsmul_zero, add_zero])

/-- On an affine open `W` where `C` has an equation and `D` a regular equation `s` whose basic open
lies in the image of `ι`, every section of `𝒪_Y(ι^* C)` over `ι⁻¹ W` comes from `𝒪_X(C + m D)` for
all large `m`. -/
theorem twistedPullbackSectionsMap_eventually_surjective (C D : CartierDivisor X)
    (hD : D.IsEffective) (hD0 : cartierPullback ι D = 0) {W : X.Opens} (hW : IsAffineOpen W)
    [Nonempty W] (c : X.functionFieldˣ) (hc : ∀ x ∈ W, C.IsLocalEquationAt x c)
    (s : Γ(X, W)) (u : X.functionFieldˣ) (hu : ∀ x ∈ W, D.IsLocalEquationAt x u)
    (hsu : (u : X.functionField) = X.germToFunctionField W s)
    (hV : X.basicOpen s ≤ ι.opensRange) (σ : Γ((cartierPullback ι C).sheaf, ι ⁻¹ᵁ W)) :
    ∃ k, ∀ m, k ≤ m →
      σ ∈ Set.range ((twistedPullbackSectionsMap ι C D hD0 m).app (op W)).hom := by
  have : Nonempty (ι ⁻¹ᵁ W) := dominant_preimage_nonempty ι W
  obtain ⟨h, hh⟩ := (dominantFunctionFieldMap_bijective_of_isOpenImmersion ι).2
    (rationalFunctionsEquiv (X := Y) (ι ⁻¹ᵁ W)
      (Scheme.Modules.Hom.app (cartierPullback ι C).sheafι (ι ⁻¹ᵁ W) σ))
  have : Nonempty (X.basicOpen s) := by
    refine ⟨⟨genericPoint X, (X.mem_basicOpen s (genericPoint X) (genericPoint_mem W)).mpr ?_⟩⟩
    refine isUnit_iff_ne_zero.mpr fun h0 => u.ne_zero ?_
    rw [hsu]
    exact h0
  have hh' : ∀ x ∈ X.basicOpen s,
      (c : X.functionField) * h ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by
    intro x hx
    obtain ⟨y, rfl⟩ := hV hx
    exact mul_mem_range_of_cartierPullback_sections ι C c hc σ hh y (X.basicOpen_le s hx)
  obtain ⟨k, hk⟩ := exists_mem_sections_add_nsmul hW c hc s u hu hsu hh'
  refine ⟨k, fun m hm => ?_⟩
  have hmem : (rationalFunctionsEquiv (X := X) W).symm h ∈ (C + m • D).sections W := by
    have h1 := mem_sections_add_effective_on_open (C + k • D) ((m - k) • D)
      (nsmul_isEffective_of_isEffective hD (m - k)) W h hk
    rwa [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hm] at h1
  refine ⟨CartierDivisor.sectionMk _ hmem, ?_⟩
  change cartierPullbackSectionsFun ι (C + m • D) (cartierPullback ι C)
      (by rw [cartierPullback_add, cartierPullback_nsmul, hD0, nsmul_zero, add_zero]) W
      (CartierDivisor.sectionMk _ hmem) = σ
  apply cartierSection_ext
  rw [cartierPullbackSectionsFun_rational, CartierDivisor.sheafι_app_sectionMk,
    LinearEquiv.apply_symm_apply, hh]

omit [IsOpenImmersion ι] in
/-- The twisted pulled-back sections maps are injective. -/
theorem twistedPullbackSectionsMap_injective (C D : CartierDivisor X)
    (hD0 : cartierPullback ι D = 0) (m : ℕ) (W : X.Opens) :
    Function.Injective ((twistedPullbackSectionsMap ι C D hD0 m).app (op W)).hom :=
  cartierPullbackSectionsMap_injective ι _ _ _ W

end Twisted

section Cover

theorem cechOpen_fin_two {T : TopCat.{u}} {ι : Type*} (U : ι → Opens T) (x : Fin 2 → ι) :
    TopCat.Presheaf.cechOpen U x = U (x 0) ⊓ U (x 1) := by
  apply le_antisymm
  · exact le_inf (TopCat.Presheaf.cechOpen_le U x 0) (TopCat.Presheaf.cechOpen_le U x 1)
  · refine le_iInf fun a => ?_
    fin_cases a
    · exact inf_le_left
    · exact inf_le_right

variable {X : Scheme.{u}} [IsIntegral X]

/-- Near every point there is an affine open on which `C` has an equation and the effective `D` a
regular equation. -/
theorem exists_affineOpen_equations (C D : CartierDivisor X) (hD : D.IsEffective) (x : X) :
    ∃ (W : X.Opens) (_ : IsAffineOpen W) (_ : x ∈ W) (c : X.functionFieldˣ) (s : Γ(X, W))
      (u : X.functionFieldˣ), (∀ y ∈ W, C.IsLocalEquationAt y c) ∧
      (∀ y ∈ W, D.IsLocalEquationAt y u) ∧
      ∀ (_ : Nonempty W), (u : X.functionField) = X.germToFunctionField W s := by
  obtain ⟨U, hxU, hne, a, ha, hDU⟩ := exists_affineOpen_regularEquation_of_isEffective D hD x
  obtain ⟨c, hc⟩ := C.exists_isLocalEquationAt x
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hc
  have hxUV : x ∈ (U.1 ⊓ V : X.Opens) := ⟨hxU, hxV⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxUV (U.1 ⊓ V).isOpen
  have hWU : W ≤ U.1 := fun y hy => (hWUV hy).1
  have hWV : W ≤ V := fun y hy => (hWUV hy).2
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  refine ⟨W, hW, hxW, c, X.presheaf.map (homOfLE hWU).op a,
    regularEquationRationalUnit X U.1 a ha,
    fun y hy => CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (hWV hy),
    fun y hy => CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hDU (hWU hy),
    fun _ => ?_⟩
  rw [regularEquationRationalUnit_val, germToFunctionField_restrict]

/-- Where a regular equation of `D` is a unit, `1` is a local equation of `D`. -/
theorem isLocalEquationAt_one_of_mem_basicOpen {D : CartierDivisor X} {W : X.Opens} [Nonempty W]
    (s : Γ(X, W)) (u : X.functionFieldˣ) (hu : ∀ y ∈ W, D.IsLocalEquationAt y u)
    (hsu : (u : X.functionField) = X.germToFunctionField W s) {y : X} (hy : y ∈ X.basicOpen s) :
    D.IsLocalEquationAt y 1 := by
  have : Nonempty (X.basicOpen s) := ⟨⟨y, hy⟩⟩
  have hunit := X.toRingedSpace.isUnit_res_basicOpen s
  have h := isLocalEquationAt_regularUnit_mul (hu y (X.basicOpen_le s hy)) (X.basicOpen s) hy
    hunit.unit⁻¹
  convert h using 1
  apply Units.ext
  rw [Units.val_one, Units.val_mul, map_inv, Units.val_inv_eq_inv_val,
    regularUnitToFunctionField_apply, Units.coe_map, IsUnit.unit_spec]
  change (1 : X.functionField) =
    (X.germToFunctionField (X.basicOpen s) (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s))⁻¹ *
      (u : X.functionField)
  rw [germToFunctionField_restrict, ← hsu, inv_mul_cancel₀ u.ne_zero]

/-- At a point of `W` where `1` is a local equation of `D`, a regular equation of `D` on `W` is a
unit. -/
theorem mem_basicOpen_of_isLocalEquationAt_one {D : CartierDivisor X} {W : X.Opens} [Nonempty W]
    (s : Γ(X, W)) (u : X.functionFieldˣ) (hu : ∀ y ∈ W, D.IsLocalEquationAt y u)
    (hsu : (u : X.functionField) = X.germToFunctionField W s) {y : X} (hyW : y ∈ W)
    (h1 : D.IsLocalEquationAt y 1) : y ∈ X.basicOpen s := by
  obtain ⟨v, hv⟩ := (hu y hyW).exists_unit_mul_eq h1
  rw [X.mem_basicOpen s y hyW]
  have hgerm : X.presheaf.germ W y hyW s = (v : X.presheaf.stalk y) := by
    apply IsFractionRing.injective (X.presheaf.stalk y) X.functionField
    rw [X.algebraMap_germ_eq_germToFunctionField hyW, ← hsu, ← hv, Units.val_one, mul_one]
  rw [hgerm]
  exact v.isUnit

end Cover

section Vanishing

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (ι : Y ⟶ X) [IsOpenImmersion ι]
  [IsDominant ι]

/-- **First cohomology on the complement of an effective divisor from vanishing of twists.** Let
`ι : Y → X` be an open immersion of integral schemes onto the complement of the support of an
effective Cartier divisor `D` on a Noetherian scheme with affine diagonal (`1` is a local equation of
`D` exactly at the points of the image). If `H¹(X, 𝒪(C + m D)) = 0` for all large `m`, then
`H¹(Y, 𝒪(ι^* C)) = 0`. -/
theorem cartierPullback_H1_subsingleton_of_twists [IsNoetherian X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (C D : CartierDivisor X) (hD : D.IsEffective)
    (hV : ∀ x : X, x ∈ ι.opensRange ↔ D.IsLocalEquationAt x 1) (m₀ : ℕ)
    (hvan : ∀ m, m₀ ≤ m → Subsingleton (Scheme.Modules.Cohomology (C + m • D).sheaf 1)) :
    Subsingleton (Scheme.Modules.Cohomology (cartierPullback ι C).sheaf 1) := by
  classical
  have hD0 : cartierPullback ι D = 0 := by
    apply cartierDivisor_eq_of_isLocalEquationAt
    intro y
    refine ⟨1, ?_, CartierDivisor.isLocalEquationAt_zero y⟩
    have h := cartierPullback_isLocalEquationAt ι D y ((hV (ι y)).mp ⟨y, rfl⟩)
    simpa only [map_one] using h
  choose W hW hxW c s u hc hu hsu using fun x => exists_affineOpen_equations C D hD x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (W x : Set X))
    (fun x => (W x).2) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  let pt : Fin t.card → X := fun k => (t.equivFin.symm k : X)
  let U : Fin t.card → X.Opens := fun k => W (pt k)
  have hUne : ∀ k, Nonempty (U k) := fun k => ⟨⟨pt k, hxW (pt k)⟩⟩
  have hcover : (⨆ k, U k) = ⊤ := by
    refine top_le_iff.mp fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨y, hy⟩, by simpa [U, pt] using hxy⟩
  have hbasic : ∀ k, X.basicOpen (s (pt k)) ≤ ι.opensRange := fun k y hy =>
    (hV y).mpr (haveI := hUne k
      isLocalEquationAt_one_of_mem_basicOpen (s (pt k)) (u (pt k)) (hu (pt k))
        (hsu (pt k) (hUne k)) hy)
  -- the members of the cover of `Y` are affine
  have hlocal : ∀ k, Subsingleton
      (Modules.cohomologyOn (cartierPullback ι C).sheaf 1 (ι ⁻¹ᵁ U k)) := by
    intro k
    haveI := hUne k
    haveI := (cartierPullback ι C).isInvertible_sheaf
    let := invertibleModule_isQuasicoherent (cartierPullback ι C).sheaf
    haveI := isLocallyNoetherian_of_isOpenImmersion ι
    have hpre : ι ⁻¹ᵁ U k = ι ⁻¹ᵁ X.basicOpen (s (pt k)) := by
      ext y
      constructor
      · intro hy
        exact mem_basicOpen_of_isLocalEquationAt_one (s (pt k)) (u (pt k)) (hu (pt k))
          (hsu (pt k) (hUne k)) hy ((hV (ι y)).mp ⟨y, rfl⟩)
      · intro hy
        exact X.basicOpen_le _ hy
    have haff : IsAffineOpen (ι ⁻¹ᵁ U k) := by
      rw [hpre]
      exact ((hW (pt k)).basicOpen (s (pt k))).preimage_of_isOpenImmersion ι (hbasic k)
    haveI : IsNoetherianRing Γ(Y, ι ⁻¹ᵁ U k) :=
      IsLocallyNoetherian.component_noetherian ⟨_, haff⟩
    exact Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen _ haff 0
  refine scheme_H1_subsingleton_of_twisted_approximation ι (cartierPullback ι C).sheaf
    (fun m => (C + m • D).sheaf) (twistedPullbackSectionsMap ι C D hD0) U hcover hlocal m₀ hvan
    (fun m x => twistedPullbackSectionsMap_injective ι C D hD0 m _) ?_
  intro x σ
  have hcech : TopCat.Presheaf.cechOpen U x = U (x 0) ⊓ U (x 1) := cechOpen_fin_two U x
  have hne : Nonempty (TopCat.Presheaf.cechOpen U x) := by
    rw [hcech]
    haveI := hUne (x 0)
    haveI := hUne (x 1)
    exact integral_opens_inter_nonempty X (U (x 0)) (U (x 1))
  have haff : IsAffineOpen (TopCat.Presheaf.cechOpen U x) := by
    rw [hcech]
    exact (hW _).inf (hW _)
  have hle : TopCat.Presheaf.cechOpen U x ≤ U (x 0) := TopCat.Presheaf.cechOpen_le U x 0
  haveI := hUne (x 0)
  let s' : Γ(X, TopCat.Presheaf.cechOpen U x) := X.presheaf.map (homOfLE hle).op (s (pt (x 0)))
  have hsu' : (u (pt (x 0)) : X.functionField) =
      X.germToFunctionField (TopCat.Presheaf.cechOpen U x) s' := by
    rw [germToFunctionField_restrict, hsu (pt (x 0)) (hUne (x 0))]
  have hV' : X.basicOpen s' ≤ ι.opensRange := fun y hy =>
    (hV y).mpr (isLocalEquationAt_one_of_mem_basicOpen s' (u (pt (x 0)))
      (fun z hz => hu (pt (x 0)) z (hle hz)) hsu' hy)
  exact twistedPullbackSectionsMap_eventually_surjective ι C D hD hD0 haff (c (pt (x 0)))
    (fun z hz => hc (pt (x 0)) z (hle hz)) s' (u (pt (x 0)))
    (fun z hz => hu (pt (x 0)) z (hle hz)) hsu' hV' σ

end Vanishing

end MixedFujita

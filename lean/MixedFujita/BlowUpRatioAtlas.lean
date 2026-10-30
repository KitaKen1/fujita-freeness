/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpChartSections
public import MixedFujita.RatioAtlasEmbedding

/-!
A blow-up of a scheme with a projective coordinate atlas embeds in projective space. Let X be
covered by affine opens U_i with functions u_{i,k} on U_i (the ratios x_k/x_i of an embedding),
and let the centre ideal be generated on U_i by g_{i,l}, with g_{i,l} = u_{i,k}^d g_{k,l} on
overlaps (the dehomogenizations of forms of degree d). On the chart of g_{i,j} over U_i the
functions u_{i,k} g_{i,l}/g_{i,j} are the ratios of the forms x_k G_l. They form an atlas of
ratios on the blow-up: equal to 1 for (k,l) = (i,j), multiplicative on overlaps, with transition
ratios vanishing outside the chart of their index, and generating the functions of each chart
over the base field. Hence an integral blow-up of a proper scheme is a closed subscheme of the
projective space with coordinates indexed by the pairs (k,l).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.IdealSheafData

namespace MixedFujita

universe u

section Restriction

variable {X Y : Scheme.{u}}

/-- Section maps commute with restriction on both sides. -/
theorem schemeHom_appLE_restrict_apply (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (hV : V' ≤ V) (hU : U' ≤ U) (e' : V' ≤ f ⁻¹ᵁ U') (s : Γ(Y, U)) :
    X.presheaf.map (homOfLE hV).op (f.appLE U V e s) =
      f.appLE U' V' e' (Y.presheaf.map (homOfLE hU).op s) := by
  have h1 := ConcreteCategory.congr_hom (f.appLE_map e (homOfLE hV).op) s
  have h2 := ConcreteCategory.congr_hom (f.map_appLE e' (homOfLE hU).op) s
  rw [CommRingCat.comp_apply] at h1 h2
  rw [h1, h2]

/-- Pulling back a restricted global function is restricting the pulled back global function. -/
theorem schemeHom_appLE_comp_restrict_top (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V e).hom.comp (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.comp f.appTop.hom := by
  ext s
  have h := schemeHom_appLE_restrict_apply f (U := ⊤) (V := ⊤) (fun _ _ => trivial)
    (le_top : V ≤ ⊤) (le_top : U ≤ ⊤) e s
  have h0 := ConcreteCategory.congr_hom
    (schemeHom_appLE_top_top f (fun _ _ => trivial : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤)) s
  exact h.symm.trans (congrArg _ h0)

end Restriction

section Atlas

variable {X : Scheme.{u}} (I : X.IdealSheafData) {n m : ℕ} (U : Fin n → X.affineOpens)
  (u : ∀ i, Fin n → Γ(X, U i)) (g : ∀ i, Fin m → I.ideal (U i))

/-- The coordinate of the pair (k,l) on the chart of the pair (i,j): the function
u_{i,k} g_{i,l}/g_{i,j}. -/
noncomputable def blowUpAtlasCoordinate (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) :
    Γ(blowUp I, blowUpChartOpen I (U i) (g i j)) :=
  (blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
      (blowUpChartOpen_le_preimage I (U i) (g i j)) (u i k) *
    blowUpChartSection I (U i) (g i j)
      (affineBlowUpAlgebra.frac (a := ((g i j : I.ideal (U i)) : Γ(X, U i))) (g i l).2)

/-- The coordinate of a chart's own pair is 1. -/
theorem blowUpAtlasCoordinate_self (hu1 : ∀ i, u i i = 1) (i : Fin n) (j : Fin m) :
    blowUpAtlasCoordinate I U u g i j i j = 1 := by
  rw [blowUpAtlasCoordinate, hu1, map_one, blowUpChartSection_frac_self, one_mul]

/-- The coordinate with the chart's own second index is the pulled back function u_{i,k}. -/
theorem blowUpAtlasCoordinate_snd_self (i : Fin n) (j : Fin m) (k : Fin n) :
    blowUpAtlasCoordinate I U u g i j k j =
      (blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
        (blowUpChartOpen_le_preimage I (U i) (g i j)) (u i k) := by
  rw [blowUpAtlasCoordinate, blowUpChartSection_frac_self, mul_one]

/-- The coordinate with the chart's own first index is the fraction g_{i,l}/g_{i,j}. -/
theorem blowUpAtlasCoordinate_fst_self (hu1 : ∀ i, u i i = 1) (i : Fin n) (j l : Fin m) :
    blowUpAtlasCoordinate I U u g i j i l =
      blowUpChartSection I (U i) (g i j)
        (affineBlowUpAlgebra.frac (a := ((g i j : I.ideal (U i)) : Γ(X, U i))) (g i l).2) := by
  rw [blowUpAtlasCoordinate, hu1, map_one, one_mul]

/-- A transition coordinate vanishes outside the chart of its index. -/
theorem blowUpAtlasCoordinate_basicOpen_le (d : ℕ)
    (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1)
    (hgc : ∀ i k l,
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (g i l : Γ(X, U i)) =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) ^ d *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op
            (g k l : Γ(X, U k)))
    (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) :
    (blowUp I).basicOpen (blowUpAtlasCoordinate I U u g k l i j) ≤
      blowUpChartOpen I (U i) (g i j) := by
  intro x hx
  rw [blowUpAtlasCoordinate, Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
    basicOpen_blowUpChartSection_frac] at hx
  obtain ⟨⟨-, hxu⟩, -, hxj⟩ := hx
  have hπu : blowUpπ I x ∈ X.basicOpen (u k i) := hxu
  have hπk : blowUpπ I x ∈ (U k).1 := X.basicOpen_le _ hπu
  have hπi : blowUpπ I x ∈ (U i).1 := hub k i hπu
  have hunit : IsUnit (X.presheaf.germ (U k).1 (blowUpπ I x) hπk (u k i)) :=
    (X.mem_basicOpen (u k i) (blowUpπ I x) hπk).mp hπu
  have hgerm : X.presheaf.germ (U k).1 (blowUpπ I x) hπk (g k j : Γ(X, U k)) =
      X.presheaf.germ (U k).1 (blowUpπ I x) hπk (u k i) ^ d *
        X.presheaf.germ (U i).1 (blowUpπ I x) hπi (g i j : Γ(X, U i)) := by
    have hπki : blowUpπ I x ∈ (U k).1 ⊓ (U i).1 := ⟨hπk, hπi⟩
    have h := congrArg (X.presheaf.germ ((U k).1 ⊓ (U i).1) (blowUpπ I x) hπki) (hgc k i j)
    rw [map_mul, map_pow, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply] at h
    exact h
  have hk := (blowUp.mem_range_chart_iff I (U k) (g k j) x hπk).mp hxj
  apply (blowUp.mem_range_chart_iff I (U i) (g i j) x hπi).mpr
  rw [hk, hgerm, map_mul, map_pow]
  exact Ideal.span_singleton_mul_left_unit ((hunit.map _).pow d) _

/-- The ring identity behind the cocycle of the atlas: with F₁ A = wᵈ x, F₂ A = wᵈ B and
F₃ B = x in a domain, (w s) F₁ = (w F₂)(s F₃). -/
theorem ratio_cocycle_of_relations {C : Type*} [CommRing C] [IsDomain C]
    {w s x A B F₁ F₂ F₃ t : C} (d : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (ht : t = w * s)
    (e₁ : F₁ * A = w ^ d * x) (e₂ : F₂ * A = w ^ d * B) (e₃ : F₃ * B = x) :
    t * F₁ = w * F₂ * (s * F₃) := by
  apply mul_right_cancel₀ (mul_ne_zero hA hB)
  rw [ht]
  linear_combination w * s * B * e₁ - w * s * F₃ * B * e₂ - w * s * w ^ d * B * e₃

/-- On the overlap of two charts the coordinates of one are those of the other times the
transition coordinate. -/
theorem blowUpAtlasCoordinate_cocycle [IsIntegral (blowUp I)] (d : ℕ)
    (huc : ∀ i k k',
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))
    (hgc : ∀ i k l,
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (g i l : Γ(X, U i)) =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) ^ d *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op
            (g k l : Γ(X, U k)))
    (i : Fin n) (j : Fin m) (k : Fin n) (l : Fin m) (k' : Fin n) (l' : Fin m) :
    (blowUp I).presheaf.map (homOfLE (inf_le_right :
        blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
          blowUpChartOpen I (U k) (g k l))).op (blowUpAtlasCoordinate I U u g k l k' l') =
      (blowUp I).presheaf.map (homOfLE (inf_le_right :
          blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
            blowUpChartOpen I (U k) (g k l))).op (blowUpAtlasCoordinate I U u g k l i j) *
        (blowUp I).presheaf.map (homOfLE (inf_le_left :
          blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
            blowUpChartOpen I (U i) (g i j))).op (blowUpAtlasCoordinate I U u g i j k' l') := by
  by_cases hne : Nonempty
      (blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) : (blowUp I).Opens)
  swap
  · have h0 : blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) = ⊥ := by
      rw [← Opens.not_nonempty_iff_eq_bot]
      rintro ⟨x, hx⟩
      exact hne ⟨⟨x, hx⟩⟩
    have : Subsingleton
        Γ(blowUp I, blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l)) :=
      h0 ▸ inferInstance
    exact Subsingleton.elim _ _
  have hβne : Nonempty (blowUpChartOpen I (U i) (g i j) : (blowUp I).Opens) :=
    hne.map fun x => ⟨x.1, x.2.1⟩
  have hγne : Nonempty (blowUpChartOpen I (U k) (g k l) : (blowUp I).Opens) :=
    hne.map fun x => ⟨x.1, x.2.2⟩
  have hdom : IsDomain
      Γ(blowUp I, blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l)) :=
    IsIntegral.component_integral _
  have eW : blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpπ I ⁻¹ᵁ ((U k).1 ⊓ (U i).1) := fun x hx =>
    ⟨blowUpChartOpen_le_preimage I (U k) (g k l) hx.2,
      blowUpChartOpen_le_preimage I (U i) (g i j) hx.1⟩
  have hγ (s : Γ(X, U k)) := schemeHom_appLE_restrict_apply (blowUpπ I)
    (blowUpChartOpen_le_preimage I (U k) (g k l))
    (inf_le_right : blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U k) (g k l))
    (inf_le_left : (U k).1 ⊓ (U i).1 ≤ (U k).1) eW s
  have hβ (s : Γ(X, U i)) := schemeHom_appLE_restrict_apply (blowUpπ I)
    (blowUpChartOpen_le_preimage I (U i) (g i j))
    (inf_le_left : blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U i) (g i j))
    (inf_le_right : (U k).1 ⊓ (U i).1 ≤ (U i).1) eW s
  have hinjγ := map_injective_of_isIntegral (blowUp I) (homOfLE (inf_le_right :
    blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U k) (g k l)))
  have hinjβ := map_injective_of_isIntegral (blowUp I) (homOfLE (inf_le_left :
    blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U i) (g i j)))
  have hA : (blowUpπ I).appLE ((U k).1 ⊓ (U i).1) _ eW
      (X.presheaf.map (homOfLE (inf_le_left : (U k).1 ⊓ (U i).1 ≤ (U k).1)).op
        (g k l : Γ(X, U k))) ≠ 0 := by
    rw [← hγ]
    exact fun h => blowUpπ_appLE_chart_ne_zero I (U k) (g k l)
      (hinjγ (h.trans (map_zero _).symm))
  have hB : (blowUpπ I).appLE ((U k).1 ⊓ (U i).1) _ eW
      (X.presheaf.map (homOfLE (inf_le_right : (U k).1 ⊓ (U i).1 ≤ (U i).1)).op
        (g i j : Γ(X, U i))) ≠ 0 := by
    rw [← hβ]
    exact fun h => blowUpπ_appLE_chart_ne_zero I (U i) (g i j)
      (hinjβ (h.trans (map_zero _).symm))
  have e₁ := congrArg ((blowUp I).presheaf.map (homOfLE (inf_le_right :
    blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U k) (g k l))).op) (blowUpChartSection_frac_mul I (U k) (g k l) (g k l'))
  have e₂ := congrArg ((blowUp I).presheaf.map (homOfLE (inf_le_right :
    blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U k) (g k l))).op) (blowUpChartSection_frac_mul I (U k) (g k l) (g k j))
  have e₃ := congrArg ((blowUp I).presheaf.map (homOfLE (inf_le_left :
    blowUpChartOpen I (U i) (g i j) ⊓ blowUpChartOpen I (U k) (g k l) ≤
      blowUpChartOpen I (U i) (g i j))).op) (blowUpChartSection_frac_mul I (U i) (g i j) (g i l'))
  rw [map_mul, hγ, hγ, hgc k i l', map_mul, map_pow] at e₁
  rw [map_mul, hγ, hγ, hgc k i j, map_mul, map_pow] at e₂
  rw [map_mul, hβ, hβ] at e₃
  rw [blowUpAtlasCoordinate, blowUpAtlasCoordinate, blowUpAtlasCoordinate, map_mul, map_mul,
    map_mul, hγ, hγ, hβ]
  have ht := congrArg (fun z => (blowUpπ I).appLE ((U k).1 ⊓ (U i).1) _ eW z) (huc k i k')
  dsimp only at ht
  rw [map_mul] at ht
  exact ratio_cocycle_of_relations d hA hB ht e₁ e₂ e₃

section Generation

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

open OAI.PiExponentSeshadri.Projective in
/-- The coordinates of a chart generate its functions over the base field, when the u_{i,k}
generate the functions of U_i and the g_{i,l} generate the ideal there. -/
theorem blowUpAtlasCoordinate_generate (hu1 : ∀ i, u i i = 1)
    (hg : ∀ i, Ideal.span (Set.range fun l => (g i l : Γ(X, U i))) = I.ideal (U i))
    (hugen : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top : (U i).1 ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (u i)))
    (i : Fin n) (j : Fin m) :
    Function.Surjective (MvPolynomial.eval₂Hom
      (((blowUp I).presheaf.map
          (homOfLE (le_top : blowUpChartOpen I (U i) (g i j) ≤ ⊤)).op).hom.comp
        ((blowUpπ I).appTop.hom.comp (schemeBaseScalars K X)))
      (fun q : Fin (n * m) => blowUpAtlasCoordinate I U u g i j
        (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)) := by
  rw [← RingHom.range_eq_top]
  apply blowUpChart_subring_eq_top I (U i) (g i j) (g i) (hg i)
  · intro r
    obtain ⟨p, rfl⟩ := hugen i r
    refine ⟨MvPolynomial.rename (fun k : Fin n => finProdFinEquiv (k, j)) p, ?_⟩
    have hk : ((blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
          (blowUpChartOpen_le_preimage I (U i) (g i j))).hom.comp
        ((X.presheaf.map (homOfLE (le_top : (U i).1 ≤ ⊤)).op).hom.comp
          (schemeBaseScalars K X)) =
        ((blowUp I).presheaf.map
            (homOfLE (le_top : blowUpChartOpen I (U i) (g i j) ≤ ⊤)).op).hom.comp
          ((blowUpπ I).appTop.hom.comp (schemeBaseScalars K X)) := by
      rw [← RingHom.comp_assoc, schemeHom_appLE_comp_restrict_top, RingHom.comp_assoc]
    have hc : (fun q : Fin (n * m) => blowUpAtlasCoordinate I U u g i j
          (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) ∘
        (fun k : Fin n => finProdFinEquiv (k, j)) =
        fun k => ((blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
          (blowUpChartOpen_le_preimage I (U i) (g i j))).hom (u i k) := by
      funext k
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_snd_self I U u g i j k
    have h := congrArg
      (fun φ : MvPolynomial (Fin n) K →+* Γ(blowUp I, blowUpChartOpen I (U i) (g i j)) => φ p)
      (coordinates_eval_natural
        ((blowUpπ I).appLE (U i).1 (blowUpChartOpen I (U i) (g i j))
          (blowUpChartOpen_le_preimage I (U i) (g i j))).hom
        ((X.presheaf.map (homOfLE (le_top : (U i).1 ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
        (u i))
    rw [RingHom.comp_apply, hk] at h
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename, hc]
    exact h.symm
  · intro l
    refine ⟨MvPolynomial.X (finProdFinEquiv (i, l)), ?_⟩
    rw [MvPolynomial.eval₂Hom_X', Equiv.symm_apply_apply]
    exact blowUpAtlasCoordinate_fst_self I U u g hu1 i j l

end Generation

section Embedding

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

/-- The charts of the generators over a cover of the base cover the blow-up. -/
theorem iSup_blowUpChartOpen_eq_top (hU : ⨆ i, (U i).1 = ⊤)
    (hg : ∀ i, Ideal.span (Set.range fun l => (g i l : Γ(X, U i))) = I.ideal (U i)) :
    ⨆ β : ULift.{u} (Fin n × Fin m),
      blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : blowUpπ I x ∈ ⨆ i, (U i).1 := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hs : Ideal.span (Subtype.val '' Set.range (g i)) = I.ideal (U i) := by
    rw [← Set.range_comp]
    exact hg i
  have hx' : x ∈ ⋃ a ∈ Set.range (g i), Set.range (blowUp.chart I (U i) a) := by
    rw [blowUp.iUnion_range_chart_of_span_eq I (U i) (Set.range (g i)) hs]
    exact hi
  obtain ⟨a, ⟨l, rfl⟩, hxa⟩ := Set.mem_iUnion₂.mp hx'
  exact Opens.mem_iSup.mpr ⟨⟨(i, l)⟩, hxa⟩

/-- An integral blow-up of a proper scheme with a projective coordinate atlas, along an ideal
generated on the atlas by dehomogenizations of forms of one degree, is a closed subscheme of
projective space over the base field. -/
theorem exists_closedImmersion_blowUp_of_atlas [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsLocallyNoetherian X] [IsIntegral (blowUp I)]
    (hU : ⨆ i, (U i).1 = ⊤) (hu1 : ∀ i, u i i = 1)
    (hub : ∀ i k, X.basicOpen (u i k) ≤ (U k).1)
    (huc : ∀ i k k',
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k') =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op (u k k'))
    (hugen : ∀ i, Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top : (U i).1 ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (u i)))
    (d : ℕ)
    (hg : ∀ i, Ideal.span (Set.range fun l => (g i l : Γ(X, U i))) = I.ideal (U i))
    (hgc : ∀ i k l,
      X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (g i l : Γ(X, U i)) =
        X.presheaf.map (homOfLE (inf_le_left : (U i).1 ⊓ (U k).1 ≤ (U i).1)).op (u i k) ^ d *
          X.presheaf.map (homOfLE (inf_le_right : (U i).1 ⊓ (U k).1 ≤ (U k).1)).op
            (g k l : Γ(X, U k))) :
    ∃ (e : blowUp I ⟶ polynomialProjectiveScheme (n * m) K) (_ : IsClosedImmersion e),
      e ≫ polynomialProjectiveToBase (n * m) K = blowUpπ I ≫ X ↘ Spec (CommRingCat.of K) := by
  let : (blowUp I).Over (Spec (CommRingCat.of K)) :=
    ⟨blowUpπ I ≫ X ↘ Spec (CommRingCat.of K)⟩
  have hπ : IsProper (blowUpπ I) := blowUp.isProper_π I
  have hprop : IsProper ((blowUp I) ↘ Spec (CommRingCat.of K)) := by
    change IsProper (blowUpπ I ≫ X ↘ Spec (CommRingCat.of K))
    infer_instance
  have hscal : schemeBaseScalars K (blowUp I) =
      (blowUpπ I).appTop.hom.comp (schemeBaseScalars K X) := by
    unfold schemeBaseScalars
    change ((blowUpπ I ≫ X ↘ Spec (CommRingCat.of K)).appTop.hom).comp _ = _
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc]
  exact exists_closedImmersion_of_ratioAtlas
    (fun β : ULift.{u} (Fin n × Fin m) => finProdFinEquiv β.down)
    (fun β => blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2))
    (iSup_blowUpChartOpen_eq_top I U g hU hg)
    (fun β q => blowUpAtlasCoordinate I U u g β.down.1 β.down.2
      (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
    (fun β => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_self I U u g hu1 β.down.1 β.down.2)
    (fun β γ q => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_cocycle I U u g d huc hgc β.down.1 β.down.2
        γ.down.1 γ.down.2 _ _)
    (fun β γ => by
      simp only [Equiv.symm_apply_apply]
      exact blowUpAtlasCoordinate_basicOpen_le I U u g d hub hgc β.down.1 β.down.2
        γ.down.1 γ.down.2)
    (fun β => isAffineOpen_blowUpChartOpen I (U β.down.1) (g β.down.1 β.down.2))
    (fun β => by
      rw [hscal]
      exact blowUpAtlasCoordinate_generate I U u g hu1 hg hugen β.down.1 β.down.2)

end Embedding

end Atlas

end MixedFujita

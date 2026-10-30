/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AlignedEtalePointBlowup
public import MixedFujita.SpecializationStalkEmbedding
public import MixedFujita.CartierStalkPullbackOrder

/-! Coordinate and Cartier-section compatibility for the actual map
from a point-blow-up intersection stalk to a prime stalk. The prime's
image on the original scheme may be a proper generization of the
specified closed point. Its local equation and coefficient compatibility
are derived by specialization, rather than by identifying those points. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {X : Scheme.{u}} [IsIntegral X]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

/-- A local Cartier equation remains a local equation at every generization. -/
theorem cartierLocalEquationAt_of_specializes (D : CartierDivisor X) {b x : X}
    (h : b ⤳ x) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    D.IsLocalEquationAt b f := by
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  exact CartierDivisor.isLocalEquationAt_iff.mpr ⟨V, h.mem_open V.isOpen hxV, hV⟩

/-- Specialization preserves the actual coefficient of an actual global
Cartier section in the same rational local equation. -/
theorem cartierLocalCoefficient_specializes (D : CartierDivisor X) {b x : X}
    (h : b ⤳ x) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) :
    X.presheaf.stalkSpecializes h (cartierLocalCoefficient D x f hf s) =
      cartierLocalCoefficient D b f (cartierLocalEquationAt_of_specializes D h f hf) s := by
  apply IsFractionRing.injective (X.presheaf.stalk b) X.functionField
  have hc : X.presheaf.stalkSpecializes h ≫
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk b) X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) :=
    X.presheaf.stalkSpecializes_comp ((genericPoint_spec X).specializes trivial) h
  have he := ConcreteCategory.congr_hom hc (cartierLocalCoefficient D x f hf s)
  exact he.trans ((cartierLocalCoefficient_image D x f hf s).trans
    (cartierLocalCoefficient_image D b f (cartierLocalEquationAt_of_specializes D h f hf) s).symm)

variable {K : Type u} [Field K] {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
  [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [T.Over (Spec (.of K))]

/-- The actual stalk square through the intersection commutes, including
identification of the original intersection image with the specified point. -/
theorem modelIntersectionStalkMap_comp_stalkMapAtEq
    (π : Y ⟶ X) (g : T ⟶ Y) [g.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) (x : X) (hq : π (g P) = x) (r : X.presheaf.stalk x) :
    modelIntersectionStalkMap (K := K) g h (stalkMapAtEq π (g P) x hq r) =
      (g ≫ π).stalkMap t (X.presheaf.stalkSpecializes
        ((h.map (g ≫ π).continuous).trans (specializes_of_eq hq)) r) := by
  subst x
  change T.presheaf.stalkSpecializes h (g.stalkMap P (π.stalkMap (g P) r)) = _
  have hcomp := (ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp g π P) r).symm
  exact (congrArg (T.presheaf.stalkSpecializes h) hcomp).trans
    ((g ≫ π).stalkSpecializes_stalkMap_apply t P h r).symm

/-- Actual etale-chart coordinates specialize as their actual germs do. -/
theorem etaleChartStalkCoords_specializes {n : ℕ} (c : EtaleChart K X n)
    {b x : X} (h : b ⤳ x) (hx : x ∈ c.U) (a : MvPolynomial (Fin n) K) :
    X.presheaf.stalkSpecializes h (etaleChartStalkCoords c x hx a) =
      etaleChartStalkCoords c b (h.mem_open c.U.isOpen hx) a := by
  exact ConcreteCategory.congr_hom (X.presheaf.germ_stalkSpecializes hx h) (c.coords a)

/-- The coordinate-map compatibility required by the surface coefficient
estimate follows from the actual intersection square. -/
theorem modelIntersectionStalkMap_coordinate_compatibility
    (π : Y ⟶ X) (g : T ⟶ Y) [π.IsOver (Spec (.of K))] [g.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) (x : X) (hq : π (g P) = x)
    {n : ℕ} (c : EtaleChart K X n) (hx : x ∈ c.U) (a : MvPolynomial (Fin n) K) :
    modelIntersectionStalkMap (K := K) g h
      (stalkMapAtEq π (g P) x hq (etaleChartStalkCoords c x hx a)) =
      schemeStalkMapAlgHom (K := K) (g ≫ π) t
        (etaleChartStalkCoords c ((g ≫ π) t)
          (((h.map (g ≫ π).continuous).trans (specializes_of_eq hq)).mem_open c.U.isOpen hx) a) := by
  rw [modelIntersectionStalkMap_comp_stalkMapAtEq,
    etaleChartStalkCoords_specializes]
  rfl

/-- The coefficient-map compatibility required by the surface estimate
is derived for every actual section, even when the prime image is a
proper generization of the original closed point. -/
theorem modelIntersectionStalkMap_section_coefficient_compatibility
    (π : Y ⟶ X) (g : T ⟶ Y) [g.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) (x : X) (hq : π (g P) = x)
    (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) :
    modelIntersectionStalkMap (K := K) g h
      (stalkMapAtEq π (g P) x hq (cartierLocalCoefficient D x f hf s)) =
      cartierStalkPullbackCoefficient D (g ≫ π) t f
        (cartierLocalEquationAt_of_specializes D
          ((h.map (g ≫ π).continuous).trans (specializes_of_eq hq)) f hf) s := by
  rw [modelIntersectionStalkMap_comp_stalkMapAtEq, cartierLocalCoefficient_specializes]
  rfl

end MixedFujita

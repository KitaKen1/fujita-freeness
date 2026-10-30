/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechDeligneIllusieMap

/-!
The relations of the Deligne–Illusie map on Čech cochains (step 10).

For the map `Ψ'^{b,a}` of check 464 (`(Ψ' y)_x = (-1)^{aq} Θ^{b,a}_{front}(y_{back}|)`):
* in degree `a = 0` the values are closed, `d ∘ Ψ'^{b,0} = 0` (`twistedFormsDiff_cechDIMap_zero`);
* `δ Ψ'^{b,a} y + (-1)^{q'+1} d Ψ'^{b,a+1} y = Ψ'^{b,a} (δ y)` (`cechDIMap_relation`), the
  relation (H2) of check 445: in the Čech coboundary at `x`, the faces `k ≤ a` delete a front
  vertex and give the cocycle relation of check 461, the faces `k > a` delete a back vertex and give
  the Čech coboundary of `y`, and the two terms at `k = a + 1` cancel;
* in the top degree `a = b`, `δ Ψ'^{b,b} y = Ψ'^{b,b} (δ y)` (`cechDIMap_relation_top`, from the
  top cocycle relation of check 463), the relation (H3).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

/-- Restrictions of a Čech cochain at equal index tuples agree. -/
theorem cech_restrict_congr {X : TopCat.{u}} {ι : Type*} {𝒰 : ι → Opens X}
    {P : TopCat.Presheaf AddCommGrpCat.{u} X} {m : ℕ} (y : TopCat.Presheaf.CechCochain 𝒰 P m)
    {z z' : Fin (m + 1) → ι} (hz : z = z') {V : Opens X} (h : V ≤ TopCat.Presheaf.cechOpen 𝒰 z)
    (h' : V ≤ TopCat.Presheaf.cechOpen 𝒰 z') :
    P.map (homOfLE h).op (y z) = P.map (homOfLE h').op (y z') := by
  subst hz
  rfl

section Indices

variable {ι : Type*}

/-- Deleting a front vertex `j ≤ a` moves the back face `a, …` to `a + 1, …`. -/
theorem comp_succAbove_cechBack_front {a q q' : ℕ} (hq : q + a = q') (x : Fin (q' + 2) → ι)
    (j : ℕ) (hj : j < a + 1) :
    x ∘ (Fin.succAbove (⟨j, by omega⟩ : Fin (q' + 2)) ∘ cechBack a q q' hq) =
      x ∘ cechBack (a + 1) q (q' + 1) (by omega) := by
  funext t
  simp only [Function.comp_apply]
  congr 1
  apply Fin.ext
  rw [Fin.succAbove_of_le_castSucc _ _ (by
      simp only [Fin.le_def, Fin.val_castSucc, cechBack_val]; omega),
    Fin.val_succ, cechBack_val, cechBack_val]
  omega

/-- Deleting a back vertex `a + 1 + j'` deletes the vertex `j' + 1` of the back face `a, …`. -/
theorem comp_succAbove_cechBack_back {a q q' : ℕ} (hq : q + a = q') (x : Fin (q' + 2) → ι)
    (j' : ℕ) (hj : j' < q + 1) :
    x ∘ (Fin.succAbove (⟨a + 1 + j', by omega⟩ : Fin (q' + 2)) ∘ cechBack a q q' hq) =
      (x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove (⟨j' + 1, by omega⟩ : Fin (q + 2)) := by
  funext t
  simp only [Function.comp_apply]
  congr 1
  apply Fin.ext
  rcases lt_or_ge (t : ℕ) (j' + 1) with ht | ht
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by
        simp only [Fin.lt_def, Fin.val_castSucc, cechBack_val]; omega),
      Fin.succAbove_of_castSucc_lt _ _ (by simp only [Fin.lt_def, Fin.val_castSucc]; omega),
      Fin.val_castSucc, cechBack_val, cechBack_val, Fin.val_castSucc]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by
        simp only [Fin.le_def, Fin.val_castSucc, cechBack_val]; omega),
      Fin.succAbove_of_le_castSucc _ _ (by simp only [Fin.le_def, Fin.val_castSucc]; omega),
      Fin.val_succ, cechBack_val, cechBack_val, Fin.val_succ]
    omega

/-- Deleting the first vertex of the back face `a, …` gives the back face `a + 1, …`. -/
theorem cechBack_comp_succAbove_zero {a q q' : ℕ} (hq : q + a = q') (x : Fin (q' + 2) → ι) :
    (x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove (0 : Fin (q + 2)) =
      x ∘ cechBack (a + 1) q (q' + 1) (by omega) := by
  funext t
  simp only [Function.comp_apply]
  congr 1
  apply Fin.ext
  rw [Fin.succAbove_zero, cechBack_val, cechBack_val, Fin.val_succ]
  omega

theorem comp_succAbove_cechBack_front_of_val {a q q' : ℕ} (hq : q + a = q') (x : Fin (q' + 2) → ι)
    (k : Fin (q' + 2)) (hk : (k : ℕ) < a + 1) :
    x ∘ (Fin.succAbove k ∘ cechBack a q q' hq) = x ∘ cechBack (a + 1) q (q' + 1) (by omega) := by
  have := comp_succAbove_cechBack_front hq x k hk
  rwa [show (⟨(k : ℕ), by omega⟩ : Fin (q' + 2)) = k from Fin.ext rfl] at this

theorem comp_succAbove_cechBack_back_of_val {a q q' : ℕ} (hq : q + a = q') (x : Fin (q' + 2) → ι)
    (k : Fin (q' + 2)) (j' : Fin (q + 1)) (hk : (k : ℕ) = a + 1 + j') :
    x ∘ (Fin.succAbove k ∘ cechBack a q q' hq) =
      (x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ := by
  have := comp_succAbove_cechBack_back hq x j' j'.isLt
  rwa [show (⟨a + 1 + j', by omega⟩ : Fin (q' + 2)) = k from Fin.ext hk.symm] at this

end Indices

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Chart

variable (c : EtaleChart K X n) {L : Type u} [CommRing L] (π : L →+* Γ(X, c.U))
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] [CharP K p] {J : Type*}
  (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  {D : CartierDivisor X} {g : X.functionFieldˣ}

/-- The twisted component as an additive map. -/
noncomputable def twistedChartDIComponentHom (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (b i a : ℕ) (h : i + a = b) (s : ℕ → J) :
    twistedFormsSections K D b c.U →+ twistedFormsSections K (p • D) i c.U :=
  AddMonoidHom.mk' (twistedChartDIComponent c π hπ p F hF hker hg b i a h s)
    (twistedChartDIComponent_add c π hπ p F hF hker hg b i a h s)

theorem twistedChartDIComponentHom_apply (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b i a : ℕ)
    (h : i + a = b) (s : ℕ → J) (ω : twistedFormsSections K D b c.U) :
    twistedChartDIComponentHom c π hπ p F hF hker hg b i a h s ω =
      twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω := rfl

end Chart

section Cech

variable {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (L : ∀ q, (Fin (q + 1) → Fin N) → Type u) [∀ q x, CommRing (L q x)]
  (π : ∀ q x, L q x →+* Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hπ : ∀ q x, Function.Surjective (π q x)) (p : ℕ) [Fact p.Prime] [CharP K p]
  (F : ∀ q x, Fin (q + 1) → (L q x →+* L q x)) (hF : ∀ q x k y, π q x (F q x k y) = π q x y ^ p)
  (hker : ∀ q x y, π q x y = 0 → ∃ z, y = (p : L q x) * z)
  {D : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
    D.IsLocalEquationAt y (g q x))
  (R : ∀ q (x : Fin (q + 2) → Fin N) (k : Fin (q + 2)),
    L q (x ∘ Fin.succAbove k) →+* L (q + 1) x)
  (hR : ∀ q x k z, π (q + 1) x (R q x k z) =
    (X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs i).U) x
      (Fin.succAbove k))).op).hom (π q (x ∘ Fin.succAbove k) z))
  (hRF : ∀ q x k j z, R q x k (F q (x ∘ Fin.succAbove k) j z) =
    F (q + 1) x (Fin.succAbove k j) (R q x k z))
  (hann : ∀ q x z, (p : L q x) * z = 0 → π q x z = 0) (hp2 : ∀ q x, (p : L q x) * p = 0)
  (hK : ∀ q x (k : K), ∃ k' : L q x,
    π q x k' = algebraMap K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) k ∧
      ∀ j, F q x j k' = k' ^ p)
  (hft : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)

include hann hp2 hK hft in
/-- **In Čech degree `a = 0` the values of the Deligne–Illusie map are closed.** -/
theorem twistedFormsDiff_cechDIMap_zero (b q : ℕ)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q + 1) → Fin N) :
    haveI := hne q x
    twistedFormsDiff p c₀ hcover D b (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
      (cechDIMap cs haff hne L π hπ p F hF hker g hg b b 0 (add_zero b) q q (add_zero q) y x) = 0 := by
  have := hne q x
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q x).U) := hft q x
  rw [cechDIMap_apply, map_zsmul]
  exact (congrArg (fun w => (-1 : ℤ) ^ (0 * q) • w)
    (twistedFormsDiff_twistedChartDIComponent_zero (cechEtaleChart cs haff hne q x) (π q x)
      (hπ q x) p (F q x) (hF q x) (hker q x) (hann q x) (hp2 q x) (hK q x) (hg q x) c₀ hcover b
      (cechFront q) _)).trans (smul_zero _)

/-- The component of degree `a` on `U_x` at a vertex sequence `s`, applied to the restriction of
`y` at an index tuple `z` with `U_x ≤ U_z`. -/
noncomputable def cechDIValue (b i a : ℕ) (h : i + a = b) {q m : ℕ} (x : Fin (m + 1) → Fin N)
    (s : ℕ → Fin (m + 1))
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (z : Fin (q + 1) → Fin N)
    (hz : TopCat.Presheaf.cechOpen (fun i => (cs i).U) x ≤ TopCat.Presheaf.cechOpen (fun i => (cs i).U) z) :
    twistedFormsSections K (p • D) i (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) :=
  twistedChartDIComponent (cechEtaleChart cs haff hne m x) (π m x) (hπ m x) p (F m x) (hF m x)
    (hker m x) (hg m x) b i a h s ((twistedFormsSheaf K D b).presheaf.map (homOfLE hz).op (y z))

theorem cechDIMap_eq_value (b i a : ℕ) (h : i + a = b) (q q' : ℕ) (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 1) → Fin N) :
    cechDIMap cs haff hne L π hπ p F hF hker g hg b i a h q q' hq y x =
      (-1 : ℤ) ^ (a * q) • cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x (cechFront q') y
        (x ∘ cechBack a q q' hq) (TopCat.Presheaf.cechOpen_le_comp _ x (cechBack a q q' hq)) :=
  rfl

theorem cechDIValue_congr_index (b i a : ℕ) (h : i + a = b) {q m : ℕ} (x : Fin (m + 1) → Fin N)
    (s : ℕ → Fin (m + 1))
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    {z z' : Fin (q + 1) → Fin N} (hzz : z = z') (hz) (hz') :
    cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s y z hz =
      cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s y z' hz' := by
  subst hzz
  rfl

theorem cechDIValue_congr_seq (b i a : ℕ) (h : i + a = b) {q m : ℕ} (x : Fin (m + 1) → Fin N)
    {s s' : ℕ → Fin (m + 1)} (hss : ∀ t ≤ a, s t = s' t)
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (z : Fin (q + 1) → Fin N) (hz) :
    cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s y z hz =
      cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s' y z hz :=
  twistedChartDIComponent_congr _ _ _ p _ _ _ _ b i a h hss _

include hR hRF hann hp2 hK hft in
/-- The face lemma of check 464 in terms of `cechDIValue`. -/
theorem cechDIMap_face_value (b i a : ℕ) (h : i + a = b) (q q' : ℕ) (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 2) → Fin N) (k : Fin (q' + 2)) :
    (twistedFormsSheaf K (p • D) i).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp
        (fun i => (cs i).U) x (Fin.succAbove k))).op
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b i a h q q' hq y (x ∘ Fin.succAbove k)) =
      (-1 : ℤ) ^ (a * q) • cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x
        (fun t => cechFront (q' + 1) (seqSkip k t)) y (x ∘ (Fin.succAbove k ∘ cechBack a q q' hq))
        (TopCat.Presheaf.cechOpen_le_comp _ x (Fin.succAbove k ∘ cechBack a q q' hq)) :=
  cechDIMap_face cs haff hne L π hπ p F hF hker g hg R hR hRF hann hp2 hK hft b i a h q q' hq y x k

/-- **The value at the Čech coboundary of `y`** is the alternating sum of the values at the faces of
the index tuple. -/
theorem cechDIValue_cechD (b i a : ℕ) (h : i + a = b) {q m : ℕ} (x : Fin (m + 1) → Fin N)
    (s : ℕ → Fin (m + 1))
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (z : Fin (q + 2) → Fin N) (hz) :
    cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s
        (TopCat.Presheaf.cechD (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q y) z hz =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        cechDIValue cs haff hne L π hπ p F hF hker g hg b i a h x s y (z ∘ Fin.succAbove k)
          (hz.trans (TopCat.Presheaf.cechOpen_le_comp _ z (Fin.succAbove k))) := by
  rw [cechDIValue, TopCat.Presheaf.cechD_apply, map_sum]
  simp only [map_zsmul, TopCat.Presheaf.map_map_apply]
  rw [← twistedChartDIComponentHom_apply, map_sum]
  simp only [map_zsmul, twistedChartDIComponentHom_apply]
  rfl

include hann hp2 hK hft in
/-- **The cocycle relation of check 461 for the values.** -/
theorem cechDIValue_cocycle (b i a : ℕ) (h1 : (i + 1) + a = b) (h2 : i + (a + 1) = b) {q m : ℕ}
    (x : Fin (m + 1) → Fin N) (s : ℕ → Fin (m + 1))
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (z : Fin (q + 1) → Fin N) (hz) :
    ∑ j ∈ Finset.range (a + 2), (-1 : ℤ) ^ j •
        cechDIValue cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x (s ∘ seqSkip j) y z hz =
      (-1 : ℤ) ^ a • twistedFormsDiffApp p c₀ hcover D i
        (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
        (cechDIValue cs haff hne L π hπ p F hF hker g hg b i (a + 1) h2 x s y z hz) := by
  have := hne m x
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne m x).U) := hft m x
  rw [twistedFormsDiffApp_of_nonempty]
  exact twistedChartDIComponent_cocycle (cechEtaleChart cs haff hne m x) (π m x) (hπ m x) p
    (F m x) (hF m x) (hker m x) (hann m x) (hp2 m x) (hK m x) (hg m x) c₀ hcover b i a h2 s _

local notation "𝒱" => cechDIValue cs haff hne L π hπ p F hF hker g hg

include hR hRF hann hp2 hK hft in
/-- **The relation (H2)**: `δ Ψ'^{b,a} y + (-1)^{q'+1} d Ψ'^{b,a+1} y = Ψ'^{b,a} (δ y)`. -/
theorem cechDIMap_relation (b i a : ℕ) (h1 : (i + 1) + a = b) (h2 : i + (a + 1) = b) (q q' : ℕ)
    (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 2) → Fin N) :
    TopCat.Presheaf.cechD (fun i => (cs i).U) (twistedFormsSheaf K (p • D) (i + 1)).presheaf q'
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 q q' hq y) x +
      (-1 : ℤ) ^ (q' + 1) • twistedFormsDiffApp p c₀ hcover D i
        (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x)
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b i (a + 1) h2 q (q' + 1) (by omega) y x) =
      cechDIMap cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 (q + 1) (q' + 1) (by omega)
        (TopCat.Presheaf.cechD (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q y) x := by
  have hB : TopCat.Presheaf.cechOpen (fun i => (cs i).U) x ≤ TopCat.Presheaf.cechOpen
      (fun i => (cs i).U) (x ∘ cechBack (a + 1) q (q' + 1) (by omega)) :=
    TopCat.Presheaf.cechOpen_le_comp _ x _
  have hN : (a + 1) + (q + 1) = q' + 2 := by omega
  -- left: the Čech coboundary through the face lemma; right: through the coboundary of `y`
  rw [TopCat.Presheaf.cechD_apply]
  rw [Finset.sum_congr rfl fun k _ => by
    rw [cechDIMap_face_value cs haff hne L π hπ p F hF hker g hg R hR hRF hann hp2 hK hft b (i + 1) a h1
      q q' hq y x k]]
  rw [cechDIMap_eq_value cs haff hne L π hπ p F hF hker g hg b i (a + 1) h2 q (q' + 1) _ y x,
    cechDIMap_eq_value cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 (q + 1) (q' + 1) _ _ x,
    cechDIValue_cechD, Fin.sum_univ_succ (n := q + 1), map_zsmul]
  -- split the faces of `x` into the front faces and the back faces
  rw [← (finCongr hN).sum_comp, Fin.sum_univ_add (a := a + 1) (b := q + 1)]
  -- the front faces: the back face moves to `a + 1`
  have hfront : ∀ j : Fin (a + 1),
      (-1 : ℤ) ^ ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) • (-1 : ℤ) ^ (a * q) •
        𝒱 b (i + 1) a h1 x
          (fun t => cechFront (q' + 1)
            (seqSkip ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) t)) y
          (x ∘ (Fin.succAbove (finCongr hN (Fin.castAdd (q + 1) j)) ∘ cechBack a q q' hq))
          (TopCat.Presheaf.cechOpen_le_comp _ x _) =
      (-1 : ℤ) ^ (a * q) • ((-1 : ℤ) ^ (j : ℕ) • 𝒱 b (i + 1) a h1 x
        (cechFront (q' + 1) ∘ seqSkip (j : ℕ)) y (x ∘ cechBack (a + 1) q (q' + 1) (by omega)) hB) := by
    intro j
    have hk : ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) = j := by simp
    rw [cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x _ y
      (comp_succAbove_cechBack_front_of_val hq x _ (by rw [hk]; exact j.isLt)) _ hB, smul_comm]
    simp only [hk]
    rfl
  -- the back faces: the faces of the back face `a`
  have hback : ∀ j' : Fin (q + 1),
      (-1 : ℤ) ^ ((finCongr hN (Fin.natAdd (a + 1) j') : Fin (q' + 2)) : ℕ) • (-1 : ℤ) ^ (a * q) •
        𝒱 b (i + 1) a h1 x
          (fun t => cechFront (q' + 1)
            (seqSkip ((finCongr hN (Fin.natAdd (a + 1) j') : Fin (q' + 2)) : ℕ) t)) y
          (x ∘ (Fin.succAbove (finCongr hN (Fin.natAdd (a + 1) j')) ∘ cechBack a q q' hq))
          (TopCat.Presheaf.cechOpen_le_comp _ x _) =
      ((-1 : ℤ) ^ (a * q) * (-1 : ℤ) ^ (a + 1)) • ((-1 : ℤ) ^ (j' : ℕ) • 𝒱 b (i + 1) a h1 x
        (cechFront (q' + 1)) y ((x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _))) := by
    intro j'
    have hk : ((finCongr hN (Fin.natAdd (a + 1) j') : Fin (q' + 2)) : ℕ) = a + 1 + j' := by simp
    rw [cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x _ y
      (comp_succAbove_cechBack_back_of_val hq x _ j' hk) _
      ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)),
      cechDIValue_congr_seq cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x
        (s' := cechFront (q' + 1)) (fun t ht => by
          rw [hk]
          simp only [seqSkip, show t < a + 1 + (j' : ℕ) by omega, ↓reduceIte]) y _ _,
      hk, smul_smul, smul_smul]
    congr 1
    ring
  -- the right side: the first face of the back face `a` is the back face `a + 1`
  have hzero : 𝒱 b (i + 1) a h1 x (cechFront (q' + 1)) y
      ((x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove 0)
      ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)) =
      𝒱 b (i + 1) a h1 x (cechFront (q' + 1)) y (x ∘ cechBack (a + 1) q (q' + 1) (by omega)) hB :=
    cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x _ y
      (cechBack_comp_succAbove_zero hq x) _ hB
  have hsucc : ∀ j' : Fin (q + 1), (-1 : ℤ) ^ ((j'.succ : Fin (q + 2)) : ℕ) •
      𝒱 b (i + 1) a h1 x (cechFront (q' + 1)) y
        ((x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)) =
      (-1 : ℤ) • ((-1 : ℤ) ^ (j' : ℕ) • 𝒱 b (i + 1) a h1 x (cechFront (q' + 1)) y
        ((x ∘ cechBack a (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _))) := by
    intro j'
    rw [Fin.val_succ, smul_smul, pow_succ, mul_comm]
  simp only [hfront, hback, hsucc, Fin.val_zero, pow_zero, one_smul]
  rw [hzero, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
    ← Finset.sum_range (fun j => (-1 : ℤ) ^ j • 𝒱 b (i + 1) a h1 x (cechFront (q' + 1) ∘ seqSkip j) y
      (x ∘ cechBack (a + 1) q (q' + 1) (by omega)) hB)]
  -- the cocycle relation of the front faces
  have hcoc := cechDIValue_cocycle cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft c₀ hcover b i a
    h1 h2 x (cechFront (q' + 1)) y (x ∘ cechBack (a + 1) q (q' + 1) (by omega)) hB
  rw [Finset.sum_range_succ, cechDIValue_congr_seq cs haff hne L π hπ p F hF hker g hg b (i + 1) a h1 x
    (s' := cechFront (q' + 1)) (fun t ht => by
      simp only [Function.comp_apply, seqSkip, show t < a + 1 by omega, ↓reduceIte]) y _ hB] at hcoc
  rw [eq_sub_of_add_eq hcoc]
  -- the signs
  have hs1 : (-1 : ℤ) ^ (a * (q + 1)) = (-1 : ℤ) ^ (a * q) * (-1 : ℤ) ^ a := by
    rw [mul_add, mul_one, pow_add]
  have hs2 : (-1 : ℤ) ^ (q' + 1) * (-1 : ℤ) ^ ((a + 1) * q) =
      -((-1 : ℤ) ^ (a * q) * (-1 : ℤ) ^ a) := by
    subst hq
    rw [← pow_add, show q + a + 1 + (a + 1) * q = a * q + a + 1 + 2 * q by ring, pow_add, pow_add,
      pow_mul, neg_one_sq, one_pow, mul_one, pow_one, pow_add]
    ring
  have hs3 : (-1 : ℤ) ^ (a + 1) = -(-1 : ℤ) ^ a := by
    rw [pow_succ]
    ring
  rw [smul_smul ((-1 : ℤ) ^ (q' + 1)), hs2, hs1, hs3]
  module

include hann hp2 hK hft in
/-- **The top cocycle relation of check 463 for the values.** -/
theorem cechDIValue_cocycle_top (b : ℕ) {q m : ℕ} (x : Fin (m + 1) → Fin N) (s : ℕ → Fin (m + 1))
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (z : Fin (q + 1) → Fin N) (hz) :
    ∑ j ∈ Finset.range (b + 2), (-1 : ℤ) ^ j • 𝒱 b 0 b (zero_add b) x (s ∘ seqSkip j) y z hz = 0 := by
  have := hne m x
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne m x).U) := hft m x
  exact twistedChartDIComponent_cocycle_top (cechEtaleChart cs haff hne m x) (π m x) (hπ m x) p
    (F m x) (hF m x) (hker m x) (hann m x) (hp2 m x) (hK m x) (hg m x) b s _

include hR hRF hann hp2 hK hft in
/-- **The relation (H3)** in the top degree: `δ Ψ'^{b,b} y = Ψ'^{b,b} (δ y)`. -/
theorem cechDIMap_relation_top (b q q' : ℕ) (hq : q + b = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 2) → Fin N) :
    TopCat.Presheaf.cechD (fun i => (cs i).U) (twistedFormsSheaf K (p • D) 0).presheaf q'
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) q q' hq y) x =
      cechDIMap cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) (q + 1) (q' + 1) (by omega)
        (TopCat.Presheaf.cechD (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q y) x := by
  have hB : TopCat.Presheaf.cechOpen (fun i => (cs i).U) x ≤ TopCat.Presheaf.cechOpen
      (fun i => (cs i).U) (x ∘ cechBack (b + 1) q (q' + 1) (by omega)) :=
    TopCat.Presheaf.cechOpen_le_comp _ x _
  have hN : (b + 1) + (q + 1) = q' + 2 := by omega
  rw [TopCat.Presheaf.cechD_apply]
  rw [Finset.sum_congr rfl fun k _ => by
    rw [cechDIMap_face_value cs haff hne L π hπ p F hF hker g hg R hR hRF hann hp2 hK hft b 0 b
      (zero_add b) q q' hq y x k]]
  rw [cechDIMap_eq_value cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) (q + 1) (q' + 1) _ _ x,
    cechDIValue_cechD, Fin.sum_univ_succ (n := q + 1)]
  rw [← (finCongr hN).sum_comp, Fin.sum_univ_add (a := b + 1) (b := q + 1)]
  have hfront : ∀ j : Fin (b + 1),
      (-1 : ℤ) ^ ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) • (-1 : ℤ) ^ (b * q) •
        𝒱 b 0 b (zero_add b) x
          (fun t => cechFront (q' + 1)
            (seqSkip ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) t)) y
          (x ∘ (Fin.succAbove (finCongr hN (Fin.castAdd (q + 1) j)) ∘ cechBack b q q' hq))
          (TopCat.Presheaf.cechOpen_le_comp _ x _) =
      (-1 : ℤ) ^ (b * q) • ((-1 : ℤ) ^ (j : ℕ) • 𝒱 b 0 b (zero_add b) x
        (cechFront (q' + 1) ∘ seqSkip (j : ℕ)) y (x ∘ cechBack (b + 1) q (q' + 1) (by omega)) hB) := by
    intro j
    have hk : ((finCongr hN (Fin.castAdd (q + 1) j) : Fin (q' + 2)) : ℕ) = j := by simp
    rw [cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) x _ y
      (comp_succAbove_cechBack_front_of_val hq x _ (by rw [hk]; exact j.isLt)) _ hB, smul_comm]
    simp only [hk]
    rfl
  have hback : ∀ j' : Fin (q + 1),
      (-1 : ℤ) ^ ((finCongr hN (Fin.natAdd (b + 1) j') : Fin (q' + 2)) : ℕ) • (-1 : ℤ) ^ (b * q) •
        𝒱 b 0 b (zero_add b) x
          (fun t => cechFront (q' + 1)
            (seqSkip ((finCongr hN (Fin.natAdd (b + 1) j') : Fin (q' + 2)) : ℕ) t)) y
          (x ∘ (Fin.succAbove (finCongr hN (Fin.natAdd (b + 1) j')) ∘ cechBack b q q' hq))
          (TopCat.Presheaf.cechOpen_le_comp _ x _) =
      ((-1 : ℤ) ^ (b * q) * (-1 : ℤ) ^ (b + 1)) • ((-1 : ℤ) ^ (j' : ℕ) • 𝒱 b 0 b (zero_add b) x
        (cechFront (q' + 1)) y ((x ∘ cechBack b (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _))) := by
    intro j'
    have hk : ((finCongr hN (Fin.natAdd (b + 1) j') : Fin (q' + 2)) : ℕ) = b + 1 + j' := by simp
    rw [cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) x _ y
      (comp_succAbove_cechBack_back_of_val hq x _ j' hk) _
      ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)),
      cechDIValue_congr_seq cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) x
        (s' := cechFront (q' + 1)) (fun t ht => by
          rw [hk]
          simp only [seqSkip, show t < b + 1 + (j' : ℕ) by omega, ↓reduceIte]) y _ _,
      hk, smul_smul, smul_smul]
    congr 1
    ring
  have hzero : 𝒱 b 0 b (zero_add b) x (cechFront (q' + 1)) y
      ((x ∘ cechBack b (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove 0)
      ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)) =
      𝒱 b 0 b (zero_add b) x (cechFront (q' + 1)) y (x ∘ cechBack (b + 1) q (q' + 1) (by omega)) hB :=
    cechDIValue_congr_index cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) x _ y
      (cechBack_comp_succAbove_zero hq x) _ hB
  have hsucc : ∀ j' : Fin (q + 1), (-1 : ℤ) ^ ((j'.succ : Fin (q + 2)) : ℕ) •
      𝒱 b 0 b (zero_add b) x (cechFront (q' + 1)) y
        ((x ∘ cechBack b (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _)) =
      (-1 : ℤ) • ((-1 : ℤ) ^ (j' : ℕ) • 𝒱 b 0 b (zero_add b) x (cechFront (q' + 1)) y
        ((x ∘ cechBack b (q + 1) (q' + 1) (by omega)) ∘ Fin.succAbove j'.succ)
        ((TopCat.Presheaf.cechOpen_le_comp _ x _).trans (TopCat.Presheaf.cechOpen_le_comp _ _ _))) := by
    intro j'
    rw [Fin.val_succ, smul_smul, pow_succ, mul_comm]
  simp only [hfront, hback, hsucc, Fin.val_zero, pow_zero, one_smul]
  rw [hzero, ← Finset.smul_sum, ← Finset.smul_sum, ← Finset.smul_sum,
    ← Finset.sum_range (fun j => (-1 : ℤ) ^ j • 𝒱 b 0 b (zero_add b) x (cechFront (q' + 1) ∘ seqSkip j) y
      (x ∘ cechBack (b + 1) q (q' + 1) (by omega)) hB)]
  have hcoc := cechDIValue_cocycle_top cs haff hne L π hπ p F hF hker g hg hann hp2 hK hft b x
    (cechFront (q' + 1)) y (x ∘ cechBack (b + 1) q (q' + 1) (by omega)) hB
  rw [Finset.sum_range_succ, cechDIValue_congr_seq cs haff hne L π hπ p F hF hker g hg b 0 b (zero_add b) x
    (s' := cechFront (q' + 1)) (fun t ht => by
      simp only [Function.comp_apply, seqSkip, show t < b + 1 by omega, ↓reduceIte]) y _ hB] at hcoc
  rw [eq_neg_of_add_eq_zero_left hcoc]
  have hs1 : (-1 : ℤ) ^ (b * (q + 1)) = (-1 : ℤ) ^ (b * q) * (-1 : ℤ) ^ b := by
    rw [mul_add, mul_one, pow_add]
  have hs3 : (-1 : ℤ) ^ (b + 1) = -(-1 : ℤ) ^ b := by
    rw [pow_succ]
    ring
  rw [hs1, hs3]
  module

end Cech

end MixedFujita

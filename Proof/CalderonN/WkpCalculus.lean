module

public import Proof.CalderonN.Chart
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.W1p.Multiplication

/-! From Proof/Archive/CollaboratorWkpCalculusOct17.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

 







noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace Gradient
namespace CalderonN.WkpCalculus

variable {n : ℕ}
set_option maxHeartbeats 2600000

open TauCeti

 
@[inline, reducible] def e (i : Fin n) : (X n) := EuclideanSpace.single i 1

 

 


def contr (i : Fin n) : (j : ℕ) → IteratedGradient (X n) (j + 1) →L[ℝ] IteratedGradient (X n) j
  | 0 => ∑ m : Fin n,
      (((EuclideanSpace.proj i : (X n) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.apply ℝ (X n) (e m))).smulRight (e m))
  | j + 1 => ContinuousLinearMap.compL ℝ (X n) (IteratedGradient (X n) (j + 1))
      (IteratedGradient (X n) j) (contr i j)

theorem contr_succ_apply (i : Fin n) (j : ℕ) (T : IteratedGradient (X n) (j + 2)) (v : (X n)) :
    contr i (j + 1) T v = contr i j (T v) := rfl

theorem innerSL_contr_zero (i : Fin n) (T : (X n) →L[ℝ] (X n)) :
    innerSL ℝ (contr i 0 T) =
      (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ).comp T := by
  refine ContinuousLinearMap.ext fun (v : (X n)) => ?_
  simp only [contr, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, sum_inner, inner_smul_left]
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousLinearMap.apply_apply, EuclideanSpace.inner_single_left]
  simp [mul_comm]


 
theorem hasWeakFDerivOn_clm_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {Ω : Opens (X n)}
    {u : (X n) → F} {U : (X n) → (X n) →L[ℝ] F} (h : HasWeakFDerivOn volume Ω u U) (L : F →L[ℝ] G) :
    HasWeakFDerivOn volume Ω (fun x => L (u x)) (fun x => L.comp (U x)) :=
  hasWeakFDerivOn_iff.mpr fun v => ((hasWeakFDerivOn_iff.mp h v).clm_comp L)

variable {Ω : Opens (X n)}

 

 
def d0 (i : Fin n) (u : Wkp (volume : Measure (X n)) Ω 2 1) : Wkp (volume : Measure (X n)) Ω 2 0 :=
  (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ).compLp (Wkp.iteratedGradient 0 u)

 
def d1 (i : Fin n) (w : Wkp (volume : Measure (X n)) Ω 2 2) : W1p (volume : Measure (X n)) Ω 2 :=
  W1p.mk (d0 i (Wkp.lowerOrder 1 w)) ((contr i 0).compLp (Wkp.iteratedGradient 1 w)) (by
    have h := hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient 0 w)
      (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ)
    refine (h.congr_ae ?_).congr_ae_deriv ?_
    · filter_upwards [ContinuousLinearMap.coeFn_compLp (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ)
        (Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 w))] with x hx
      exact hx.symm
    · filter_upwards [ContinuousLinearMap.coeFn_compLp (contr i 0)
        (Wkp.iteratedGradient 1 w)] with x hx
      rw [hx, innerSL_contr_zero])

theorem value_d1 (i : Fin n) (w : Wkp (volume : Measure (X n)) Ω 2 2) :
    W1p.value (d1 i w) = d0 i (Wkp.lowerOrder 1 w) := W1p.value_mk _ _ _

theorem gradient_d1 (i : Fin n) (w : Wkp (volume : Measure (X n)) Ω 2 2) :
    W1p.gradient (d1 i w) = (contr i 0).compLp (Wkp.iteratedGradient 1 w) := W1p.gradient_mk _ _ _

theorem dPack_hasWeakFDerivOn (i : Fin n) (k : ℕ) (w : Wkp (volume : Measure (X n)) Ω 2 (k + 3))
    {v : Wkp (volume : Measure (X n)) Ω 2 (k + 1)}
    (hv : ⇑(Wkp.iteratedGradient k v) =ᵐ[(volume : Measure (X n)).restrict Ω]
        fun x => contr i k (Wkp.iteratedGradient (k + 1) (Wkp.lowerOrder (k + 2) w) x)) :
    HasWeakFDerivOn volume Ω (Wkp.iteratedGradient k v)
      ((contr i (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w)) := by
  have h := hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient (k + 1) w)
    (contr i k)
  refine (h.congr_ae hv.symm).congr_ae_deriv ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLp (contr i (k + 1))
    (Wkp.iteratedGradient (k + 2) w)] with x hx
  rw [hx]
  rfl

 
def dPack (i : Fin n) : (k : ℕ) → (w : Wkp (volume : Measure (X n)) Ω 2 (k + 2)) →
    {v : Wkp (volume : Measure (X n)) Ω 2 (k + 1) //
      ⇑(Wkp.iteratedGradient k v) =ᵐ[(volume : Measure (X n)).restrict Ω]
        fun x => contr i k (Wkp.iteratedGradient (k + 1) w x)}
  | 0, w => ⟨(d1 i w : Wkp (volume : Measure (X n)) Ω 2 1), by
      have h := Wkp.iteratedGradient_zero (d1 i w : Wkp (volume : Measure (X n)) Ω 2 1)
      rw [h]
      erw [gradient_d1]
      exact ContinuousLinearMap.coeFn_compLp _ _⟩
  | k + 1, w =>
    ⟨Wkp.mk k (dPack i k (Wkp.lowerOrder (k + 2) w)).1
        ((contr i (k + 1)).compLp (Wkp.iteratedGradient (k + 2) w))
        (dPack_hasWeakFDerivOn i k w (dPack i k (Wkp.lowerOrder (k + 2) w)).2), by
      rw [Wkp.iteratedGradient_mk]
      exact ContinuousLinearMap.coeFn_compLp _ _⟩

 
def d (i : Fin n) : (k : ℕ) → Wkp (volume : Measure (X n)) Ω 2 (k + 1) →
    Wkp (volume : Measure (X n)) Ω 2 k
  | 0, u => d0 i u
  | k + 1, u => (dPack i k u).1


theorem d_succ (i : Fin n) (k : ℕ) (u : Wkp (volume : Measure (X n)) Ω 2 (k + 2)) :
    d i (k + 1) u = (dPack i k u).1 := rfl

 
theorem lowerOrder_d (i : Fin n) : ∀ (k : ℕ) (u : Wkp (volume : Measure (X n)) Ω 2 (k + 2)),
    Wkp.lowerOrder k (d i (k + 1) u) = d i k (Wkp.lowerOrder (k + 1) u)
  | 0, u => by
      rw [d_succ]
      exact (Wkp.lowerOrder_zero (d1 i u : Wkp (volume : Measure (X n)) Ω 2 1)).trans
        (value_d1 i u)
  | k + 1, u => by
      show Wkp.lowerOrder (k + 1) (dPack i (k + 1) u).1 = (dPack i k (Wkp.lowerOrder (k + 2) u)).1
      rw [dPack]
      exact Wkp.lowerOrder_mk _ _ _ (dPack_hasWeakFDerivOn i k u (dPack i k _).2)

 
theorem iteratedGradient_d (i : Fin n) (k : ℕ) (u : Wkp (volume : Measure (X n)) Ω 2 (k + 2)) :
    Wkp.iteratedGradient k (d i (k + 1) u) =
      (contr i k).compLp (Wkp.iteratedGradient (k + 1) u) := by
  apply Lp.ext
  filter_upwards [(dPack i k u).2, ContinuousLinearMap.coeFn_compLp (contr i k)
    (Wkp.iteratedGradient (k + 1) u)] with x h1 h2
  rw [d_succ, h1, h2]

 
theorem value_d (i : Fin n) : ∀ (k : ℕ) (u : Wkp (volume : Measure (X n)) Ω 2 (k + 1)),
    ⇑(Wkp.value k (d i k u)) =ᵐ[(volume : Measure (X n)).restrict Ω]
      fun x => W1p.gradient (Wkp.firstOrder k u) x i
  | 0, u => by
      rw [Wkp.value_zero, Wkp.firstOrder_zero]
      filter_upwards [ContinuousLinearMap.coeFn_compLp (EuclideanSpace.proj i : (X n) →L[ℝ] ℝ)
        (Wkp.iteratedGradient 0 u)] with x hx
      rw [d, d0, hx, Wkp.iteratedGradient_zero]
      rfl
  | k + 1, u => by
      rw [Wkp.value_succ, lowerOrder_d, Wkp.firstOrder_succ]
      exact value_d i k _

def lift (i : Fin n) : (j : ℕ) → IteratedGradient (X n) j →L[ℝ] IteratedGradient (X n) (j + 1)
  | 0 => (ContinuousLinearMap.compL ℝ (X n) ℝ (X n)
      (ContinuousLinearMap.toSpanSingleton ℝ (e i))).comp (innerSL ℝ)
  | j + 1 => ContinuousLinearMap.compL ℝ (X n) (IteratedGradient (X n) j)
      (IteratedGradient (X n) (j + 1)) (lift i j)

theorem hasWeakFDerivOn_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {ι : Type*} (s : Finset ι) {u : ι → (X n) → F} {U : ι → (X n) → (X n) →L[ℝ] F}
    (h : ∀ i ∈ s, HasWeakFDerivOn volume Ω (u i) (U i)) :
    HasWeakFDerivOn volume Ω (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, U i x) := by
  refine hasWeakFDerivOn_iff.mpr fun v => ?_
  have := HasWeakLineDerivOn.sum (v := v) s fun i hi => hasWeakFDerivOn_iff.mp (h i hi) v
  simpa only [FunLike.coe_sum, Finset.sum_apply] using this

 
def topField : (k : ℕ) → (Fin n → Wkp (volume : Measure (X n)) Ω 2 k) → (X n) → IteratedGradient (X n) k
  | 0, g => fun x => ∑ i, Wkp.value 0 (g i) x • e i
  | k + 1, g => fun x => ∑ i, lift i k (Wkp.iteratedGradient k (g i) x)

theorem hasWeakFDerivOn_topField : ∀ (k : ℕ) (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 (k + 1)),
    HasWeakFDerivOn volume Ω (topField k fun i => Wkp.lowerOrder k (g i))
      (fun x => ∑ i, lift i k (Wkp.iteratedGradient k (g i) x))
  | 0, g => by
      refine hasWeakFDerivOn_sum Finset.univ fun i _ => ?_
      exact hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_value (g i))
        (ContinuousLinearMap.toSpanSingleton ℝ (e i))
  | k + 1, g => by
      refine hasWeakFDerivOn_sum Finset.univ fun i _ => ?_
      exact hasWeakFDerivOn_clm_comp (Wkp.hasWeakFDerivOn_iteratedGradient k (g i)) (lift i k)

theorem ofPartials_hasWeakFDerivOn (k : ℕ) (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 (k + 1))
    {U : Wkp (volume : Measure (X n)) Ω 2 (k + 1)}
    (hU : ⇑(Wkp.iteratedGradient k U) =ᵐ[(volume : Measure (X n)).restrict Ω]
      topField k fun i => Wkp.lowerOrder k (g i)) :
    HasWeakFDerivOn volume Ω (Wkp.iteratedGradient k U)
      ((∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i)) :
        Lp (IteratedGradient (X n) (k + 1)) 2 ((volume : Measure (X n)).restrict Ω))) := by
  refine ((hasWeakFDerivOn_topField k g).congr_ae hU.symm).congr_ae_deriv ?_
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (lift i k).compLp (Wkp.iteratedGradient k (g i))),
    ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp (lift i k)
      (Wkp.iteratedGradient k (g i))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => (h2 i).symm

 
theorem gradientSum_ae (k : ℕ)
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 (k + 1)) :
    ⇑(∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i)) :
        Lp (IteratedGradient (X n) (k + 1)) 2 ((volume : Measure (X n)).restrict Ω)) =ᵐ[
          (volume : Measure (X n)).restrict Ω] topField (k + 1) g := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i => (lift i k).compLp (Wkp.iteratedGradient k (g i))),
      ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp (lift i k)
        (Wkp.iteratedGradient k (g i))] with x h1 h2
  rw [h1]
  exact Finset.sum_congr rfl fun i _ => h2 i

def ofPartialsStep (k : ℕ) (w : W1p (volume : Measure (X n)) Ω 2)
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 (k + 1))
    (previous : {U : Wkp (volume : Measure (X n)) Ω 2 (k + 1) //
      Wkp.firstOrder k U = w ∧
        ⇑(Wkp.iteratedGradient k U) =ᵐ[(volume : Measure (X n)).restrict Ω]
          topField k (fun i => Wkp.lowerOrder k (g i))}) :
    {U : Wkp (volume : Measure (X n)) Ω 2 (k + 2) //
      Wkp.firstOrder (k + 1) U = w ∧
        ⇑(Wkp.iteratedGradient (k + 1) U) =ᵐ[(volume : Measure (X n)).restrict Ω]
          topField (k + 1) g} := by
  let D : Lp (IteratedGradient (X n) (k + 1)) 2 ((volume : Measure (X n)).restrict Ω) :=
    ∑ i, (lift i k).compLp (Wkp.iteratedGradient k (g i))
  have hD : HasWeakFDerivOn volume Ω (Wkp.iteratedGradient k previous.val) D :=
    ofPartials_hasWeakFDerivOn k g (U := previous.val) previous.property.2
  let U : Wkp (volume : Measure (X n)) Ω 2 (k + 2) := Wkp.mk k previous.val D hD
  have hlow : Wkp.lowerOrder (k + 1) U = previous.val :=
    Wkp.lowerOrder_mk k previous.val D hD
  have hgrad : Wkp.iteratedGradient (k + 1) U = D :=
    Wkp.iteratedGradient_mk k previous.val D hD
  refine ⟨U, ?_, ?_⟩
  · rw [Wkp.firstOrder_succ, hlow]
    exact previous.property.1
  · rw [hgrad]
    exact gradientSum_ae k g


def ofPartialsPack : (k : ℕ) → (w : W1p (volume : Measure (X n)) Ω 2) →
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 k) →
    (∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X n)).restrict Ω]
      fun x => W1p.gradient w x i) →
    {U : Wkp (volume : Measure (X n)) Ω 2 (k + 1) // Wkp.firstOrder k U = w ∧
      ⇑(Wkp.iteratedGradient k U) =ᵐ[(volume : Measure (X n)).restrict Ω] topField k g}
  | 0, w, g, h => ⟨(w : Wkp (volume : Measure (X n)) Ω 2 1), rfl, by
      change ⇑(W1p.gradient w) =ᵐ[_] _
      filter_upwards [ae_all_iff.mpr h] with x hx
      simp only [topField, hx]
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (W1p.gradient w x)]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]⟩
  | k + 1, w, g, h =>
    ofPartialsStep k w g (ofPartialsPack k w (fun i => Wkp.lowerOrder k (g i)) h)


def ofPartials (k : ℕ) (w : W1p (volume : Measure (X n)) Ω 2)
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X n)).restrict Ω]
      fun x => W1p.gradient w x i) : Wkp (volume : Measure (X n)) Ω 2 (k + 1) :=
  (ofPartialsPack k w g h).1

theorem firstOrder_ofPartials (k : ℕ) (w : W1p (volume : Measure (X n)) Ω 2)
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X n)).restrict Ω]
      fun x => W1p.gradient w x i) :
    Wkp.firstOrder k (ofPartials k w g h) = w :=
  (ofPartialsPack k w g h).2.1

theorem value_ofPartials (k : ℕ) (w : W1p (volume : Measure (X n)) Ω 2)
    (g : Fin n → Wkp (volume : Measure (X n)) Ω 2 k)
    (h : ∀ i, ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X n)).restrict Ω]
      fun x => W1p.gradient w x i) :
    Wkp.value (k + 1) (ofPartials k w g h) = W1p.value w := by
  rw [← Wkp.value_firstOrder, firstOrder_ofPartials]

end CalderonN.WkpCalculus

module

public import Proof.CalderonN.WeakFixedBallH2
public import Proof.CalderonN.GreenSourceCutoff
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Classical
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

public section

/-! Weak-to-classical identification from the released `ClassicalBallEquation`.
The representative is required to agree with the weak solution on the
open set where the equation is tested. -/
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Distributions ENNReal Matrix.Norms.Elementwise

namespace CalderonN
open TauCeti TauCeti.PDE
variable {n : ℕ} {U V : Opens (X n)}

theorem weak_gradient_eq_gradient_of_ae_value (hUV : U ≤ V)
    (w : W1p (volume : Measure (X n)) V 2)
    {b : X n → ℝ} (hb : ContDiff ℝ ∞ b)
    (hValue : ⇑(W1p.value w) =ᵐ[(volume : Measure (X n)).restrict U] b) :
    ⇑(W1p.gradient w) =ᵐ[(volume : Measure (X n)).restrict U] gradient b := by
  let w' := W1p.restrictL hUV w
  have hw : ⇑(W1p.value w') =ᵐ[(volume : Measure (X n)).restrict U] b :=
    (W1p.value_restrictL_ae hUV w).trans hValue
  have hd := ((W1p.hasWeakFDerivOn w').congr_ae hw).ae_eq_fderiv
    ((hb.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn (U : Set (X n)))
    (fun x _ => hb.differentiable (by simp) x)
  refine (W1p.gradient_restrictL_ae hUV w).symm.trans ?_
  filter_upwards [hd] with x hx
  exact (InnerProductSpace.toDual ℝ (X n)).injective (by
    ext y
    simpa only [gradient, LinearIsometryEquiv.apply_symm_apply,
      InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
        congrArg (fun l : X n →L[ℝ] ℝ => l y) hx)


set_option maxHeartbeats 2500000 in
theorem negativeBallDivergence_eq_of_interior_representation
    (hU : U ≤ fixedBallOpens n) {a : X n → Mat n} (ha : ContDiff ℝ ∞ a) {f b : X n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (v : FixedBallH1Zero n) (hV : ⇑(W1p.value (v : FixedBallH1 n))
       =ᵐ[(volume : Measure (X n)).restrict U] b)
    (F : Lp ℝ 2 ((volume : Measure (X n)).restrict (fixedBallOpens n)))
    (hF : ⇑F =ᵐ[(volume : Measure (X n)).restrict (fixedBallOpens n)] f)
    (h : IsWeakSolutionDirichlet a 0 0 F v) :
    EqOn (negativeBallDivergence a b) f U := by
  let p (i : I n) (x : X n) := ∑ j : I n, a x i j * coordDeriv j b x
  have hGr := weak_gradient_eq_gradient_of_ae_value hU (v : FixedBallH1 n) hb hV
  have hp (i : I n) : ContDiff ℝ ∞ (p i) := by
    apply ContDiff.sum
    intro j _
    let L : Mat n →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    exact (L.contDiff.comp ha).mul ((hb.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hcoord (u : X n → ℝ) (x : X n) (i : I n) : gradient u x i = coordDeriv i u x := by
    rw [coordDeriv, ← inner_gradient_left]
    simp only [axis, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  let D := negativeBallDivergence a b - f
  have hD : Continuous D := ((contDiff_negativeBallDivergence ha hb).sub hf).continuous
  have hTest (φ : X n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
      (hφU : tsupport φ ⊆ U) : ∫ x, φ x • D x = 0 := by
    let ψ : 𝓓(fixedBallOpens n,ℝ) := ⟨φ,hφ,hφc,hφU.trans hU⟩
    have hEn := weakFixedBall_test h ψ
    change (∫ x in (fixedBallOpens n : Set (X n)), matrixBilinearForm (a x) (gradient φ x)
      (W1p.gradient (v : FixedBallH1 n) x)) =
        ∫ x in (fixedBallOpens n : Set (X n)), F x * φ x at hEn
    have hout (x : X n) (hx : x ∉ (U : Set (X n))) : φ x = 0 ∧ gradient φ x = 0 :=
      ⟨image_eq_zero_of_notMem_tsupport (fun hz => hx (hφU hz)),
        gradient_of_notMem_tsupport (fun hz => hx (hφU hz))⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (fixedBallOpens n).isOpen.measurableSet hU
        (fun x hx => by rw [(hout x hx.2).2]; exact (matrixBilinearForm (a x)).map_zero₂ _),
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (fixedBallOpens n).isOpen.measurableSet hU
        (fun x hx => by rw [(hout x hx.2).1, mul_zero])] at hEn
    have hL : (∫ x in (U : Set (X n)), matrixBilinearForm (a x) (gradient φ x)
        (W1p.gradient (v : FixedBallH1 n) x)) =
        ∫ x, ∑ i : I n, p i x * coordDeriv i φ x := by
      have hz (x : X n) (hx : x ∉ (U : Set (X n))) : ∀ i, coordDeriv i φ x = 0 :=
        fun i => by rw [← hcoord, (hout x hx).2]; rfl
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (U : Set (X n))) (f := fun x => ∑ i : I n, p i x * coordDeriv i φ x)
        (fun x hx => by simp [hz x hx])]
      refine integral_congr_ae ?_
      filter_upwards [hGr] with x hg
      simp only [hg, matrixBilinearForm_apply, dotProduct, Matrix.mulVec, hcoord, p]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hR : (∫ x in (U : Set (X n)), F x * φ x) = ∫ x, φ x * f x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := (U : Set (X n))) (f := fun x => φ x * f x)
        (fun x hx => by rw [(hout x hx).1, zero_mul])]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hU hF] with x hx
      rw [hx, mul_comm]
    rw [hL,hR] at hEn
    have hInt₁ (i : I n) : Integrable (fun x => p i x * coordDeriv i φ x) := by
      have hC : Continuous (coordDeriv i φ) :=
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
      exact ((hp i).continuous.mul hC).integrable_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ (axis i)).mul_left)
    have hInt₂ (i : I n) : Integrable (fun x => φ x * coordDeriv i (p i) x) := by
      have hC : Continuous (coordDeriv i (p i)) :=
        ((hp i).continuous_fderiv (by simp)).clm_apply continuous_const
      exact (hφ.continuous.mul hC).integrable_of_hasCompactSupport hφc.mul_right
    have hTwo : (∫ x, ∑ i : I n, p i x * coordDeriv i φ x) =
        ∫ x, φ x * negativeBallDivergence a b x := by
      rw [integral_finsetSum _ (fun i _ => hInt₁ i)]
      change (∑ i, ∫ x, p i x * coordDeriv i φ x) =
        ∫ x, φ x * (-(∑ i, coordDeriv i (p i) x))
      simp only [mul_neg, Finset.mul_sum, integral_neg]
      rw [integral_finsetSum _ (fun i _ => hInt₂ i), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        (integral_mul_coordDeriv_eq_neg isOpen_univ (hp i).contDiffOn hφ hφc (subset_univ _) i).trans
          (congrArg Neg.neg (integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)))
    have hInt' (g : X n → ℝ) (hg : Continuous g) : Integrable (fun x => φ x * g x) :=
      (hφ.continuous.mul hg).integrable_of_hasCompactSupport hφc.mul_right
    rw [hTwo] at hEn
    simp only [D, Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub (hInt' _ (contDiff_negativeBallDivergence ha hb).continuous)
      (hInt' _ hf.continuous), hEn, sub_self]
  have hAE : D =ᵐ[(volume : Measure (X n)).restrict U] (fun _ => (0 : ℝ)) := by
    apply (ae_restrict_iff' U.isOpen.measurableSet).mpr
    exact U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hD.locallyIntegrable.locallyIntegrableOn U) hTest
  have hZ := Measure.eqOn_open_of_ae_eq hAE U.isOpen hD.continuousOn continuousOn_const
  exact fun x hx => sub_eq_zero.mp (hZ hx)

end CalderonN

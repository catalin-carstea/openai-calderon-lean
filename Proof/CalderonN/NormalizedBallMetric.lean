module

public import Proof.CalderonN.NormalBallChart
public import Proof.CalderonN.MetricPullback
import Proof.CalderonN.NormalEndpointJets

import Proof.CalderonN.MetricPair
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Adapted from `NormalizedBallMetric` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Metric
open scoped ContDiff Matrix

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The normal chart derivative with its explicit scalar radius removed. -/
@[expose] def normalizedBallDerivative (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim)) (y : (X dim)) (r : ℝ) (z : (X dim)) :
    (X dim) →L[ℝ] (X dim) :=
  (fderiv ℝ (fun v => E (y,v)) (r • frameVector e y z)).comp (frameVectorL (e y))

/-- The first metric on the fixed ball with the scaling factor removed.
It is defined even at zero radius. -/
@[expose] def normalizedBallMetric (g : (MetricField dim)) (E : (X dim) × (X dim) → (X dim)) (e : (Frame dim))
    (y : (X dim)) (r : ℝ) (z : (X dim)) : (Mat dim) :=
  let M := coordinateMatrix (normalizedBallDerivative E e y r z)
  Mᵀ * g (normalBallChartMap E e y r z) * M

theorem pullbackMetric_normalBallChartMap {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (g : (MetricField dim)) (e : (Frame dim)) (y : (X dim)) (r : ℝ) :
    pullbackMetric g (normalBallChartMap E e y r) = r^2 • normalizedBallMetric g E e y r := by
  funext z
  have he : coordinateJacobian (normalBallChartMap E e y r) z =
      r • coordinateMatrix (normalizedBallDerivative E e y r z) := by
    unfold coordinateJacobian
    rw [normalBallChartMap_deriv hE]
    ext i j
    simp only [normalizedBallDerivative,coordinateMatrix_apply,ContinuousLinearMap.comp_apply,
      smul_apply,map_smul,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
  change _ = r^2 • normalizedBallMetric g E e y r z
  simp only [pullbackMetric,he,normalizedBallMetric,Matrix.transpose_smul,Matrix.smul_mul,
    Matrix.mul_smul,smul_smul,pow_two]

private theorem contDiff_frameVector_family {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {e : T → (I dim) → (X dim)} (he : ∀ i, ContDiff ℝ ∞ (fun t => e t i))
    {z : T → (X dim)} (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ (fun t => ∑ i : (I dim), z t i • e t i) :=
  ContDiff.sum (fun i _ => (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz).smul (he i)))

/-- The normalized derivative matrix in the original dilation and signed
radius parameters. -/
theorem contDiff_normalizedBallDerivative_family_entry
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {e : ℝ → (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.1 p.2 i))
    (a b : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (ℝ × (X dim))) =>
      coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2) a b) := by
  let T := ℝ × ((X dim) × (ℝ × (X dim)))
  let base (q : T) := (q.1,q.2.1)
  let input (q : T) : ℝ × ((X dim) × (X dim)) :=
    (q.1,(q.2.1,q.2.2.1 • frameVector (e q.1) q.2.1 q.2.2.2))
  let A (q : T) := coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2)
  have hbase : ContDiff ℝ ∞ base := contDiff_fst.prodMk contDiff_snd.fst
  have hv (w : T → (X dim)) (hw : ContDiff ℝ ∞ w) :
      ContDiff ℝ ∞ (fun q : T => frameVector (e q.1) q.2.1 (w q)) :=
    contDiff_frameVector_family (fun i => (he i).comp hbase) hw
  have hinput : ContDiff ℝ ∞ input :=
    contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.fst.smul
      (hv _ contDiff_snd.snd.snd)))
  have heq (q : T) : A q a b =
      fderiv ℝ (fun p : ℝ × ((X dim) × (X dim)) => E p.1 p.2) (input q)
        (0,(0,frameVector (e q.1) q.2.1 (axis b))) a := by
    let z := (q.2.1,q.2.2.1 • frameVector (e q.1) q.2.1 q.2.2.2)
    have hD := ((hE.differentiable (by simp) (q.1,z)).hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right q.1 z)).fderiv
    have hEpart : fderiv ℝ (E q.1) z =
        (fderiv ℝ (fun p : ℝ × ((X dim) × (X dim)) => E p.1 p.2) (q.1,z)).comp
          (ContinuousLinearMap.inr ℝ ℝ ((X dim) × (X dim))) := hD
    have hvPart :
        fderiv ℝ (fun v => E q.1 (q.2.1,v)) z.2 =
          (fderiv ℝ (E q.1) z).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim)) := by
      exact (((hE.comp (contDiff_const.prodMk contDiff_id)).differentiable
        (by simp) z).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right q.2.1 z.2)).fderiv
    change A q a b = _
    rw [show A q a b = fderiv ℝ (fun v => E q.1 (q.2.1,v)) z.2
        (0 + frameVector (e q.1) q.2.1 (axis b)) a from by
      simp only [A,coordinateMatrix_apply,normalizedBallDerivative,
        ContinuousLinearMap.comp_apply,zero_add,z,frameVectorL_apply_frame]]
    rw [hvPart,hEpart]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,zero_add]
    rfl
  change ContDiff ℝ ∞ (fun q : T => A q a b)
  simp_rw [heq]
  have hJ := (hE.fderiv_right (m := ∞) (by simp)).comp hinput
  have hvec : ContDiff ℝ ∞ (fun q : T => ((0 : ℝ),((0 : (X dim)),frameVector (e q.1) q.2.1 (axis b)))) :=
    contDiff_const.prodMk (contDiff_const.prodMk (hv _ contDiff_const))
  exact (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp (hJ.clm_apply hvec)

/-- The normalized pullback has joint smooth coefficient entries in the
center, original dilation, fixed-ball variable, and signed radius. -/
theorem contDiff_normalizedBallMetric_family_entry
    {E : ℝ → (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    {e : ℝ → (Frame dim)} (he : ∀ i, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => e p.1 p.2 i))
    {g : ℝ → (MetricField dim)} (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (ℝ × (X dim))) =>
      normalizedBallMetric (g q.1) (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2 i j) := by
  let T := ℝ × ((X dim) × (ℝ × (X dim)))
  let base (q : T) := (q.1,q.2.1)
  let input (q : T) : ℝ × ((X dim) × (X dim)) :=
    (q.1,(q.2.1,q.2.2.1 • frameVector (e q.1) q.2.1 q.2.2.2))
  let A (q : T) := coordinateMatrix (normalizedBallDerivative (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2)
  have hbase : ContDiff ℝ ∞ base := contDiff_fst.prodMk contDiff_snd.fst
  have hv (w : T → (X dim)) (hw : ContDiff ℝ ∞ w) :
      ContDiff ℝ ∞ (fun q : T => frameVector (e q.1) q.2.1 (w q)) :=
    contDiff_frameVector_family (fun i => (he i).comp hbase) hw
  have hinput : ContDiff ℝ ∞ input :=
    contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.fst.smul
      (hv _ contDiff_snd.snd.snd)))
  have hmetric (a b : (I dim)) : ContDiff ℝ ∞ (fun q : T =>
      g q.1 (normalBallChartMap (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2) a b) :=
    (hg a b).comp (contDiff_fst.prodMk (hE.comp hinput))
  have hA (a b : (I dim)) : ContDiff ℝ ∞ (fun q : T => A q a b) :=
    contDiff_normalizedBallDerivative_family_entry hE he a b
  change ContDiff ℝ ∞ (fun q : T =>
    ((A q)ᵀ * g q.1 (normalBallChartMap (E q.1) (e q.1) q.2.1 q.2.2.1 q.2.2.2) * A q) i j)
  simp only [Matrix.mul_apply,Matrix.transpose_apply]
  exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (hA b i).mul (hmetric b a)).mul (hA a j)

theorem normalizedBallDerivative_zero
    {Y Ω : Set (X dim)} {γ : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {ρ : (X dim) → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ) {y : (X dim)} (hy : y ∈ Y)
    {e : (Frame dim)} (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    (z : (X dim)) : normalizedBallDerivative E e y 0 z = frameVectorL (e y) := by
  apply ContinuousLinearMap.ext
  intro w
  have hSlice := ((hE.differentiable (by simp) (y,(0 : X dim))).hasFDerivAt.comp 0
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) y (0 : X dim))).fderiv
  simp only [normalizedBallDerivative, ContinuousLinearMap.comp_apply, frameVectorL_apply_frame, zero_smul]
  change fderiv ℝ (fun v => E (y,v)) 0 = _ at hSlice
  rw [hSlice]
  exact hN.vertical_zero hy e he _

/-- The limiting pulled-back metric is the Euclidean scalar metric for
a conformal reference normal ball. -/
theorem normalizedBallMetric_zero_of_conformal
    {Y Ω : Set (X dim)} {γ g : (MetricField dim)} {E : (X dim) × (X dim) → (X dim)} {ρ : (X dim) → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ) {y : (X dim)} (hy : y ∈ Y)
    {e : (Frame dim)} (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {c : ℝ} (hc : 0 < c) (hγ : γ y = c • g y) (z : (X dim)) :
    normalizedBallMetric g E e y 0 z = c⁻¹ • (1 : (Mat dim)) := by
  have hcol (i : (I dim)) : frameVector e y (axis i) = e y i := by
    simp [frameVector,axis,PiLp.single_apply,ite_smul]
  have hA (i j : (I dim)) : coordinateMatrix (normalizedBallDerivative E e y 0 z) i j = e y j i := by
    rw [coordinateMatrix_apply,normalizedBallDerivative_zero hE hN hy he,frameVectorL_apply_frame]
    exact congrArg (fun w : (X dim) => w i) (hcol j)
  ext i j
  simp only [normalizedBallMetric,normalBallChartMap,zero_smul,hN.exp_zero hy,
    Matrix.mul_apply,Matrix.transpose_apply,hA,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  have hEntry : (∑ a : (I dim), ∑ b : (I dim), e y i b * g y b a * e y j a) =
      metricPair g y (e y i) (e y j) := by
    unfold metricPair
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp_rw [Finset.sum_mul]
  rw [hEntry]
  have hp := he i j
  have hp' : metricPair γ y (e y i) (e y j) = c * metricPair g y (e y i) (e y j) := by
    unfold metricPair
    rw [hγ]
    simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  rw [hp'] at hp
  rw [← hp,← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

end CalderonN

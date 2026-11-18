import Proof.Archive.MetricFrameOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 30
open scoped ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.NormalCoordinatesFrame

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma contDiffAt_metricPair (M : P → R3 →L[ℝ] R3) (v w : P → R3) (x : P)
    (hM : ContDiffAt ℝ ∞ M x) (hv : ContDiffAt ℝ ∞ v x) (hw : ContDiffAt ℝ ∞ w x) :
    ContDiffAt ℝ ∞ (fun y => metricPair (M y) (v y) (w y)) x :=
  (hM.clm_apply hv).inner ℝ hw

lemma contDiffAt_gramSecond (M : P → R3 →L[ℝ] R3) (x : P) (hM : ContDiffAt ℝ ∞ M x)
    (hp : ∀ v : R3,v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiffAt ℝ ∞ (fun y => gramSecond (M y)) x := by
  have hnum := contDiffAt_metricPair M (fun _ => coordinateVector 1) (fun _ => coordinateVector 0)
    x hM contDiffAt_const contDiffAt_const
  have hden := contDiffAt_metricPair M (fun _ => coordinateVector 0) (fun _ => coordinateVector 0)
    x hM contDiffAt_const contDiffAt_const
  exact contDiffAt_const.sub ((hnum.div hden (hp _ coordinateVector_zero_ne).ne').smul contDiffAt_const)

lemma contDiffAt_gramThird (M : P → R3 →L[ℝ] R3) (x : P) (hM : ContDiffAt ℝ ∞ M x)
    (hp : ∀ v : R3,v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiffAt ℝ ∞ (fun y => gramThird (M y)) x := by
  have h1 := contDiffAt_gramSecond M x hM hp
  have hnum0 := contDiffAt_metricPair M (fun _ => coordinateVector 2) (fun _ => coordinateVector 0)
    x hM contDiffAt_const contDiffAt_const
  have hden0 := contDiffAt_metricPair M (fun _ => coordinateVector 0) (fun _ => coordinateVector 0)
    x hM contDiffAt_const contDiffAt_const
  have hnum1 := contDiffAt_metricPair M (fun _ => coordinateVector 2) (fun y => gramSecond (M y))
    x hM contDiffAt_const h1
  have hden1 := contDiffAt_metricPair M (fun y => gramSecond (M y)) (fun y => gramSecond (M y))
    x hM h1 h1
  exact (contDiffAt_const.sub ((hnum0.div hden0 (hp _ coordinateVector_zero_ne).ne').smul contDiffAt_const)).sub
    ((hnum1.div hden1 (hp _ (gramSecond_ne_zero (M x))).ne').smul h1)

lemma contDiffAt_metricNormalize (M : P → R3 →L[ℝ] R3) (v : P → R3) (x : P)
    (hM : ContDiffAt ℝ ∞ M x) (hv : ContDiffAt ℝ ∞ v x)
    (hpos : 0 < metricPair (M x) (v x) (v x)) :
    ContDiffAt ℝ ∞ (fun y => metricNormalize (M y) (v y)) x := by
  have hs := (contDiffAt_metricPair M v v x hM hv hv).sqrt hpos.ne'
  exact (hs.inv (Real.sqrt_pos.mpr hpos).ne').smul hv

lemma contDiffAt_metricGramFrame (M : P → R3 →L[ℝ] R3) (x : P) (hM : ContDiffAt ℝ ∞ M x)
    (hp : ∀ v : R3,v ≠ 0 → 0 < metricPair (M x) v v) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => metricGramFrame (M y) i) x := by
  fin_cases i
  · simpa [metricGramFrame] using contDiffAt_metricNormalize M (fun _ => coordinateVector 0)
      x hM contDiffAt_const (hp _ coordinateVector_zero_ne)
  · simpa [metricGramFrame] using contDiffAt_metricNormalize M (fun y => gramSecond (M y))
      x hM (contDiffAt_gramSecond M x hM hp) (hp _ (gramSecond_ne_zero (M x)))
  · simpa [metricGramFrame] using contDiffAt_metricNormalize M (fun y => gramThird (M y))
      x hM (contDiffAt_gramThird M x hM hp) (hp _ (gramThird_ne_zero (M x)))

lemma contDiffAt_metricGramFrameOperator (M : P → R3 →L[ℝ] R3) (x : P)
    (hM : ContDiffAt ℝ ∞ M x)
    (hp : ∀ v : R3,v ≠ 0 → 0 < metricPair (M x) v v) :
    ContDiffAt ℝ ∞ (fun y => frameOperator (metricGramFrame (M y))) x := by
  apply ContDiffAt.sum
  intro i _
  exact contDiffAt_const.smulRight (contDiffAt_metricGramFrame M x hM hp i)

end OAI.AnisotropicCalderon.NormalCoordinatesFrame

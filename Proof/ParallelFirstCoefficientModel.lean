import Proof.ParallelFirstMetricCoefficient
import Proof.NormalizedDensityCovariantCenter

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def parallelFirstCoefficientCovector (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X) (t : ℝ) : X →L[ℝ] ℝ :=
  (firstDensityLogDifferential g g₁ (y+t • a)).comp (affineParallelFrame g y a L t)

def parallelFirstCoefficientModel (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X) (p : ℝ × X) : Mat :=
  parallelFirstCoefficientCovector g g₁ y a L p.1 p.2 • (1:Mat)

lemma contDiffAt_parallelFirstCoefficientModel (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X) (p : ℝ × X)
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) (y+p.1 • a)) :
    ContDiffAt ℝ ∞ (parallelFirstCoefficientModel g g₁ y a L) p := by
  have hCenter : ContDiff ℝ ∞ (fun q : ℝ × X => y+q.1 • a) := contDiff_const.add (contDiff_fst.smul contDiff_const)
  have hFrame : ContDiff ℝ ∞ (fun q : ℝ × X => affineParallelFrame g y a L q.1) :=
    (contDiff_affineParallelFrame g y a L).comp contDiff_fst
  have hOp := (hEll.comp p hCenter.contDiffAt).clm_comp hFrame.contDiffAt
  exact (hOp.clm_apply contDiffAt_snd).smul contDiffAt_const

lemma parallelFirstCoefficientModel_remainder (g g₁ : MetricField) (E : X × X → X)
    (y a : X) (r : ℝ) (L : X →L[ℝ] X) (p : ℝ × X) (i j : I) :
    parallelNormalizedFirstCoefficientRemainder g g₁ E y a r L p i j =
      parallelNormalizedFirstCoefficient g g₁ E y a r L p i j-(1:Mat) i j-
        r*parallelFirstCoefficientModel g g₁ y a L p i j := by
  simp only [parallelNormalizedFirstCoefficientRemainder,parallelFirstCoefficientModel,
    parallelFirstCoefficientCovector,parallelFrameInput,ContinuousLinearMap.comp_apply,
    Matrix.smul_apply,smul_eq_mul,map_smul]
  ring

/-- The actual first-model covector has precisely the already controlled
    covariant center derivative; the radius is frozen in this analytic family. -/
theorem hasDerivAt_parallelFirstCoefficientCovector (g g₁ : MetricField) (y a : X) (L : X →L[ℝ] X)
    (hEll : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) y) :
    HasDerivAt (parallelFirstCoefficientCovector g g₁ y a L)
      ((firstDensityLogCovariantDerivative g g₁ y a).comp L) 0 := by
  have hCenter : HasDerivAt (fun t : ℝ => y+t • a) a 0 := by
    have hb := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const a)
    change HasDerivAt (fun t : ℝ => y+t • a) _ 0 at hb
    simpa only [one_smul,zero_add] using hb
  have hAt : ContDiffAt ℝ ∞ (firstDensityLogDifferential g g₁) (y+(0:ℝ) • a) := by simpa using hEll
  have hFirst := (hAt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 hCenter
  have hFrame := hasDerivAt_affineParallelFrame g y a L 0
  have hAll := hFirst.clm_comp hFrame
  change HasDerivAt (parallelFirstCoefficientCovector g g₁ y a L) _ 0 at hAll
  convert hAll using 1
  ext z
  simp only [Function.comp_def,firstDensityLogCovariantDerivative,_root_.sub_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,affineParallelFrame_zero,zero_smul,add_zero,_root_.neg_apply,map_neg]
  ring

end ShrinkingSpheres

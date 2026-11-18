import Proof.UniformParallelFrameMetricBounds
import Proof.QuadraticMatrixCoefficientTransfer
import Proof.UniformQuadraticReferenceCoefficient
import Proof.FirstMetricNormalDensity
import Proof.NormalDiskInterior

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Matrix.Norms.Operator
namespace ShrinkingSpheres

def parallelReferenceCoefficientCenterBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (Z : ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*18*(4*K^2)^2*parallelMetricCenterBudget hm K M K Z

def parallelReferenceCoefficientMixedBudget {m : ℕ} (hm : 5 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (Z : ℝ) : ℝ :=
  metricDensityBudget (4*K^2)*(486*(4*K^2)^3*parallelMetricCenterBudget hm K M K Z*
    parallelMetricAngularBudget hm K M K Z+18*(4*K^2)^2*parallelMetricMixedBudget hm K M K Z)

/-- Actual uniform quadratic center C1 control of the reference divergence
    coefficient on a local parallel-frame family, for every admissible radius. -/
theorem uniform_parallel_reference_coefficient_center {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ a : X,∀ z ∈ Metric.closedBall (0:X) Z,
      ∀ b : X,∀ i j,
      let G := parallelFrameNormalMetric d.γ d.expMap y a (d.radius y) (frameVectorLinear d.frame y)
      |fderiv ℝ (fun p => matrixFamilyCoefficient G p i j) (0,z) (1,0)| ≤
        parallelReferenceCoefficientCenterBudget hm K M Z*(d.radius y)^2*‖a‖ ∧
      |fderiv ℝ (fderiv ℝ (fun p => matrixFamilyCoefficient G p i j)) (0,z) (0,b) (1,0)| ≤
        parallelReferenceCoefficientMixedBudget hm K M Z*(d.radius y)^2*‖a‖*‖b‖ := by
  obtain ⟨ηG,hηG,hGeometry⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ (by omega) K ρ c₀ M Cj hK hρ Z hZ
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic (Y:=Y) hΩ (by omega)
    K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨min ηG (min ηE 1),lt_min hηG (lt_min hηE zero_lt_one),?_⟩
  intro floor hf ε hε hSmall d hd y hy a z hz b i j
  dsimp only
  let r := d.radius y
  let L := frameVectorLinear d.frame y
  let G := parallelFrameNormalMetric d.γ d.expMap y a r L
  let KP := 4*K^2
  let D := metricDensityBudget KP
  let A := parallelMetricCenterBudget hm K M K Z
  let B := parallelMetricAngularBudget hm K M K Z
  let C := parallelMetricMixedBudget hm K M K Z
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKP : 0 < KP := by dsimp [KP];positivity
  have hD : 0 ≤ D := by dsimp [D,metricDensityBudget];positivity
  have hEnvelope := backgroundExpJetEnvelope_ge_one hm hKpos.le M
  have hQ : 0 ≤ backgroundJointNormalMetricJetBudget hm K M := by dsimp [backgroundJointNormalMetricJetBudget];positivity
  have hA : 0 ≤ A := by dsimp [A,parallelMetricCenterBudget];positivity
  have hB : 0 ≤ B := by dsimp [B,parallelMetricAngularBudget];positivity
  have hC : 0 ≤ C := by dsimp [C,parallelMetricMixedBudget];positivity
  have hCenter := hd.2.1.center_mem hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y hCenter
  have hL : ‖L‖ ≤ K := hd.1.1.norm_frameVectorLinear_le hK hCenter d.frame hFrame
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (radius_bounds r (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : r ≤ 1 := hrε.trans (hSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hzNorm : ‖z‖ ≤ Z := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hw := frameVector_mem_disk d.γ d.frame y z Z hFrame hz
  have hPack := hGeometry floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy (L z) hw
  have hRadius : ContinuousOn (fun x => max ρ (d.radius x)) Y := by
    intro x hx
    have hConst : ContinuousAt (fun _ : X => ρ) x := continuousAt_const
    have hMax : ContinuousAt (fun t : X => max ρ (d.radius t)) x :=
      hConst.max ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hx)).continuousAt)
    exact hMax.continuousWithinAt
  have hStrict : metricPair d.γ y (r • L z) (r • L z) < (max ρ r)^2 :=
    metricPair_lt_of_mem_interior_disk d.γ y (r • L z) (max ρ r)
      (hρ.trans_le (le_max_left _ _)) hPack.1.1
  have hJets (k l : I) := hd.1.parallel_frame_metric_jet_bounds hY hΩ hKpos hm hd.2.1 hRadius hy a r hr.le L
    K Z hKpos.le hZ hL z hzNorm hStrict hPack.1.2 b k l
  have hEll : Elliptic (Metric.closedBall (0:X) Z) KP
      (framedNormalMetric d.γ d.frame d.expMap y r) :=
    hElliptic floor hf ε hε (hSmall.trans ((min_le_right _ _).trans (min_le_left _ _))) d hd y hy d.γ (by simp)
  have hAt : G (0,z) = framedNormalMetric d.γ d.frame d.expMap y r z :=
    parallelFrameNormalMetric_zero d.γ d.expMap y a r d.frame z
  have hPos : 0 < (G (0,z)).det := by rw [hAt];exact (hEll.posDef hKP hz).det_pos
  obtain ⟨S,hS,hHere,hGS,hDet⟩ := hd.2.1.exists_parallel_frame_metric_domain hΩ hd.1.1 hy a r L z hStrict.le hPos
  have hInv (k l : I) : |(G (0,z))⁻¹ k l| ≤ KP := by rw [hAt];exact hEll.inverse_entry_bound hKP hz k l
  have hMu : matrixFamilyDensity G (0,z) ≤ D := by
    change Real.sqrt (G (0,z)).det ≤ D
    rw [hAt]
    exact hEll.density_upper_bound hKP hz
  have hProduce := matrixFamily_coefficient_quadratic_mixed_bound hS G hGS hDet z hHere b r KP D (A*‖a‖) B (C*‖a‖)
    hr.le hr1 hKP.le hD (by positivity) hB (by positivity) hInv hMu
    (fun k l => (hJets k l).1.trans_eq (by dsimp only [A];ring))
    (fun k l => (hJets k l).2.1)
    (fun k l => (hJets k l).2.2.trans_eq (by dsimp only [C];ring)) i j
  exact ⟨hProduce.1.trans_eq (by dsimp only [parallelReferenceCoefficientCenterBudget,D,KP,A];ring),
    hProduce.2.trans_eq (by dsimp only [parallelReferenceCoefficientMixedBudget,D,KP,A,B,C];ring)⟩

end ShrinkingSpheres

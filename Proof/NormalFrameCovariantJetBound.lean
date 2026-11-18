import Proof.NormalFrameParallelDerivativeScaling
import Proof.LogRadiusDirectionalBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

/-- Any differentiable normal-frame family with uniform unit parallel and
relative-radius jets has a covariant actual-profile jet bound. Frame jets
cancel exactly; no quantitative frame-derivative hypothesis is needed. -/
theorem norm_normalFrame_covariant_jet_le_of_unit
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hK : 1 ≤ K) (hf : 1 ≤ floor) {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : NormalFrameParameter → E)
    (hHDiff : DifferentiableAt ℝ H (y,(d.radius y,frameVectorLinear d.frame y)))
    (CP CR : ℝ) (hCP : 0 ≤ CP) (hCR : 0 ≤ CR)
    (hParallelUnit : ∀ a : X,‖a‖ ≤ 1 →
      ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖ ≤ CP)
    (hRadius : ‖deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ ≤ CR) :
    ∀ a : X,‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
      ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
        deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤
      (CP+3*K*CR)*beta d.γ d.radius y*‖a‖ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCenter0 := hd.2.1.center_mem hy
  have hFrameSmooth : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Ω := hd.1.2.2.2.2.2.2.1
  have hFrameAll : ∀ x ∈ Ω,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i = j then 1 else 0 := hd.1.2.2.2.2.2.2.2
  have hFrameAt (i : I) := (hFrameSmooth i).contDiffAt (hΩ.mem_nhds hCenter0)
  have hFrameDiff (i : I) := (hFrameAt i).differentiableAt (by simp)
  have hF := (contDiffAt_frameVectorLinear d.frame y hFrameAt).differentiableAt (by simp)
  have hrDiff := ((hd.2.2.2.2.1.1).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hBeta : 1 ≤ beta d.γ d.radius y := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  intro a
  have hParallelN := norm_deriv_normalFrame_parallel_le_of_unit d.γ d.frame d.radius y H hHDiff CP hParallelUnit a
  have hSkew := frameConnection_skew hΩ hd.1.1 hKpos d.frame hFrameSmooth hFrameAll hCenter0 a
  have hSplit := deriv_normalFrame_family_covariant_split d.γ d.frame d.radius y a H hrDiff hr0 hF hFrameDiff
    (hFrameAll y hCenter0) hSkew hHDiff
  change ‖deriv (fun t => H (normalFrameActualCurve d.frame d.radius y a t)) 0-
    ∑ i,∑ j,((1/2:ℝ)*frameConnectionCoefficient d.γ d.frame y a i j) •
      deriv (fun t => H (normalFrameRotationCurve d.frame d.radius y i j t)) 0‖ ≤ _
  rw [hSplit]
  have hLog := hd.1.1.logRadius_direction_bound hK d.frame d.radius hCenter0 (hFrameAll y hCenter0) a
  have hBeta0 : 0 ≤ beta d.γ d.radius y := zero_le_one.trans hBeta
  have hPWeight : CP*‖a‖ ≤ CP*beta d.γ d.radius y*‖a‖ := by
    have hMul := mul_le_mul_of_nonneg_left hBeta (by positivity : 0 ≤ CP*‖a‖)
    simpa only [mul_one] using hMul.trans_eq (by ring)
  calc
    _ ≤ ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖+
        ‖(fderiv ℝ (fun x => Real.log (d.radius x)) y a) •
          deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ := norm_add_le _ _
    _ = ‖deriv (fun t => H (normalFrameParallelCurve d.γ d.frame d.radius y a t)) 0‖+
        |fderiv ℝ (fun x => Real.log (d.radius x)) y a| *
          ‖deriv (fun t => H (normalFrameRadiusCurve d.frame d.radius y t)) 0‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ CP*‖a‖+(3*K*beta d.γ d.radius y*‖a‖)*(CR) :=
      add_le_add hParallelN (mul_le_mul hLog hRadius (norm_nonneg _) (by positivity))
    _ ≤ CP*beta d.γ d.radius y*‖a‖+(3*K*beta d.γ d.radius y*‖a‖)*(CR) :=
      add_le_add hPWeight le_rfl
    _ = (CP+3*K*CR)*beta d.γ d.radius y*‖a‖ := by ring


end ShrinkingSpheres

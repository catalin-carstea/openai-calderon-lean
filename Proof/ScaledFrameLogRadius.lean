import Proof.FrameLogRadiusComponentBound
import Proof.FrameCovectorDerivative
import Proof.MovingFrameSecond
import Proof.FirstAdjointCorrectionSobolev
import Proof.HessianDifferential
import Proof.HessianCoordinateBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

def scaledFrameLogRadius (r : X → ℝ) (e : Frame) (j : I) : X → ℝ :=
  fun y => r y*fderiv ℝ (fun x => Real.log (r x)) y (e y j)

def scaledFrameLogRadiusCovariant (g : MetricField) (r : X → ℝ) (e : Frame)
    (y a : X) (j : I) : ℝ :=
  fderiv ℝ (scaledFrameLogRadius r e j) y a-
    ∑ k : I,frameConnectionCoefficient g e y a j k*scaledFrameLogRadius r e k y

theorem contDiffOn_scaledFrameLogRadius {Y : Set X} (hY : IsOpen Y)
    {r : X → ℝ} (hR : ContDiffOn ℝ ∞ r Y) (hPos : ∀ y ∈ Y,r y ≠ 0)
    {e : Frame} (he : ∀ j,ContDiffOn ℝ ∞ (fun y => e y j) Y) (j : I) :
    ContDiffOn ℝ ∞ (scaledFrameLogRadius r e j) Y := by
  have hLog := hR.log hPos
  have hD := hLog.fderiv_of_isOpen (m:=∞) hY (by simp)
  exact hR.mul (hD.clm_apply (he j))

/-- The connection cancels all actual derivatives of the chosen frame.
    The remaining coefficient is a radius-weighted logarithmic Hessian. -/
theorem scaledFrameLogRadiusCovariant_eq {Y : Set X} (hY : IsOpen Y)
    (g : MetricField) {r : X → ℝ} (hR : ContDiffOn ℝ ∞ r Y)
    {e : Frame} (he : ∀ j,ContDiffOn ℝ ∞ (fun y => e y j) Y)
    {y : X} (hy : y ∈ Y) (hPos : 0 < r y)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0)
    (a : X) (j : I) :
    scaledFrameLogRadiusCovariant g r e y a j =
      r y*(hessianBilinear g (fun x => Real.log (r x)) y a (e y j)+
        fderiv ℝ (fun x => Real.log (r x)) y a*fderiv ℝ (fun x => Real.log (r x)) y (e y j)) := by
  let f := fun x => Real.log (r x)
  have hRad := (hR.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hLog : ContDiffAt ℝ ∞ f y := (hR.contDiffAt (hY.mem_nhds hy)).log hPos.ne'
  have hDLog := (hLog.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hEj := ((he j).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  let ell := fun x => fderiv ℝ f x (e x j)
  have hEll : DifferentiableAt ℝ ell y := hDLog.clm_apply hEj
  have hProd := hRad.hasFDerivAt.mul hEll.hasFDerivAt
  have hActual : fderiv ℝ (scaledFrameLogRadius r e j) y a=
      r y*fderiv ℝ ell y a+ell y*fderiv ℝ r y a := by
    have hh := DFunLike.congr_fun hProd.fderiv a
    change fderiv ℝ (scaledFrameLogRadius r e j) y a=_ at hh
    simpa only [_root_.add_apply,_root_.smul_apply,smul_eq_mul,mul_comm] using hh
  have hCov := frame_covector_derivative_eq_hessian g e f y a j hDLog hEj hFrame
  have hConnection : (∑ k : I,frameConnectionCoefficient g e y a j k*scaledFrameLogRadius r e k y)=
      r y*(∑ k : I,frameConnectionCoefficient g e y a j k*fderiv ℝ f y (e y k)) := by
    simp only [scaledFrameLogRadius,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hRadius : fderiv ℝ r y a=r y*fderiv ℝ f y a := by
    rw [logRadius_derivative r y a hRad hPos.ne',← mul_assoc,mul_inv_cancel₀ hPos.ne',one_mul]
  unfold scaledFrameLogRadiusCovariant
  rw [hActual,hConnection,hRadius]
  calc
    _ = r y*(fderiv ℝ ell y a-∑ k : I,frameConnectionCoefficient g e y a j k*fderiv ℝ f y (e y k))+
        r y*(fderiv ℝ f y a*fderiv ℝ f y (e y j)) := by change _ = _;dsimp only [ell];ring
    _ = _ := by rw [hCov];ring


theorem frame_logRadius_abs_le_beta (g : MetricField) (e : Frame) (r : X → ℝ) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j) = if i=j then 1 else 0) (i : I) :
    |fderiv ℝ (fun x => Real.log (r x)) y (e y i)| ≤ beta g r y := by
  exact frame_logRadius_component_bound g e r y hFrame i


/-- In the frame directions used by the principal trace, the whole actual
    coefficient derivative is uniformly epsilon-small. -/
theorem Admissible.scaledFrameLogRadiusCovariant_frame_bound {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (i j : I) :
    |scaledFrameLogRadiusCovariant d.γ d.radius d.frame y (d.frame y i) j| ≤
      (|Cj 2|+1)*ε := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Y :=
    fun j => (hd.1.2.2.2.2.2.2.1 j).mono hSub
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hP := hd.2.2.2.2.1
  have hr := (hP.2 y hy).1
  let f := fun x => Real.log (d.radius x)
  let b := beta d.γ d.radius y
  have hLog : ContDiffOn ℝ ∞ f Y := hP.1.log (fun x hx => (hP.2 x hx).1.ne')
  have hDLog := ((hLog.contDiffAt (hY.mem_nhds hy)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hHessEq : hessianBilinear d.γ f y (d.frame y i) (d.frame y j) =
      frameHessian d.γ d.frame f y i j :=
    hessianBilinear_eq_coordinate d.γ f y hDLog (d.frame y i) (d.frame y j)
  have hJet : jetNorm d.γ d.frame f 2 y ≤ Cj 2*b^2 :=
    (hP.2 y hy).2.2.2 2 (by norm_num)
  have hJet' : jetNorm d.γ d.frame f 2 y ≤ |Cj 2| *b^2 :=
    hJet.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hHess : |hessianBilinear d.γ f y (d.frame y i) (d.frame y j)| ≤ |Cj 2| *b^2 :=
    (congrArg abs hHessEq).trans_le ((frameHessian_abs_le_jetNorm d.γ d.frame f y i j).trans hJet')
  have hProd : |fderiv ℝ f y (d.frame y i)*fderiv ℝ f y (d.frame y j)| ≤ b^2 := by
    rw [abs_mul]
    exact (mul_le_mul (frame_logRadius_abs_le_beta d.γ d.frame d.radius y hFrame i)
      (frame_logRadius_abs_le_beta d.γ d.frame d.radius y hFrame j) (abs_nonneg _) (Real.sqrt_nonneg _)).trans_eq
        (pow_two b).symm
  rw [scaledFrameLogRadiusCovariant_eq hY d.γ hP.1 he hy hr hFrame,abs_mul,abs_of_pos hr]
  calc
    _ ≤ d.radius y*(|hessianBilinear d.γ f y (d.frame y i) (d.frame y j)|+
        |fderiv ℝ f y (d.frame y i)*fderiv ℝ f y (d.frame y j)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hr.le
    _ ≤ d.radius y*(|Cj 2| *b^2+b^2) := mul_le_mul_of_nonneg_left (add_le_add hHess hProd) hr.le
    _ = (|Cj 2|+1)*(d.radius y*b^2) := by ring
    _ ≤ (|Cj 2|+1)*ε := mul_le_mul_of_nonneg_left (hd.2.2.2.2.2 y hy).2 (by positivity)

theorem Admissible.scaledFrameLogRadiusCovariant_frame_le {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i j : I) :
    |scaledFrameLogRadiusCovariant d.γ d.radius d.frame y (d.frame y i) j| ≤ |Cj 2|+1 :=
  (hd.scaledFrameLogRadiusCovariant_frame_bound hY hy i j).trans
    ((mul_le_mul_of_nonneg_left hε1 (by positivity : 0 ≤ |Cj 2|+1)).trans_eq (mul_one _))

end ShrinkingSpheres

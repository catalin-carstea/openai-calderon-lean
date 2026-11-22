module

public import Proof.CalderonN.TraceCoordinateModel
public import Proof.CalderonN.SupportedHorizontalRotationCovariance

import Proof.CalderonN.MovingRadius
import Mathlib.Tactic

/-! In chart coordinates the logarithmic-radius part of the derivative
cancels the derivative of the reciprocal radius, leaving only bounded
frame and connection coefficients in the leading velocity commutator. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)

abbrev supportedCoordinateHorizontal (i : I dim) :=
  supportedHorizontal hY hg hK he (fun _ => axis i) contDiffOn_const

theorem supportedCoordinateHorizontal_eq_base_add_rotation (i : I dim) :
    supportedCoordinateHorizontal hY hg hK he i =
      smoothSupportedTraceBaseDiff (axis i)+
      (∑ a : I dim,∑ b : I dim,smoothSupportedTraceBaseMul hY
        (fun x => (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b)
        (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b))*
        supportedRotation hY a b) := by
  have hBase : (∑ j : I dim,smoothSupportedTraceBaseMul hY (fun _ : X dim => axis i j)
        (contDiffOn_vector_component (fun _ => axis i) contDiffOn_const j)*
          smoothSupportedTraceBaseDiff (axis j)) = smoothSupportedTraceBaseDiff (axis i) := by
    classical
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [LinearMap.sum_apply,map_sum,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,
      axis,PiLp.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change _ = _
  unfold supportedCoordinateHorizontal supportedHorizontal
  rw [hBase]

theorem supportedCoordinateHorizontal_comm_scalar (f : X dim → ℝ)
    (hf : ContDiffOn ℝ ∞ f Y) (i : I dim) :
    let f' (x : X dim) := coordDeriv i f x
    let hf' : ContDiffOn ℝ ∞ f' Y := (hf.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
    supportedCoordinateHorizontal hY hg hK he i*smoothSupportedTraceBaseMul hY f hf-
      smoothSupportedTraceBaseMul hY f hf*supportedCoordinateHorizontal hY hg hK he i =
      smoothSupportedTraceBaseMul hY f' hf' := by
  dsimp only
  rw [supportedCoordinateHorizontal_eq_base_add_rotation]
  let μ := smoothSupportedTraceBaseMul hY f hf
  let K₁ (a b : I dim) := smoothSupportedTraceBaseMul hY
    (fun x => (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b)
    (contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he _ contDiffOn_const a b))
  let Rot := supportedRotation hY
  let Q := ∑ a : I dim,∑ b : I dim,K₁ a b*Rot a b
  let P := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  have hKμ (a b : I dim) : K₁ a b*μ = μ*K₁ a b := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [K₁,μ,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,smul_smul]
    rw [mul_comm]
  have hRμ (a b : I dim) : μ*Rot a b = Rot a b*μ :=
    smoothSupportedTraceBaseMul_comm_fiber hY f hf _ _
  have hQ : Q*μ = μ*Q := by
    simp only [Q,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_assoc,← hRμ,← mul_assoc,hKμ,mul_assoc]
  have hP := smoothSupportedTraceBaseDiff_mul hY (axis i) f hf
  dsimp only at hP
  change (P+Q)*μ-μ*(P+Q) = _
  rw [add_mul,mul_add,hQ,hP]
  abel

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

theorem supportedFlatDegree_comm_coordinateRaising (hn : 3 ≤ dim) (j : I dim) :
    let B := supportedFlatDegree hA hEll S hY
    let R := supportedCoordinateRaising hY hg he hA hEll S j
    B*R-R*B = R := by
  dsimp only
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  let B := smoothTraceFlatDegree hA hEll S
  let R := smoothTraceRaising B
  let v := smoothSupportedTraceFiberL x u
  simp only [LinearMap.sub_apply,map_sub,Module.End.mul_apply,supportedCoordinateRaising,
    smoothSupportedTraceFiberAction_fiber,LinearMap.sum_apply,map_sum,smoothSupportedTraceBaseMul_fiber,
    map_smul,← Finset.sum_sub_distrib,← smul_sub]
  change (∑ a : I dim,traceFrameCoordinate g e a j x • (B (R a v)-R a (B v))) =
    ∑ a : I dim,traceFrameCoordinate g e a j x • R a v
  apply Finset.sum_congr rfl
  intro a _
  have h := congrArg (fun T : Module.End ℝ (SmoothSphereTrace dim) => T v)
    (smoothTraceDegree_comm_raising hn hA hEll S a)
  simpa only [LinearMap.sub_apply,Module.End.mul_apply] using congrArg (traceFrameCoordinate g e a j x • ·) h

variable {r : X dim → ℝ} (hr : ContDiffOn ℝ ∞ r Y) (hr₀ : ∀ x ∈ Y,r x ≠ 0)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (r x)) Y)

theorem supportedCoordinateModel_comm_leadingVelocity (hn : 3 ≤ dim) (i j : I dim) :
    let H := supportedCoordinateHorizontal hY hg hK he i
    let R := supportedCoordinateRaising hY hg he hA hEll S j
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S i
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S j
    D*V-V*D = smoothSupportedTraceBaseMul hY (fun x => (r x)⁻¹) (hr.inv hr₀)*(H*R-R*H) := by
  dsimp only
  let H := supportedCoordinateHorizontal hY hg hK he i
  let R := supportedCoordinateRaising hY hg he hA hEll S j
  let B := supportedFlatDegree hA hEll S hY
  let f := traceCoordinateLogGradient r i
  let hF := contDiffOn_traceCoordinateLogGradient hY hlog i
  let F := smoothSupportedTraceBaseMul hY f hF
  let s := fun x => (r x)⁻¹
  let hs := hr.inv hr₀
  let M := smoothSupportedTraceBaseMul hY s hs
  have hHM : H*M-M*H = -(M*F) := by
    rw [supportedCoordinateHorizontal_comm_scalar hY hg hK he s hs i,← smoothSupportedTraceBaseMul_mul hY,
      ← smoothSupportedTraceBaseMul_neg hY]
    apply smoothSupportedTraceBaseMul_congr
    intro x hx
    have hrD := (hr.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ s x (axis i) = -((r x)⁻¹*fderiv ℝ (fun y => Real.log (r y)) x (axis i))
    have hSD : fderiv ℝ s x = (-(r x ^ 2)⁻¹) • fderiv ℝ r x := by
      have h := (hasDerivAt_inv (hr₀ x hx)).comp_hasFDerivAt x hrD.hasFDerivAt
      simpa only [Function.comp_def] using h.fderiv
    rw [hSD,logRadius_derivative r x (axis i) hrD (hr₀ x hx)]
    simp only [smul_apply,smul_eq_mul]
    field_simp [hr₀ x hx]
  have hMB : M*B = B*M := smoothSupportedTraceBaseMul_comm_fiber hY _ _ _ _
  have hMF : M*F = F*M := by
    rw [← smoothSupportedTraceBaseMul_mul hY,← smoothSupportedTraceBaseMul_mul hY]
    apply smoothSupportedTraceBaseMul_congr
    exact fun _ _ => mul_comm _ _
  have hFR : F*R = R*F := by
    ext u : 1
    apply smoothSupportedTraceSection_ext_by_fibers
    intro x hx
    simp only [F,R,supportedCoordinateRaising,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber,
      LinearMap.sum_apply,map_sum,smoothSupportedTraceFiberAction_fiber,map_smul,
      smul_smul,mul_comm]
  have hBR : B*R-R*B = R := supportedFlatDegree_comm_coordinateRaising hY hg he hA hEll S hn j
  change (H+F*B)*(M*R)-(M*R)*(H+F*B) = M*(H*R-R*H)
  have hHM' : H*M = M*H-M*F := by
    rw [sub_eq_iff_eq_add] at hHM
    rw [hHM]
    abel
  have hBR' : B*R = R+R*B := sub_eq_iff_eq_add.mp hBR
  rw [add_mul,mul_add,← mul_assoc H M R,hHM']
  have hFMB : (F*B)*(M*R) = (M*F)*(B*R) := by
    rw [mul_assoc F B,← mul_assoc B M,← hMB,mul_assoc M B,← mul_assoc F M,← hMF]
  rw [hFMB,hBR']
  have hRFB : (M*R)*(F*B) = (M*F)*(R*B) := by
    rw [mul_assoc M R,← mul_assoc R F,← hFR]
    simp only [mul_assoc]
  rw [hRFB]
  noncomm_ring

end CalderonN

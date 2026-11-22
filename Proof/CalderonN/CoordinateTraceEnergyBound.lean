module

public import Proof.CalderonN.IntegratedCoordinateTraceError
public import Proof.CalderonN.TraceFrameHorizontalLinearity

import Proof.CalderonN.TraceFrameCoefficients
import Mathlib.Tactic

/-! The coordinate derivative differs from a bounded combination of the
actual orthonormal horizontal derivatives by a first angular derivative. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}

theorem supportedTrace_coordinateDerivative_fiber_eq (hY : IsOpen Y)
    {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {x : X dim} (hx : x ∈ Y) (i : I dim) (u : SmoothSupportedTraceSection Y) :
    let H (a : I dim) := supportedHorizontal hY hg hK he (fun y => e y a) (he a)
    let R (a b : I dim) := smoothSphereTraceRotation a b
    let c (a b : I dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b
    smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff (axis i) u) =
      (∑ a,traceFrameCoordinate g e a i x • smoothSupportedTraceFiberL x (H a u))-
      (∑ a,∑ b,c a b • R a b (smoothSupportedTraceFiberL x u)) := by
  dsimp only
  classical
  let H (a : I dim) := supportedHorizontal hY hg hK he (fun y => e y a) (he a)
  let H₀ (j : I dim) := supportedHorizontal hY hg hK he (fun _ => axis j) contDiffOn_const
  let F := smoothSupportedTraceFiberL (Y:=Y) x
  let c₁ (a : I dim) := traceFrameCoordinate g e a i x
  let c (a b : I dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b
  let R (a b : I dim) := smoothSphereTraceRotation a b
  have hv : (∑ a,c₁ a • e x a) = axis i := by
    have h := frameVectorL_frameCoordinatesL g x (e x) (hframe x hx) (axis i)
    rw [frameVectorL_apply _ _ x] at h
    exact h
  have hCoeff (j : I dim) : (∑ a,c₁ a*e x a j) = if j=i then 1 else 0 := by
    have h := congrArg (EuclideanSpace.proj (𝕜:=ℝ) j) hv
    simpa only [map_sum,map_smul,PiLp.proj_apply,smul_eq_mul,axis,PiLp.single_apply] using h
  have hH (a : I dim) : F (H a u) = ∑ j,e x a j • F (H₀ j u) := by
    change F (supportedHorizontal hY hg hK he (fun y => e y a) (he a) u) = _
    rw [supportedHorizontal_axis_sum hY hg hK he hframe _ (he a)]
    simp only [F,H₀,LinearMap.sum_apply,map_sum,Module.End.mul_apply,smoothSupportedTraceBaseMul_fiber]
  have hH₀ (j : I dim) :
      F (H₀ j u) = F (smoothSupportedTraceBaseDiff (axis j) u)+
        ∑ a,∑ b,((-(1/2:ℝ))*frameConnectionCoefficient g e x (axis j) a b) • R a b (F u) := by
    dsimp only [F,H₀,R,supportedHorizontal]
    simp only [LinearMap.add_apply,map_add,LinearMap.sum_apply,map_sum,Module.End.mul_apply,
      smoothSupportedTraceBaseMul_fiber,smoothSupportedTraceFiberAction_fiber]
    congr 1
    simp [axis,PiLp.single_apply,ite_smul,Finset.sum_ite_eq',eq_comm]
  have hSum : (∑ a,c₁ a • F (H a u)) = F (H₀ i u) := by
    simp_rw [hH,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul,hCoeff,ite_smul,one_smul,zero_smul]
    simp [Finset.sum_ite_eq']
  change F (smoothSupportedTraceBaseDiff (axis i) u) =
    (∑ a,c₁ a • F (H a u))-(∑ a,∑ b,c a b • R a b (F u))
  rw [hSum,hH₀]
  dsimp only [c]
  abel

theorem coordinateTraceEnergy_le_horizontal (hn : 3 ≤ dim)
    (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {x : X dim} (hx : x ∈ Y) (β : X dim → ℝ) (hβ : 1 ≤ β x)
    (J R₀ : ℝ) (hJ : 0 ≤ J) (hR₀ : 0 ≤ R₀)
    (hEntry : ∀ a i,|traceFrameCoordinate g e a i x| ≤ J)
    (hΓ : ∀ i a b,|frameConnectionCoefficient g e x (axis i) a b| ≤ J)
    (hRot : ∀ a b : I dim,SmoothTraceAngularBound hn 1 R₀ (smoothSphereTraceRotation a b))
    (u : SmoothSupportedTraceSection Y) :
    let H (a : I dim) := supportedHorizontal hY hg hK he (fun y => e y a) (he a)
    let C := (dim:ℝ)*J+(dim:ℝ)^2*(J*R₀)
    coordinateTraceEnergy hn β u x ≤
      (2*(dim:ℝ)*C^2+1)*
        ((β x)⁻¹*(∑ a,traceOrderNorm hn 2 (smoothSupportedTraceFiberL x (H a u))^2)+
          β x*traceOrderNorm hn 3 (smoothSupportedTraceFiberL x u)^2) := by
  dsimp only
  let H (a : I dim) := supportedHorizontal hY hg hK he (fun y => e y a) (he a)
  let T := smoothSphereTraceSobolev hn (traceOrderExponent 2) (traceOrderExponent_le 2)
  let F := smoothSupportedTraceFiberL (Y:=Y) x
  let c₁ (a i : I dim) := traceFrameCoordinate g e a i x
  let c (i a b : I dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (axis i) a b
  let R (a b : I dim) := smoothSphereTraceRotation a b
  let X₀ := traceOrderNorm hn 3 (F u)
  let S := ∑ a,‖T (F (H a u))‖^2
  let H₀ := Real.sqrt S
  let C := (dim:ℝ)*J+(dim:ℝ)^2*(J*R₀)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hX₀ : 0 ≤ X₀ := norm_nonneg _
  have hHi (i : I dim) : ‖T (F (H i u))‖ ≤ H₀ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hS]
    exact Finset.single_le_sum (fun a _ => sq_nonneg ‖T (F (H a u))‖) (Finset.mem_univ i)
  have hRotN (a b : I dim) : ‖T (R a b (F u))‖ ≤ R₀*X₀ :=
    hRot a b 2 3 (by decide) (F u)
  have hCΓ (i a b : I dim) : |c i a b| ≤ J := by
    dsimp only [c]
    rw [abs_mul,abs_of_nonpos (by norm_num : -(1/2:ℝ) ≤ 0),neg_neg]
    exact (mul_le_mul_of_nonneg_left (hΓ i a b) (by norm_num)).trans (by linarith only [hJ])
  have hT (i : I dim) :
      ‖T (F (smoothSupportedTraceBaseDiff (axis i) u))‖ ≤ C*(H₀+X₀) := by
    rw [supportedTrace_coordinateDerivative_fiber_eq hY hg hK he hframe hx i u]
    change ‖T ((∑ a,c₁ a i • F (H a u))-(∑ a,∑ b,c i a b • R a b (F u)))‖ ≤ _
    simp only [map_sub,map_sum,map_smul]
    refine (norm_sub_le _ _).trans ?_
    have h₁ : ‖∑ a,c₁ a i • T (F (H a u))‖ ≤ (dim:ℝ)*(J*H₀) := by
      calc
        _ ≤ ∑ a : I dim,J*H₀ := (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => by
          rw [norm_smul,Real.norm_eq_abs]
          exact mul_le_mul (hEntry a i) (hHi a) (norm_nonneg _) hJ)
        _ = _ := by simp [nsmul_eq_mul]
    have h₂ : ‖∑ a,∑ b,c i a b • T (R a b (F u))‖ ≤ (dim:ℝ)^2*(J*(R₀*X₀)) := by
      calc
        _ ≤ ∑ a : I dim,∑ b : I dim,J*(R₀*X₀) := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
            rw [norm_smul,Real.norm_eq_abs]
            exact mul_le_mul (hCΓ i a b) (hRotN a b) (norm_nonneg _) hJ))
        _ = _ := by simp [nsmul_eq_mul,pow_two,mul_assoc]
    refine (add_le_add h₁ h₂).trans ?_
    dsimp only [C]
    nlinarith only [mul_nonneg (show 0 ≤ (dim:ℝ)*J by positivity) hX₀,
      mul_nonneg (show 0 ≤ (dim:ℝ)^2*(J*R₀) by positivity) (Real.sqrt_nonneg S)]
  have hD (i : I dim) :
      ‖T (F (smoothSupportedTraceBaseDiff (axis i) u))‖^2 ≤ 2*C^2*(S+X₀^2) := by
    have h₁ : ‖T (F (smoothSupportedTraceBaseDiff (axis i) u))‖^2 ≤ (C*(H₀+X₀))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (add_nonneg (Real.sqrt_nonneg _) hX₀))).mpr (hT i)
    have h₂ : (H₀+X₀)^2 ≤ 2*(H₀^2+X₀^2) := by nlinarith only [sq_nonneg (H₀-X₀)]
    calc
      _ ≤ _ := h₁
      _ = C^2*(H₀+X₀)^2 := by ring
      _ ≤ C^2*(2*(H₀^2+X₀^2)) := mul_le_mul_of_nonneg_left h₂ (sq_nonneg C)
      _ = _ := by rw [show H₀^2 = S from Real.sq_sqrt hS]; ring
  have hDS : (∑ i : I dim,‖T (F (smoothSupportedTraceBaseDiff (axis i) u))‖^2) ≤
      2*(dim:ℝ)*C^2*(S+X₀^2) :=
    (Finset.sum_le_sum fun i _ => hD i).trans_eq (by simp [nsmul_eq_mul]; ring)
  have hβ₀ : 0 < β x := zero_lt_one.trans_le hβ
  have hb : (β x)⁻¹ ≤ β x := (inv_le_one_of_one_le₀ hβ).trans hβ
  have hβ₂ := mul_le_mul_of_nonneg_right hb (sq_nonneg X₀)
  change (β x)⁻¹*(∑ i : I dim,‖T (F (smoothSupportedTraceBaseDiff (axis i) u))‖^2)+β x*X₀^2
    ≤ (2*(dim:ℝ)*C^2+1)*((β x)⁻¹*S+β x*X₀^2)
  have hbD := mul_le_mul_of_nonneg_left hDS (inv_nonneg.mpr hβ₀.le)
  have hbS := mul_le_mul_of_nonneg_left hβ₂ (show 0 ≤ 2*(dim:ℝ)*C^2 by positivity)
  nlinarith only [hbD,hbS,mul_nonneg (inv_nonneg.mpr hβ₀.le) hS]

end CalderonN

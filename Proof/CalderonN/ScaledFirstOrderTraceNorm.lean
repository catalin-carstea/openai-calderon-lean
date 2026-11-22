module

public import Proof.CalderonN.IntegratedCoordinateTraceError

import Proof.CalderonN.PhysicalTraceLowerOrderMass
import Proof.CalderonN.SmoothTraceHigherLift
import Proof.CalderonN.ActualGaussConormalBounds
import Mathlib.Tactic

/-! A first base derivative with a coefficient of size β⁻² and a first
angular derivative of size β⁻¹ are absorbed directly in norm. -/

public section

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 5100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem norm_smoothTraceL2_le_half (hn : 3 ≤ dim) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceL2 hn u‖ ≤ traceOrderNorm hn 2 u := by
  rw [← norm_smoothSphereTraceSobolev_zero_eq,traceOrderNorm_half_eq]
  exact norm_smoothSphereTraceSobolev_mono hn 0 (1/2) (by norm_num) (by norm_num) (by norm_num) u

theorem sq_norm_scaledFirstOrder_trace_le (hn : 3 ≤ dim) (β floor C : ℝ)
    (hFloor : 1 ≤ floor) (hβ : floor ≤ β) (hC : 0 ≤ C)
    (u : SmoothSphereTrace dim) (H : I dim → SmoothSphereTrace dim)
    (L : I dim → Module.End ℝ (SmoothSphereTrace dim)) (Q : Module.End ℝ (SmoothSphereTrace dim))
    (hL : ∀ i,SmoothTraceAngularBound hn 0 (C*(β⁻¹)^2) (L i))
    (hQ : SmoothTraceAngularBound hn 1 (C*β⁻¹) Q) :
    ‖smoothSphereTraceL2 hn ((∑ i,L i (H i))+Q u)‖^2 ≤
      (2*((dim:ℝ)*C+C)^2/floor^2)*
        (β⁻¹*(∑ i,traceOrderNorm hn 2 (H i)^2)+β*traceOrderNorm hn 3 u^2) := by
  let S := ∑ i,traceOrderNorm hn 2 (H i)^2
  let W := traceOrderNorm hn 3 u
  let A := (dim:ℝ)*C+C
  let U := (∑ i,L i (H i))+Q u
  have hβ₀ : 0 < β := (zero_lt_one.trans_le hFloor).trans_le hβ
  have hf₀ : 0 < floor := zero_lt_one.trans_le hFloor
  have hDim : 0 ≤ (dim:ℝ) := Nat.cast_nonneg _
  have hiβ : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ₀.le
  have hif : 0 ≤ floor⁻¹ := inv_nonneg.mpr hf₀.le
  have hA : 0 ≤ A := add_nonneg (mul_nonneg hDim hC) hC
  have hW : 0 ≤ W := norm_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (traceOrderNorm hn 2 (H i)))
  have hSi (i : I dim) : traceOrderNorm hn 2 (H i) ≤ Real.sqrt S := by
    have hi : 0 ≤ traceOrderNorm hn 2 (H i) := norm_nonneg _
    apply (sq_le_sq₀ hi (Real.sqrt_nonneg S)).mp
    rw [Real.sq_sqrt hS]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (traceOrderNorm hn 2 (H j))) (Finset.mem_univ i)
  have hLi (i : I dim) : traceOrderNorm hn 2 (L i (H i)) ≤ C*(β⁻¹)^2*Real.sqrt S :=
    (hL i 2 2 (by decide) (H i)).trans (mul_le_mul_of_nonneg_left (hSi i) (by positivity))
  let T := smoothSphereTraceL2 hn
  have hL' : ‖∑ i,T (L i (H i))‖ ≤ (dim:ℝ)*(C*(β⁻¹)^2*Real.sqrt S) := by
    refine (norm_sum_le _ _).trans ?_
    have hl (i : I dim) : ‖T (L i (H i))‖ ≤ C*(β⁻¹)^2*Real.sqrt S :=
      (norm_smoothTraceL2_le_half hn (L i (H i))).trans (hLi i)
    refine (Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hl i)).trans_eq ?_
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hQ' : ‖T (Q u)‖ ≤ C*β⁻¹*W :=
    (norm_smoothTraceL2_le_half hn (Q u)).trans (hQ 2 3 (by decide) u)
  have hN : ‖T U‖ ≤ (A/floor)*(β⁻¹*Real.sqrt S+W) := by
    dsimp only [U]
    rw [map_add,map_sum]
    refine ((norm_add_le _ _).trans (add_le_add hL' hQ')).trans ?_
    have hRec : β⁻¹ ≤ floor⁻¹ := inv_anti₀ hf₀ hβ
    have h₁ := mul_le_mul_of_nonneg_left hRec
      (mul_nonneg (mul_nonneg (mul_nonneg hDim hC) hiβ) (Real.sqrt_nonneg S))
    have h₂ := mul_le_mul_of_nonneg_left hRec (mul_nonneg hC hW)
    dsimp only [A]
    rw [div_eq_mul_inv]
    have h₃ := mul_nonneg (mul_nonneg (mul_nonneg hC hif) hiβ) (Real.sqrt_nonneg S)
    have h₄ := mul_nonneg (mul_nonneg (mul_nonneg hDim hC) hif) hW
    linarith only [h₁,h₂,h₃,h₄]
  have hb : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hFloor.trans hβ)
  have hS' : (β⁻¹*Real.sqrt S)^2 ≤ β⁻¹*S := by
    rw [mul_pow,Real.sq_sqrt hS]
    apply mul_le_mul_of_nonneg_right _ hS
    nlinarith only [mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hβ₀.le)]
  have hW' : W^2 ≤ β*W^2 := le_mul_of_one_le_left (sq_nonneg W) (hFloor.trans hβ)
  have hYoung : (β⁻¹*Real.sqrt S+W)^2 ≤ 2*(β⁻¹*S+β*W^2) := by
    nlinarith only [hS',hW',sq_nonneg (β⁻¹*Real.sqrt S-W)]
  calc
    ‖smoothSphereTraceL2 hn U‖^2 ≤ ((A/floor)*(β⁻¹*Real.sqrt S+W))^2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (div_nonneg hA hf₀.le)
        (add_nonneg (mul_nonneg hiβ (Real.sqrt_nonneg S)) hW))).mpr hN
    _ = (A/floor)^2*(β⁻¹*Real.sqrt S+W)^2 := by ring
    _ ≤ (A/floor)^2*(2*(β⁻¹*S+β*W^2)) := mul_le_mul_of_nonneg_left hYoung (sq_nonneg _)
    _ = _ := by rw [div_pow]; ring

theorem norm_scaledFirstOrder_supportedTrace_le (hn : 3 ≤ dim)
    (hY : IsOpen Y) (μ β e : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (hμ₀ : ∀ x ∈ Y,0 ≤ μ x) (floor C : ℝ) (hFloor : 1 ≤ floor) (hC : 0 ≤ C)
    (hβ : ∀ x ∈ Y,floor ≤ β x) (he : IntegrableOn e Y)
    (u v : SmoothSupportedTraceSection Y)
    (hMajor : ∀ x ∈ Y,μ x*(coordinateTraceEnergy hn β u x+coordinateTraceEnergy hn β v x) ≤ e x)
    (S : Module.End ℝ (SmoothSupportedTraceSection Y))
    (hFiber : ∀ x ∈ Y,∃ (L : I dim → Module.End ℝ (SmoothSphereTrace dim))
        (Q : Module.End ℝ (SmoothSphereTrace dim)),
      (∀ i,SmoothTraceAngularBound hn 0 (C*((β x)⁻¹)^2) (L i)) ∧
      SmoothTraceAngularBound hn 1 (C*(β x)⁻¹) Q ∧
      ∀ w,smoothSupportedTraceFiberL x (S w) =
        (∑ i,L i (smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff (axis i) w)))+
          Q (smoothSupportedTraceFiberL x w)) :
    let B := smoothSupportedTracePairingL hn hY μ hμ
    Real.sqrt (B (S u) (S u)+B (S v) (S v)) ≤
      (Real.sqrt 2*((dim:ℝ)*C+C))/floor*Real.sqrt (∫ x in Y,e x) := by
  dsimp only
  let A := (dim:ℝ)*C+C
  let P := (2*A^2/floor^2)
  let E := ∫ x in Y,e x
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hu := (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ (S u) (S u)).integrableOn (s:=Y)
  have hv := (integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ (S v) (S v)).integrableOn (s:=Y)
  simp only [real_inner_self_eq_norm_sq] at hu hv
  have hNorm : smoothSupportedTracePairing hn μ (S u) (S u)+
      smoothSupportedTracePairing hn μ (S v) (S v) ≤ P*E := by
    rw [smoothSupportedTracePairing_self_eq_setIntegral,smoothSupportedTracePairing_self_eq_setIntegral,
      ← integral_add hu hv,← integral_const_mul]
    apply integral_mono_ae (hu.add hv) (he.const_mul P)
    filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
    obtain ⟨L,Q,hL,hQ,hEq⟩ := hFiber x hx
    have hh (w : SmoothSupportedTraceSection Y) :
        ‖smoothSupportedTraceL2 hn (S w) x‖^2 ≤ P*coordinateTraceEnergy hn β w x := by
      rw [smoothSupportedTraceL2,hEq w]
      exact sq_norm_scaledFirstOrder_trace_le hn (β x) floor C hFloor (hβ x hx) hC
        _ _ L Q hL hQ
    refine (add_le_add (mul_le_mul_of_nonneg_left (hh u) (hμ₀ x hx))
      (mul_le_mul_of_nonneg_left (hh v) (hμ₀ x hx))).trans ?_
    calc
      _ = P*(μ x*(coordinateTraceEnergy hn β u x+coordinateTraceEnergy hn β v x)) := by ring
      _ ≤ P*e x := mul_le_mul_of_nonneg_left (hMajor x hx) hP
  refine (Real.sqrt_le_sqrt hNorm).trans_eq ?_
  rw [Real.sqrt_mul hP]
  congr 1
  dsimp only [P]
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),
    Real.sqrt_sq (by dsimp [A]; positivity),Real.sqrt_sq (zero_le_one.trans hFloor)]

end CalderonN

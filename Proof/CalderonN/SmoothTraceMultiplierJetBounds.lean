module

public import Proof.CalderonN.ParametricSphereMultiplierJets
public import Proof.CalderonN.SmoothTraceCommutatorBounds

import Proof.CalderonN.SmoothTraceHigherLift
import Mathlib.Tactic

/-! Fixed-ball scalar derivatives bound the multiplier and its actual
angular commutators on the four trace Sobolev levels. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def smoothTraceMultiplierJetConstant (dim : ℕ) (C : ℝ) : ℝ :=
  let c := (2*Real.sqrt ((dim:ℝ)+3))*C
  let d := (2*Real.sqrt ((dim:ℝ)+3))*(4*C)
  max c (smoothTraceRotationLiftConstant dim c d)

theorem smoothTraceMultiplierJetConstant_nonneg (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ smoothTraceMultiplierJetConstant dim C := by
  unfold smoothTraceMultiplierJetConstant
  exact le_max_of_le_left (by positivity)

theorem smoothTraceMultiplier_angularBound_of_jets (hn : 3 ≤ dim) (m : SmoothData dim)
    (C : ℝ) (hC : 0 ≤ C) (h : ∀ z ∈ closedBall (0:X dim) 1,LocalSmoothJetBudget m.1 z 2 C) :
    SmoothTraceAngularBound hn 0 (smoothTraceMultiplierJetConstant dim C) (smoothSphereTraceMul m) := by
  apply smoothSphereTraceMul_angularBound hn m hC (by positivity)
  · intro z hz
    have h₀ := (h z (ball_subset_closedBall hz)).bound 0 (by decide)
    rwa [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h₀
  · intro z hz
    have h₁ := (h z (ball_subset_closedBall hz)).fderiv.bound 0 (by decide)
    rw [norm_gradient_eq_norm_fderiv]
    rwa [norm_iteratedFDeriv_zero] at h₁
  · intro i j z hz
    have hr := localSmoothJetBudget_sphereRotation i j (mem_ball_zero_iff.mp hz).le
      (N:=1) (h z (ball_subset_closedBall hz))
    have h₀ := hr.bound 0 (by decide)
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at h₀
    norm_num at h₀
    exact h₀
  · intro i j z hz
    have hr := localSmoothJetBudget_sphereRotation i j (mem_ball_zero_iff.mp hz).le
      (N:=1) (h z (ball_subset_closedBall hz))
    have h₁ := hr.fderiv.bound 0 (by decide)
    rw [norm_gradient_eq_norm_fderiv]
    rw [norm_iteratedFDeriv_zero] at h₁
    norm_num at h₁
    exact h₁

theorem smoothTraceMultiplier_commutatorBounds_of_jets (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (m : SmoothData dim) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z ∈ closedBall (0:X dim) 1, LocalSmoothJetBudget m.1 z 3 C) :
    let U := smoothTraceMultiplierJetConstant dim C
    let R := smoothTraceMultiplierJetConstant dim (8*C)
    let V := 64*C
    let V₁ := smoothTraceRotationLiftConstant dim V V
    let V₂ := smoothTraceRotationLiftConstant dim V₁ V₁
    let D := 2*(dim:ℝ)^4*(V+V₁+V₂)
    SmoothTraceCommutatorBounds hn B 0 (U+R+D) (smoothSphereTraceMul m) := by
  dsimp only
  let U := smoothTraceMultiplierJetConstant dim C
  let R := smoothTraceMultiplierJetConstant dim (8*C)
  let V := 64*C
  let V₁ := smoothTraceRotationLiftConstant dim V V
  let V₂ := smoothTraceRotationLiftConstant dim V₁ V₁
  let D := 2*(dim:ℝ)^4*(V+V₁+V₂)
  have hU := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) C hC
  have hR := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (8*C) (by positivity)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hV₁ : 0 ≤ V₁ := Real.sqrt_nonneg _
  have hV₂ : 0 ≤ V₂ := Real.sqrt_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hFirst (i j : I dim) (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
      LocalSmoothJetBudget (sphereRotationDerivative i j m.1) z 2 (8*C) := by
    have h' := localSmoothJetBudget_sphereRotation i j (mem_closedBall_zero_iff.mp hz) (N:=2) (h z hz)
    norm_num at h'
    exact h'
  have hSecond (i j a b : I dim) (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
      LocalSmoothJetBudget (sphereRotationDerivative a b (sphereRotationDerivative i j m.1)) z 1 (32*C) := by
    have h' := localSmoothJetBudget_sphereRotation a b (mem_closedBall_zero_iff.mp hz) (N:=1) (hFirst i j z hz)
    exact h'.enlarge (by ring_nf; rfl)
  have hThird (i j a b p q : I dim) (z : X dim) (hz : z ∈ closedBall (0:X dim) 1) :
      LocalSmoothJetBudget
        (sphereRotationDerivative p q (sphereRotationDerivative a b (sphereRotationDerivative i j m.1))) z 0 V := by
    have h' := localSmoothJetBudget_sphereRotation p q (mem_closedBall_zero_iff.mp hz) (N:=0) (hSecond i j a b z hz)
    exact h'.enlarge (by dsimp only [V]; ring_nf; rfl)
  have hEval {f : X dim → ℝ} {z : X dim} {N : ℕ} {C : ℝ}
      (h : LocalSmoothJetBudget f z N C) : |f z| ≤ C := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h.bound 0 (Nat.zero_le _)
  refine ⟨by positivity,?_,?_,?_⟩
  · exact (smoothTraceMultiplier_angularBound_of_jets hn m C hC
      (fun z hz => (h z hz).mono_order (by decide))).enlarge (by linarith)
  · have hBnd := smoothTraceMultiplier_degreeComm_order_zero hn B hB hFin m V hV
      (fun i j z hz => (hEval (hFirst i j z (sphere_subset_closedBall hz))).trans (by dsimp only [V]; linarith))
      (fun i j a b z hz => (hEval (hSecond i j a b z (sphere_subset_closedBall hz))).trans
        (by dsimp only [V]; linarith))
      (fun i j a b p q z hz => hEval (hThird i j a b p q z (sphere_subset_closedBall hz)))
    exact hBnd.enlarge (show D ≤ U+R+D by linarith)
  · intro i j
    let m' : SmoothData dim := ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩
    rw [smoothTraceAngularComm,show smoothSphereTraceRotation i j*smoothSphereTraceMul m-
      smoothSphereTraceMul m*smoothSphereTraceRotation i j = smoothSphereTraceMul m' from
        smoothSphereTraceMul_rotation_comm m i j]
    exact (smoothTraceMultiplier_angularBound_of_jets hn m' (8*C) (by positivity) (hFirst i j)).enlarge
      (show R ≤ U+R+D by linarith)

end CalderonN

module

public import Proof.CalderonN.SmoothTraceMultiplierDegreeComm
public import Proof.CalderonN.SmoothTraceAngularCommutator

import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.Gradient

import Proof.CalderonN.FlatTraceRaisingAdjoint
import Proof.CalderonN.BallRotationCalculus
import Mathlib.Tactic

/-! Linear angular data, their degree commutator and the raising
generator obey the required fractional angular bounds. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

namespace SmoothTraceAngularBound

theorem sum {ι : Type*} {hn : 3 ≤ dim} {n : ℕ} (S : Finset ι)
    (A : ι → Module.End ℝ (SmoothSphereTrace dim)) (C : ι → ℝ)
    (h : ∀ i ∈ S,SmoothTraceAngularBound hn n (C i) (A i)) :
    SmoothTraceAngularBound hn n (∑ i ∈ S,C i) (∑ i ∈ S,A i) := by
  intro i j hij u
  simp only [traceOrderNorm,LinearMap.sum_apply,map_sum]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k hk => h k hk i j hij u)).trans_eq
    (Finset.sum_mul _ _ _).symm)

end SmoothTraceAngularBound

@[expose] def smoothLinearTraceDatum (L : X dim →L[ℝ] ℝ) : SmoothData dim := ⟨L,L.contDiff⟩

omit [Nontrivial (Fin dim)] in
theorem smoothLinearTraceDatum_rotation (L : X dim →L[ℝ] ℝ) (i j : I dim) :
    sphereRotationDerivative i j (⇑L) = (L.comp (ballRotationGeneratorL i j) : X dim → ℝ) := by
  funext z
  rw [sphereRotationDerivative,L.fderiv]
  rfl

theorem smoothLinearTraceDatum_multiplier_bound (hn : 3 ≤ dim)
    (L : X dim →L[ℝ] ℝ) (A : ℝ) (hA : 0 ≤ A) (hL : ‖L‖ ≤ A) :
    let c := (2*Real.sqrt ((dim : ℝ)+3))*A
    let d := (2*Real.sqrt ((dim : ℝ)+3))*(2*A)
    SmoothTraceAngularBound hn 0 (max c (smoothTraceRotationLiftConstant dim c d))
      (smoothSphereTraceMul (smoothLinearTraceDatum L)) := by
  have hRot (i j : I dim) : ‖L.comp (ballRotationGeneratorL i j)‖ ≤ 2*A :=
    (L.opNorm_comp_le _).trans ((mul_le_mul hL (norm_ballRotationGeneratorL_le i j)
      (norm_nonneg _) hA).trans_eq (mul_comm _ _))
  have hOn (P : X dim →L[ℝ] ℝ) (B : ℝ) (hB : 0 ≤ B) (hP : ‖P‖ ≤ B)
      {z : X dim} (hz : z ∈ (fixedBallOpens dim : Set (X dim))) : |P z| ≤ B :=
    (P.le_opNorm z).trans ((mul_le_mul hP (mem_ball_zero_iff.mp hz).le (norm_nonneg _) hB).trans_eq (mul_one _))
  apply smoothSphereTraceMul_angularBound hn _ hA (by positivity)
  · exact fun z hz => hOn L A hA hL hz
  · intro z _
    change ‖gradient (⇑L) z‖ ≤ A
    rw [norm_gradient_eq_norm_fderiv,L.fderiv]
    exact hL
  · intro i j z hz
    change |sphereRotationDerivative i j (⇑L) z| ≤ _
    rw [smoothLinearTraceDatum_rotation]
    exact hOn _ _ (by positivity) (hRot i j) hz
  · intro i j z _
    change ‖gradient (sphereRotationDerivative i j (⇑L)) z‖ ≤ _
    rw [smoothLinearTraceDatum_rotation,norm_gradient_eq_norm_fderiv,ContinuousLinearMap.fderiv]
    exact hRot i j

theorem smoothLinearTraceDatum_degreeComm_bound (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (L : X dim →L[ℝ] ℝ) (A : ℝ) (hA : 0 ≤ A) (hL : ‖L‖ ≤ A) :
    let c := 8*A
    let c₁ := smoothTraceRotationLiftConstant dim c c
    let c₂ := smoothTraceRotationLiftConstant dim c₁ c₁
    SmoothTraceAngularBound hn 0 (2*(dim:ℝ)^4*(c+c₁+c₂))
      (B*smoothSphereTraceMul (smoothLinearTraceDatum L)-smoothSphereTraceMul (smoothLinearTraceDatum L)*B) := by
  have hRot (P : X dim →L[ℝ] ℝ) (i j : I dim) : ‖P.comp (ballRotationGeneratorL i j)‖ ≤ ‖P‖*2 :=
    (P.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left (norm_ballRotationGeneratorL_le i j) (norm_nonneg _))
  have hOn (P : X dim →L[ℝ] ℝ) {z : X dim} (hz : z ∈ standardSphere dim) : |P z| ≤ ‖P‖ := by
    have h := P.le_opNorm z
    simpa only [Real.norm_eq_abs,mem_sphere_zero_iff_norm.mp hz,mul_one] using h
  apply smoothTraceMultiplier_degreeComm_order_zero hn B hB hFin _ (8*A) (by positivity)
  · intro i j z hz
    change |sphereRotationDerivative i j (⇑L) z| ≤ _
    rw [smoothLinearTraceDatum_rotation]
    have h := (hOn (L.comp (ballRotationGeneratorL i j)) hz).trans (hRot L i j)
    linarith only [h,hL,hA]
  · intro i j a b z hz
    change |sphereRotationDerivative a b (sphereRotationDerivative i j (⇑L)) z| ≤ _
    rw [smoothLinearTraceDatum_rotation,smoothLinearTraceDatum_rotation]
    let P := L.comp (ballRotationGeneratorL i j)
    have h := (hOn (P.comp (ballRotationGeneratorL a b)) hz).trans (hRot P a b)
    change |(P.comp (ballRotationGeneratorL a b)) z| ≤ _
    have hP : ‖P‖ ≤ ‖L‖*2 := hRot L i j
    linarith only [h,hP,hL,hA]
  · intro i j a b c d z hz
    change |sphereRotationDerivative c d (sphereRotationDerivative a b (sphereRotationDerivative i j (⇑L))) z| ≤ _
    rw [smoothLinearTraceDatum_rotation,smoothLinearTraceDatum_rotation,smoothLinearTraceDatum_rotation]
    let P := L.comp (ballRotationGeneratorL i j)
    let Q := P.comp (ballRotationGeneratorL a b)
    have hP : ‖P‖ ≤ ‖L‖*2 := hRot L i j
    have hQ : ‖Q‖ ≤ ‖P‖*2 := hRot P a b
    have h := (hOn (Q.comp (ballRotationGeneratorL c d)) hz).trans (hRot Q c d)
    change |(Q.comp (ballRotationGeneratorL c d)) z| ≤ _
    linarith only [h,hQ,hP,hL]

end CalderonN

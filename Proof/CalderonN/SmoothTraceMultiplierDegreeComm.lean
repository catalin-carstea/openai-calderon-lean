module

public import Proof.CalderonN.SmoothTraceWeightedDegree
public import Proof.CalderonN.SmoothTraceMultiplierOrder

import Proof.CalderonN.SmoothTraceHigherLift
import Proof.CalderonN.SmoothTraceDegreeFromRotation
import Proof.CalderonN.SmoothZonalSobolev
import Mathlib.Tactic

/-! The commutator of the flat degree with a real multiplier has order
zero on the four trace levels used by the error-form estimate. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def rotateDatum (m : SmoothData dim) (i j : Fin dim) : SmoothData dim :=
  ⟨sphereRotationDerivative i j m.1,contDiff_sphereRotationDerivative i j m.1 m.2⟩

private theorem norm_smoothTraceMul_sobolev_zero (hn : 3 ≤ dim)
    (m : SmoothData dim) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ z ∈ standardSphere dim, |m.1 z| ≤ C)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn 0 (by norm_num) (smoothSphereTraceMul m u)‖ ≤
      C*‖smoothSphereTraceSobolev hn 0 (by norm_num) u‖ := by
  rw [← norm_smoothSphereTraceL2_eq_sobolev_zero,← norm_smoothSphereTraceL2_eq_sobolev_zero]
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let F : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  let G := smoothDataMul m F
  have hEq : smoothSphereTraceMul m (smoothSphereTrace F) = smoothSphereTrace G := by
    apply Subtype.ext
    funext z
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    rfl
  change ‖smoothSphereTraceL2 hn (smoothSphereTraceMul m (smoothSphereTrace F))‖ ≤
    C*‖smoothSphereTraceL2 hn (smoothSphereTrace F)‖
  rw [hEq,smoothSphereTraceL2_apply,smoothSphereTraceL2_apply]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [smoothSphereLift_ae G.1 G.2,smoothSphereLift_ae F.1 F.2] with z hG hF
  rw [hG,hF,Real.norm_eq_abs,Real.norm_eq_abs]
  change |m.1 z*F.1 z| ≤ C*|F.1 z|
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hm z z.property) (abs_nonneg _)

private theorem norm_smoothTraceMul_sobolev_succ (hn : 3 ≤ dim)
    (m : SmoothData dim) (s t : ℝ) (he : s+1 = t) (ht : t ≤ 2)
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ u, ‖smoothSphereTraceSobolev hn s (by linarith) (smoothSphereTraceMul m u)‖ ≤
      C*‖smoothSphereTraceSobolev hn s (by linarith) u‖)
    (hK : ∀ i j u, ‖smoothSphereTraceSobolev hn s (by linarith)
      (smoothSphereTraceMul (rotateDatum m i j) u)‖ ≤ C*‖smoothSphereTraceSobolev hn s (by linarith) u‖)
    (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn t ht (smoothSphereTraceMul m u)‖ ≤
      smoothTraceRotationLiftConstant dim C C*‖smoothSphereTraceSobolev hn t ht u‖ := by
  have hs : s+1 ≤ 2 := he.symm ▸ ht
  have h := norm_smoothSphereTrace_higher_of_rotation hn s s hs hs (smoothSphereTraceMul m) C C hC hC
    hm (fun i j u => by rw [smoothSphereTraceMul_rotation_comm]; exact hK i j u) u
  rw [smoothSphereTraceSobolev_order_eq hn he hs ht,smoothSphereTraceSobolev_order_eq hn he hs ht] at h
  exact h

private theorem integerTraceExponent_le (k : Fin 4) : (k.val:ℝ)-1 ≤ 2 := by
  have hk : k.val ≤ 3 := by omega
  have hk' : (k.val:ℝ) ≤ 3 := by exact_mod_cast hk
  linarith

private theorem norm_smoothTraceMul_integer_levels (hn : 3 ≤ dim) (m : SmoothData dim)
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ z ∈ standardSphere dim, |m.1 z| ≤ C)
    (hm₁ : ∀ i j z, z ∈ standardSphere dim → |(rotateDatum m i j).1 z| ≤ C)
    (hm₂ : ∀ i j a b z, z ∈ standardSphere dim → |(rotateDatum (rotateDatum m i j) a b).1 z| ≤ C) :
    let C₁ := smoothTraceRotationLiftConstant dim C C
    let C₂ := smoothTraceRotationLiftConstant dim C₁ C₁
    let D := C+C₁+C₂
    ∀ k : Fin 4, ∀ u,
      ‖smoothSphereTraceSobolev hn ((k.val:ℝ)-1) (integerTraceExponent_le k) (smoothSphereTraceMul m u)‖ ≤
        D*‖smoothSphereTraceSobolev hn ((k.val:ℝ)-1) (integerTraceExponent_le k) u‖ := by
  dsimp only
  let L := smoothTraceRotationLiftConstant dim C C
  let H := smoothTraceRotationLiftConstant dim L L
  let D := C+L+H
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hZero := norm_smoothTraceMul_sobolev_zero hn m hC hm
  have hOne := norm_smoothTraceMul_sobolev_succ hn m 0 1 (by norm_num) (by norm_num) C hC
    hZero (fun i j u => norm_smoothTraceMul_sobolev_zero hn (rotateDatum m i j) hC (hm₁ i j) u)
  have hRotOne (i j : Fin dim) := norm_smoothTraceMul_sobolev_succ hn (rotateDatum m i j) 0 1
    (by norm_num) (by norm_num) C hC (norm_smoothTraceMul_sobolev_zero hn _ hC (hm₁ i j))
    (fun a b u => norm_smoothTraceMul_sobolev_zero hn _ hC (hm₂ i j a b) u)
  have hTwo := norm_smoothTraceMul_sobolev_succ hn m 1 2 (by norm_num) (by norm_num) L hL hOne hRotOne
  have hNeg := norm_smoothTrace_adjoint_of_bound hn 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (smoothSphereTraceMul m) (smoothSphereTraceMul m) (smoothSphereTraceMul_symmetric hn m) L hL hOne
  intro k u
  have hAt (s : ℝ) (hs : s ≤ 2) (he : (k.val:ℝ)-1 = s) (v : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn ((k.val:ℝ)-1) (integerTraceExponent_le k) v‖ = ‖smoothSphereTraceSobolev hn s hs v‖ :=
    congrArg norm (smoothSphereTraceSobolev_order_eq hn he (integerTraceExponent_le k) hs v)
  fin_cases k
  · simp_rw [hAt (-1) (by norm_num) (by norm_num)]
    exact (hNeg u).trans (mul_le_mul_of_nonneg_right (show L ≤ D by dsimp only [D]; linarith) (norm_nonneg _))
  · simp_rw [hAt 0 (by norm_num) (by norm_num)]
    exact (hZero u).trans (mul_le_mul_of_nonneg_right (show C ≤ D by dsimp only [D]; linarith) (norm_nonneg _))
  · simp_rw [hAt 1 (by norm_num) (by norm_num)]
    exact (hOne u).trans (mul_le_mul_of_nonneg_right (show L ≤ D by dsimp only [D]; linarith) (norm_nonneg _))
  · simp_rw [hAt 2 (by norm_num) (by norm_num)]
    exact (hTwo u).trans (mul_le_mul_of_nonneg_right (show H ≤ D by dsimp only [D]; linarith) (norm_nonneg _))

theorem smoothTraceMultiplier_degreeComm_order_zero (hn : 3 ≤ dim)
    (B : Module.End ℝ (SmoothSphereTrace dim)) (hB : SmoothTraceAdjoint hn B B)
    (hFin : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))
    (m : SmoothData dim) (C : ℝ) (hC : 0 ≤ C)
    (hm₁ : ∀ i j z, z ∈ standardSphere dim → |sphereRotationDerivative i j m.1 z| ≤ C)
    (hm₂ : ∀ i j a b z, z ∈ standardSphere dim →
      |sphereRotationDerivative a b (sphereRotationDerivative i j m.1) z| ≤ C)
    (hm₃ : ∀ i j a b c d z, z ∈ standardSphere dim →
      |sphereRotationDerivative c d (sphereRotationDerivative a b (sphereRotationDerivative i j m.1)) z| ≤ C) :
    let C₁ := smoothTraceRotationLiftConstant dim C C
    let C₂ := smoothTraceRotationLiftConstant dim C₁ C₁
    SmoothTraceAngularBound hn 0 (2*(dim:ℝ)^4*(C+C₁+C₂))
      (B*smoothSphereTraceMul m-smoothSphereTraceMul m*B) := by
  dsimp only
  let C₁ := smoothTraceRotationLiftConstant dim C C
  let C₂ := smoothTraceRotationLiftConstant dim C₁ C₁
  let D := C+C₁+C₂
  let T := smoothSphereTraceMul m
  have hC₁ : 0 ≤ C₁ := Real.sqrt_nonneg _
  have hC₂ : 0 ≤ C₂ := Real.sqrt_nonneg _
  have hD : 0 ≤ D := add_nonneg (add_nonneg hC hC₁) hC₂
  have hSym := smoothSphereTraceMul_symmetric hn m
  have hR (i j : Fin dim) (k : Fin 4) (u : SmoothSphereTrace dim) :
      ‖smoothSphereTraceSobolev hn ((k.val:ℝ)-1) (integerTraceExponent_le k)
        (smoothTraceAngularComm i j T u)‖ ≤
      D*‖smoothSphereTraceSobolev hn ((k.val:ℝ)-1) (integerTraceExponent_le k) u‖ := by
    change _ ≤ _
    rw [show smoothTraceAngularComm i j T = smoothSphereTraceMul (rotateDatum m i j) from
      smoothSphereTraceMul_rotation_comm m i j]
    exact norm_smoothTraceMul_integer_levels hn (rotateDatum m i j) C hC (hm₁ i j) (hm₂ i j) (hm₃ i j) k u
  intro i j hij u
  have hj : j = i := Fin.ext (by simpa using hij)
  subst j
  let s := traceOrderExponent i
  have hs : s+1/2 = (i.val:ℝ)-1 := by
    dsimp only [s,traceOrderExponent]
    ring
  have hns : -s+1/2 = (i.rev.val:ℝ)-1 := by
    fin_cases i <;> norm_num [s,traceOrderExponent,Fin.rev]
  have hLe (k : Fin 4) : (k.val:ℝ)-1 ≤ 2  := integerTraceExponent_le k
  have hLe₁ : s+1/2 ≤ 2 := hs.symm ▸ hLe i
  have hLe₂ : -s+1/2 ≤ 2 := hns.symm ▸ hLe i.rev
  have hR₁ (a b : Fin dim) (v : SmoothSphereTrace dim) := hR a b i v
  have hR₂ (a b : Fin dim) (v : SmoothSphereTrace dim) := hR a b i.rev v
  simp_rw [smoothSphereTraceSobolev_order_eq hn hs.symm (hLe i) hLe₁] at hR₁
  simp_rw [smoothSphereTraceSobolev_order_eq hn hns.symm (hLe i.rev) hLe₂] at hR₂
  exact norm_smoothTraceDegree_comm_le_of_rotation hn B T hB hFin hSym s D hD hLe₁ hLe₂ hR₁ hR₂ u

end CalderonN

module

public import Proof.CalderonPatch.NativeBoundaryWave

import Mathlib.Tactic

public section

noncomputable section
open Filter Finset Set
open scoped ContDiff Manifold Topology

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I coordDeriv)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

theorem signedLayerCoordinates_face (y : Y) :
    signedLayerCoordinates (y,(0 : ℝ)) = normalFacePoint y := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [signedLayerCoordinates_height,normalFacePoint_height]
  · rw [signedLayerCoordinates_tangent]
    change y i = Fin.insertNth (α := fun _ : I (n+1) => ℝ) 0 0 (fun k => y k) i.succ
    rw [← Fin.succAbove_zero,Fin.insertNth_apply_succAbove]

/-- A signed function shares its normal derivative on the flat face
with its restriction to the signed height line. -/
theorem coordDeriv_wave_face {V : Y × ℝ → ℂ} (hV : ContDiff ℝ ∞ V)
    (L : ℂ →L[ℝ] ℝ) (y : Y) :
    coordDeriv 0 (L ∘ V ∘ signedLayerCoordinates.symm) (normalFacePoint y) =
      L (deriv (fun t => V (y,t)) 0) := by
  rw [← signedLayerCoordinates_face,coordDeriv_read_signed_normal hV,splitNormal]

theorem ContDiffBump.hasDerivAt_zero_at_center (η : ContDiffBump (0 : ℝ)) :
    HasDerivAt (fun t => η t) 0 0 := by
  refine (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) η.rIn_pos] with t ht
  exact η.one_of_mem_closedBall (Metric.ball_subset_closedBall ht)

private theorem conj_tangentialWave_mul (ξ : I n → ℝ) (h : ℝ) (y : Y) :
    (starRingEnd ℂ) (tangentialWave ξ h y) * tangentialWave ξ h y = 1 := by
  rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,norm_tangentialWave]
  simp

/-- The real and imaginary normal pairings remove the oscillatory
phase, leaving exactly the finite polynomial of trace coefficients. -/
theorem BoundaryLayerCoefficients.finiteWave_face_normalPairing
    {ξ : I n → ℝ} {U : Set Y} (B : BoundaryLayerCoefficients ξ U)
    (a : Y → ℂ) (η : ContDiffBump (0 : ℝ)) (N : ℕ) {h : ℝ} (hh : h ≠ 0) (y : Y) :
    let V := B.finiteWave a η N h
    let d := deriv (fun t => V (y,t)) 0
    h * ((V (y,0)).re * d.re + (V (y,0)).im * d.im) =
      ∑ j ∈ range (N+1), h ^ j * ((starRingEnd ℂ) (a y) * B.traceCoefficient a j y).re := by
  let V := B.finiteWave a η N h
  let w := tangentialWave ξ h y
  let d := deriv (fun t => V (y,t)) 0
  let T := ∑ j ∈ range (N+1), (h : ℂ) ^ j * B.traceCoefficient a j y
  have hη : η 0 = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall_self η.rIn_pos.le)
  have hv : V (y,0) = w * a y := B.finiteWave_face a η hη N h y
  have hd : (h : ℂ) * d = w * T := by
    have hDeriv := (B.hasDerivAt_finiteWave_normal a η (ContDiffBump.hasDerivAt_zero_at_center η)
      hη N h y).deriv
    change d = w * (T / (h : ℂ)) at hDeriv
    rw [hDeriv]
    field_simp [Complex.ofReal_ne_zero.mpr hh]
  have hprod : (h : ℂ) * ((starRingEnd ℂ) (V (y,0)) * d) = (starRingEnd ℂ) (a y) * T := by
    rw [mul_left_comm,hd,hv,map_mul]
    calc
      _ = ((starRingEnd ℂ) w * w) * ((starRingEnd ℂ) (a y) * T) := by ring
      _ = _ := by rw [conj_tangentialWave_mul,one_mul]
  have hsum : ((starRingEnd ℂ) (a y) * T).re =
      ∑ j ∈ range (N+1), h ^ j * ((starRingEnd ℂ) (a y) * B.traceCoefficient a j y).re := by
    unfold T
    rw [Finset.mul_sum]
    change Complex.reAddGroupHom _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change ((starRingEnd ℂ) (a y) * ((h : ℂ) ^ j * B.traceCoefficient a j y)).re = _
    rw [mul_left_comm]
    have he : (h : ℂ) ^ j = ((h ^ j : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  change h * ((V (y,0)).re * d.re + (V (y,0)).im * d.im) = _
  calc
    _ = ((h : ℂ) * ((starRingEnd ℂ) (V (y,0)) * d)).re := by
      rw [Complex.mul_re,Complex.mul_re]
      simp
    _ = _ := by rw [hprod,hsum]

end CalderonPatch.BoundaryLayer

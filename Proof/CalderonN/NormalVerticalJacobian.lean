module

public import Proof.CalderonN.NormalGeodesicVariation
public import Proof.CalderonN.NormalPullbackMetric

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Velocity-parameter derivative of the actual position and velocity. -/
def normalVelocityVariation (expMap : X dim × X dim → X dim) (y v u : X dim) (t : ℝ) : X dim × X dim :=
  fderiv ℝ (normalGeodesicPhase expMap y) (v,t) (u,0)

lemma NormalCoordinates.position_parameter_derivative {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
      normalVerticalJacobian expMap y (t • v) (t • u) := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,t • v)) (y,t • v) :=
    ((hReg.contDiffAt (hU.mem_nhds (hTube ⟨hy,hv⟩))).differentiableAt (by simp)).hasFDerivAt
  have hF : HasFDerivAt (fun p : (X dim) × ℝ => p.1) (ContinuousLinearMap.fst ℝ (X dim) ℝ) (v,t) := hasFDerivAt_fst
  have hS : HasFDerivAt (fun p : (X dim) × ℝ => p.2) (ContinuousLinearMap.snd ℝ (X dim) ℝ) (v,t) := hasFDerivAt_snd
  have hScaled : HasFDerivAt (fun p : (X dim) × ℝ => p.2 • p.1)
      (t • ContinuousLinearMap.fst ℝ (X dim) ℝ+(ContinuousLinearMap.snd ℝ (X dim) ℝ).smulRight v) (v,t) := hS.smul hF
  have hInput := (hasFDerivAt_const (𝕜:=ℝ) y (v,t)).prodMk hScaled
  have hd := hE.comp (v,t) hInput
  have hh := congrArg (fun L : ((X dim) × ℝ) →L[ℝ] (X dim) => L (u,0)) hd.fderiv
  change fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
    fderiv ℝ expMap (y,t • v) (0,t • u+(0:ℝ) • v) at hh
  simpa only [zero_smul,add_zero,normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply] using hh

lemma NormalCoordinates.variation_position_eq {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v u : (X dim)) (t : ℝ) (hv : t • v ∈ disk g y (R y)) :
    (normalVelocityVariation expMap y v u t).1 = normalVerticalJacobian expMap y (t • v) (t • u) := by
  have hPhase := hN.contDiffAt_phase hy (v,t) hv
  have hd := (hPhase.differentiableAt (by simp)).hasFDerivAt.fst
  have hh := congrArg (fun L : ((X dim) × ℝ) →L[ℝ] (X dim) => L (u,0)) hd.fderiv
  have hfst : fderiv ℝ (normalGeodesicPosition expMap y) (v,t) (u,0) =
      (normalVelocityVariation expMap y v u t).1 := hh
  exact hfst.symm.trans (hN.position_parameter_derivative hy v u t hv)

lemma NormalCoordinates.hasDerivAt_variation_position {Y Ω : Set (X dim)}
    (hΩ : IsOpen Ω) {K : ℝ} {g : MetricField dim} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X dim × X dim → X dim} {R : X dim → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X dim} (hy : y ∈ Y)
    (v u : X dim) (hv : v ∈ interior (disk g y (R y))) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s : ℝ => (normalVelocityVariation expMap y v u s).1)
      (normalVelocityVariation expMap y v u t).2 t := by
  let P := normalGeodesicPhase expMap y (v,t)
  let J := normalVelocityVariation expMap y v u t
  have hPos : P.1 ∈ Ω := hN.path_image hy v (interior_subset hv) ht
  have hspray := ((hg.contDiffAt_coordinateGeodesicSpray hΩ hK P hPos).differentiableAt (by simp)).hasFDerivAt
  have hd := hspray.fst.fderiv
  change fderiv ℝ (fun p : X dim × X dim => p.2) P =
    (ContinuousLinearMap.fst ℝ (X dim) (X dim)).comp (fderiv ℝ (coordinateGeodesicSpray g) P) at hd
  have h := congrArg (fun A : (X dim × X dim) →L[ℝ] X dim => A J) hd
  rw [fderiv_snd] at h
  change J.2 = (fderiv ℝ (coordinateGeodesicSpray g) P J).1 at h
  exact (hasDerivAt_prod_fst (hN.hasDerivAt_phase_variation hΩ hg hK hy v u hv ht)).congr_deriv h.symm

end CalderonN

import Proof.FramedRaisingHalfEndpoints
import Proof.PrincipalModelDegreeCoordinateWeights
import Proof.PrincipalModelRaisingCoordinateWeights
import Proof.FirstErrorCoordinateContraction
import Proof.DegreeHalfCovariantData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma frameTensor_single_operator_coordinate_contraction {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : MetricField) (e : Frame) (y : X)
    (hFrame : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (Q : Mat) (F : I → W) (b : I) :
    (∑ j : I,e y j b • (∑ i : I,frameTensorMatrix g e y Q i j •
      (∑ a : I,e y i a • F a)))=∑ a : I,Q a b • F a := by
  calc
    _ = ∑ a : I,(∑ i : I,∑ j : I,frameTensorMatrix g e y Q i j*e y i a*e y j b) • F a := by
      simp only [Fin.sum_univ_three]
      module
    _ = _ := by simp only [frameTensorMatrix_reconstruct g e y hFrame]

lemma Admissible.scaledFrameLogRadius_eq_radius_coordinate {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (i : I) :
    scaledFrameLogRadius d.radius d.frame i y=∑ a : I,d.frame y i a*coordDeriv a d.radius y := by
  have hdr := (hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)
  have hl := logRadius_derivative d.radius y (d.frame y i) hdr (hd.2.2.2.2.1.2 y hy).1.ne'
  have hRad : scaledFrameLogRadius d.radius d.frame i y=fderiv ℝ d.radius y (d.frame y i) := by
    rw [scaledFrameLogRadius,hl,← mul_assoc,mul_inv_cancel₀ (hd.2.2.2.2.1.2 y hy).1.ne',one_mul]
  rw [hRad]
  have hMap := congrArg (fderiv ℝ d.radius y) (axis_expansion (d.frame y i))
  simpa only [map_sum,map_smul,smul_eq_mul,coordDeriv] using hMap.symm

/-- The full model first-base coefficient in fixed coordinates consists
    of a scalar degree block and the actual inverse-metric perturbation
    against the physical raising family. -/
lemma Admissible.principalModelFirstDerivative_coordinate_eq {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) (b : I) :
    (∑ j : I,d.frame y j b • principalModelFirstDerivativeHalfL d y j)=
      principalModelDegreeCoordinateWeight d b y • degreeHalfL+
      ∑ a : I,principalModelRaisingCoordinateWeight d a b y • framedRaisingHalfL d y (axis a) := by
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  have hD (i : I) : scaledFrameLogRadius d.radius d.frame i y • degreeHalfL=
      ∑ a : I,d.frame y i a • (coordDeriv a d.radius y • degreeHalfL) := by
    rw [hd.scaledFrameLogRadius_eq_radius_coordinate hY hy i]
    simp only [Finset.sum_smul,smul_smul]
  have hDegree : (∑ j : I,d.frame y j b • (∑ i : I,
      ((q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y) • degreeHalfL))=
        principalModelDegreeCoordinateWeight d b y • degreeHalfL := by
    calc
      _ = ∑ j : I,d.frame y j b • (∑ i : I,(q i j+q j i) •
          (∑ a : I,d.frame y i a • (coordDeriv a d.radius y • degreeHalfL))) := by
        simp only [mul_smul,hD]
      _ = ∑ a : I,(principal d.γ d.g₂ y a b+principal d.γ d.g₂ y b a) •
          (coordDeriv a d.radius y • degreeHalfL) :=
        frameTensor_operator_coordinate_contraction d.γ d.frame y hFrame _ _ b
      _ = _ := by simp only [principalModelDegreeCoordinateWeight,Finset.sum_smul,smul_smul]
  let δQ := principal d.γ d.g₂ y-(d.γ y)⁻¹
  have hF (i : I) : flatHalfRaisingL i=∑ a : I,d.frame y i a • framedRaisingHalfL d y (axis a) :=
    (framedRaisingHalfL_frame d y hFrame i).symm.trans (framedRaisingHalfL_axis_expansion d y (d.frame y i))
  have hRaising : (∑ j : I,d.frame y j b • ((2:ℝ) •
      (∑ i : I,(q i j-(if i=j then 1 else 0)) • flatHalfRaisingL i)))=
        ∑ a : I,principalModelRaisingCoordinateWeight d a b y • framedRaisingHalfL d y (axis a) := by
    have hδ (i j : I) : frameTensorMatrix d.γ d.frame y δQ i j=q i j-(if i=j then 1 else 0) := by
      rw [frameTensorMatrix_sub,frameTensorMatrix_inverse_metric d.γ d.frame y hFrame]
    calc
      _ = (2:ℝ) • (∑ j : I,d.frame y j b • (∑ i : I,frameTensorMatrix d.γ d.frame y δQ i j •
          (∑ a : I,d.frame y i a • framedRaisingHalfL d y (axis a)))) := by
        simp only [hδ,hF,Fin.sum_univ_three]
        module
      _ = (2:ℝ) • (∑ a : I,δQ a b • framedRaisingHalfL d y (axis a)) := congrArg (fun v => (2:ℝ) • v)
        (frameTensor_single_operator_coordinate_contraction d.γ d.frame y hFrame δQ _ b)
      _ = _ := by simp only [principalModelRaisingCoordinateWeight,δQ,Finset.smul_sum,smul_smul]
  change (∑ j : I,d.frame y j b • ((∑ i : I,((q i j+q j i)*scaledFrameLogRadius d.radius d.frame i y) • degreeHalfL)+
    (2:ℝ) • (∑ i : I,(q i j-(if i=j then 1 else 0)) • flatHalfRaisingL i)))=_
  simp only [smul_add,Finset.sum_add_distrib,hDegree,hRaising]
end ShrinkingSpheres

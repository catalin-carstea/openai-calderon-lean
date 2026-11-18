import Proof.FramedNormalGauss
import Proof.RadialMatrixInverse
import Proof.FirstMetricNormalDensity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge

lemma NormalCoordinates.framedNormalMetric_radial_row {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame) (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (r : ℝ) (hr : r ≠ 0) (z : X)
    (hv : r • frameVector e y z ∈ interior (disk g y (R y))) (j : I) :
    ∑ i : I,z i*framedNormalMetric g e expMap y r z i j=z j := by
  have hh := hN.framedNormalMetric_gauss hΩ hg hK hy hyΩ e r hr z (axis j) hv
  rw [metricPair_frameVector g e y z (axis j) he] at hh
  simpa only [metricPair,axis,PiLp.single_apply,Pi.single_apply,mul_ite,ite_mul,mul_one,mul_zero,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_comm] using hh

lemma NormalCoordinates.framedNormal_principal_radial_row {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : X} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : Frame) (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (r : ℝ) (hr : r ≠ 0) (z : X)
    (hv : r • frameVector e y z ∈ interior (disk g y (R y)))
    (hDet : IsUnit (framedNormalMetric g e expMap y r z).det) (j : I) :
    ∑ i : I,z i*principalCoefficient (framedNormalMetric g e expMap y r) z i j=
      Real.sqrt (framedNormalMetric g e expMap y r z).det*z j := by
  have hInv := radial_row_inverse (framedNormalMetric g e expMap y r z) (fun i => z i) hDet
    (hN.framedNormalMetric_radial_row hΩ hg hK hy hyΩ e he r hr z hv)
  calc
    _ = Real.sqrt (framedNormalMetric g e expMap y r z).det*
      (∑ i : I,z i*(framedNormalMetric g e expMap y r z)⁻¹ i j) := by
      simp only [principalCoefficient,OAI.AnisotropicCalderon.vol,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := congrArg (fun q : ℝ => Real.sqrt (framedNormalMetric g e expMap y r z).det*q) (hInv j)
end ShrinkingSpheres

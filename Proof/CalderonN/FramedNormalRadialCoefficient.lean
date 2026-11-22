module

public import Proof.CalderonN.FramedNormalGauss
public import Proof.CalderonN.FirstMetricNormalDensity

import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Topology

namespace CalderonN

lemma radial_row_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℝ) (z : n → ℝ) (hDet : IsUnit G.det)
    (hRad : ∀ j,∑ i,z i*G i j=z j) :
    ∀ j,∑ i,z i*G⁻¹ i j=z j := by
  have hRow : Matrix.vecMul z G=z := funext hRad
  have hh := congrArg (fun w : n → ℝ => Matrix.vecMul w G⁻¹) hRow
  rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv G hDet,Matrix.vecMul_one] at hh
  exact congrFun hh.symm

variable {dim : ℕ} [NeZero dim]

lemma NormalCoordinates.framedNormalMetric_radial_row {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : (Frame dim)) (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (r : ℝ) (hr : r ≠ 0) (z : (X dim))
    (hv : r • frameVector e y z ∈ interior (disk g y (R y))) (j : (I dim)) :
    ∑ i : (I dim),z i*framedNormalMetric g e expMap y r z i j=z j := by
  have hh := hN.framedNormalMetric_gauss hΩ hg hK hy hyΩ e r hr z (axis j) hv
  rw [metricPair_frameVector g e y z (axis j) he] at hh
  simpa only [metricPair,axis,PiLp.single_apply,Pi.single_apply,mul_ite,ite_mul,mul_one,mul_zero,one_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_comm] using hh

lemma NormalCoordinates.framedNormal_divergence_radial_row {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) (hyΩ : y ∈ Ω)
    (e : (Frame dim)) (he : ∀ i j,metricPair g y (e y i) (e y j)=if i=j then 1 else 0)
    (r : ℝ) (hr : r ≠ 0) (z : (X dim))
    (hv : r • frameVector e y z ∈ interior (disk g y (R y)))
    (hDet : IsUnit (framedNormalMetric g e expMap y r z).det) (j : (I dim)) :
    ∑ i : (I dim),z i*divergenceCoeff (framedNormalMetric g e expMap y r) z i j=
      Real.sqrt (framedNormalMetric g e expMap y r z).det*z j := by
  have hInv := radial_row_inverse (framedNormalMetric g e expMap y r z) (fun i => z i) hDet
    (hN.framedNormalMetric_radial_row hΩ hg hK hy hyΩ e he r hr z hv)
  calc
    _ = Real.sqrt (framedNormalMetric g e expMap y r z).det*
      (∑ i : (I dim),z i*(framedNormalMetric g e expMap y r z)⁻¹ i j) := by
      simp only [divergenceCoeff,chartVolume,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = _ := congrArg (fun q : ℝ => Real.sqrt (framedNormalMetric g e expMap y r z).det*q) (hInv j)

end CalderonN

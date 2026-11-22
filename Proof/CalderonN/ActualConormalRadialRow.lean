module

public import Proof.CalderonN.FixedBallSmoothFlux
public import Proof.CalderonN.FirstMetricConormal
public import Proof.CalderonN.NormalCoefficientVelocityJets

import Proof.CalderonN.NormalizedVelocityAtZero
import Proof.CalderonN.NormalCenterBoundaryChainRule
import Proof.CalderonN.LinearMetric
import Mathlib.Tactic

/-! Gauss' radial row for the same coefficient used by the weak and strong
fixed-ball responses. -/

public section

noncomputable section
open Set Metric Matrix
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem framedNormalMetric_ref_posDef_of_frame {Y Ω : Set (X dim)} {m : ℕ}
    {K : ℝ} {R : X dim → ℝ} {M : Fin (m+1) → ℝ}
    {d : Data dim} {e : Frame dim} (hB : Background Ω K M d.γ d.g₁ d.g₂ e)
    (hN : NormalCoordinates Y Ω d.γ d.expMap R) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y)
    (he : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    (s : ℝ) (z : X dim)
    (hv : s • frameVector d.frame y z ∈ disk d.γ y (R y)) :
    (framedNormalMetric d.γ d.frame d.expMap y s z).PosDef := by
  let v := s • frameVector d.frame y z
  let J := normalVerticalJacobian d.expMap y v
  let T := J.comp (frameVectorLinear d.frame y)
  have hJ := hN.normalVerticalJacobian_isInvertible hy v hv
  have hF : Function.Bijective (frameVectorLinear d.frame y) := by
    simpa only [show ⇑(frameVectorLinear d.frame y) = frameVector d.frame y from
      funext (frameVectorLinear_apply d.frame y)] using bijective_frameVector d.γ d.frame y he
  have hT : Function.Bijective T := hJ.bijective.comp hF
  let E : X dim ≃L[ℝ] X dim := (LinearEquiv.ofBijective T.toLinearMap hT).toContinuousLinearEquiv
  have hE : E.toContinuousLinearMap = T := by
    ext x
    rfl
  have hD : (coordinateMatrix T).det ≠ 0 := by
    rw [← hE]
    exact coordinateMatrix_det_ne_zero E
  have hM (i j : I dim) : coordinateMatrix T i j = (J (d.frame y j)) i := by
    simp only [coordinateMatrix_apply,T,ContinuousLinearMap.comp_apply,frameVectorLinear_apply,frameVector_axis]
  have ha : framedNormalMetric d.γ d.frame d.expMap y s z =
      (coordinateMatrix T)ᵀ * d.γ (d.expMap (y,v)) * coordinateMatrix T := by
    ext a b
    simp only [Matrix.mul_apply,Matrix.transpose_apply,hM,framedNormalMetric,normalPullbackMetricPair,metricPair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [J,v,normalVerticalJacobian,ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
    ring
  have hx : d.expMap (y,v) ∈ Ω := ((hN.2 y hy).2.2 v hv).1
  rw [ha,← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact (hB.1.posDef hK hx).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hD)))

private theorem framedNormalMetric_ref_posDef {Y Ω : Set (X dim)} {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data dim} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (s : ℝ) (z : X dim)
    (hv : s • frameVector d.frame y z ∈ disk d.γ y (max ρ (d.radius y))) :
    (framedNormalMetric d.γ d.frame d.expMap y s z).PosDef :=
  framedNormalMetric_ref_posDef_of_frame hd.1 hd.2.1 hK hy
    (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) s z hv

theorem actualNormalCoeff_radial_row_of_frame (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K : ℝ} {R : X dim → ℝ}
    {M : Fin (m+1) → ℝ} {d : Data dim} {e : Frame dim}
    (hB : Background Ω K M d.γ d.g₁ d.g₂ e)
    (hN : NormalCoordinates Y Ω d.γ d.expMap R) (hK : 0 < K) {y : X dim} (hy : y ∈ Y)
    (he : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    {s : ℝ} (hs : s ≠ 0) (z : X dim)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (R y))) (j : Fin dim) :
    ∑ i, z i * firstNormalVelocityCoefficient d y (s • frameVector d.frame y z) i j =
      firstNormalRadialWeight d y s z * z j := by
  have hp := framedNormalMetric_ref_posDef_of_frame hB hN hK hy he s z (interior_subset hv)
  have hDet := isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  simp only [firstNormalVelocityCoefficient_rescaled]
  exact normalizedFirstNormalCoeff_radial_row_of_frame hn hΩ hB hN hK hy he hs z hv hDet j

theorem Admissible.actualNormalCoeff_radial_row (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X dim} (hy : y ∈ Y)
    {s : ℝ} (hs : s ≠ 0) (z : X dim)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y)))) (j : Fin dim) :
    ∑ i, z i * firstNormalVelocityCoefficient d y (s • frameVector d.frame y z) i j =
      firstNormalRadialWeight d y s z * z j := by
  have hp := framedNormalMetric_ref_posDef hd hK hy s z (interior_subset hv)
  have hDet := isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  simp only [firstNormalVelocityCoefficient_rescaled]
  exact hd.normalizedFirstNormalCoeff_radial_row hn hΩ hK hy hs z hv hDet j

theorem Admissible.inner_actualNormalFlux_radial_row (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X dim} (hy : y ∈ Y)
    {s : ℝ} (hs : s ≠ 0) (z : X dim)
    (hv : s • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ (d.radius y))))
    (u : X dim → ℝ) :
    ⟪z,smoothBallFlux (fun x => firstNormalVelocityCoefficient d y (s • frameVector d.frame y x)) u z⟫_ℝ =
      firstNormalRadialWeight d y s z * fderiv ℝ u z z := by
  have hp := framedNormalMetric_ref_posDef hd hK hy s z (interior_subset hv)
  have hDet := isUnit_iff_ne_zero.mpr hp.det_pos.ne'
  have h := hd.normalizedFirstNormalCoeff_conormal hn hΩ hK hy hs z hv hDet u
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,smoothBallFlux_apply,
    firstNormalVelocityCoefficient_rescaled,mul_comm] using h

end CalderonN

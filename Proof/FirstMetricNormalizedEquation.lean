import Proof.FirstMetricConformalConnection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

/-- Conformal normalization cancels the scalar in the principal tensor. -/
theorem Background.firstMetric_principal {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    principal γ g₁ x = (γ x)⁻¹ := by
  let κ := firstMetricConformalFactor γ g₁ x
  have hκ : κ ≠ 0 := (hB.firstMetricConformalFactor_pos hK hx).ne'
  letI : Invertible κ := invertibleOfNonzero hκ
  have hDet : IsUnit (γ x).det := isUnit_iff_ne_zero.mpr (hB.1.posDef hK hx).det_pos.ne'
  have hInv : (g₁ x)⁻¹ = κ⁻¹ • (γ x)⁻¹ := by
    rw [hB.firstMetric_eq_conformalFactor hK hx]
    exact (Matrix.inv_smul (γ x) κ hDet).trans (by rw [invOf_eq_inv])
  rw [principal,hInv,Matrix.mul_smul,Matrix.mul_nonsing_inv _ hDet,
    Matrix.trace_smul,Matrix.trace_one]
  simp only [Fintype.card_fin,Nat.cast_ofNat,smul_eq_mul,smul_smul]
  have hScalar : (3/(κ⁻¹*3))*κ⁻¹ = (1:ℝ) := by field_simp
  rw [hScalar,one_smul]

/-- Contraction of connection coefficients can be computed in any orthonormal frame. -/
lemma connection_difference_frame_contraction (γ g : MetricField) (e : Frame) (x : X)
    (he : ∀ i j, metricPair γ x (e x i) (e x j) = if i = j then 1 else 0) (k : I) :
    (∑ i, ∑ j, (γ x)⁻¹ i j*(christoffel γ x k i j-christoffel g x k i j)) =
      ∑ a, (connection γ x (e x a) (e x a)-connection g x (e x a) (e x a)) k := by
  rw [inverse_metric_of_frame γ e x he]
  simp only [connection,PiLp.sub_apply,WithLp.ofLp_toLp,Matrix.mul_apply,
    Matrix.transpose_apply,frameMatrix,Fin.sum_univ_three]
  ring

/-- In dimension three the normalized first-metric drift is minus the
    reference gradient of the canonical conformal depth. -/
theorem Background.firstMetric_drift {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (k : I) :
    drift γ g₁ x k = -(metricGradient e (firstMetricConformalDepth γ g₁) x) k := by
  let t := firstMetricConformalDepth γ g₁
  let V := metricGradient e t x
  have he := hB.2.2.2.2.2.2.2 x hx
  have hConn (a : I) : connection γ x (e x a) (e x a)-connection g₁ x (e x a) (e x a) =
      (2:ℝ) • (fderiv ℝ t x (e x a) • e x a)-V := by
    rw [hB.firstMetric_connection_eq hΩ hK hx,he a a,if_pos rfl,one_smul]
    module
  rw [drift,hB.firstMetric_principal hK hx,connection_difference_frame_contraction γ g₁ e x he k]
  simp_rw [hConn,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  have hV : ∑ a, fderiv ℝ t x (e x a)*e x a k = V k := by
    simp only [V,metricGradient,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hV]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change 2*V k-3*V k = -V k
  ring

/-- The genuine normalized first-metric equation, with no extra conformal premise. -/
theorem Background.firstMetric_normalized_laplace {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (u : X → ℝ) :
    laplace γ u x-∑ k, metricGradient e (firstMetricConformalDepth γ g₁) x k*coordDeriv k u x =
      (3/((γ x)*(g₁ x)⁻¹).trace)*laplace g₁ u x := by
  have h := normalized_laplace γ g₁ u x
  rw [hB.firstMetric_principal hK hx] at h
  simp_rw [hB.firstMetric_drift hΩ hK hx,neg_mul,Finset.sum_neg_distrib] at h
  exact h

end ShrinkingSpheres

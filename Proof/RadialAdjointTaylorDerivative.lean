import Proof.RadialAdjointForcingDerivative
import Proof.AdjointCancelledRemainderDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped Topology
namespace ShrinkingSpheres

/-- A genuine inverse and the exact first-adjoint identity turn forward and
    coefficient Taylor jets into the actual adjoint Taylor derivative bound. -/
theorem norm_radial_adjoint_taylor_derivative_le
    {P E H : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (M0 M01 : P → E →L[ℝ] E) (M1 M11 Inv : P → H →L[ℝ] H)
    (D D1 Da1 T Td : P → H →L[ℝ] E) (D0 : H →L[ℝ] E)
    (x : P) (U : Set P) (hU : IsOpen U) (hx : x ∈ U) (r C q : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hM0 : DifferentiableAt ℝ M0 x) (hM01 : DifferentiableAt ℝ M01 x)
    (hM1 : DifferentiableAt ℝ M1 x) (hM11 : DifferentiableAt ℝ M11 x)
    (hD : DifferentiableAt ℝ D x) (hD1 : DifferentiableAt ℝ D1 x)
    (hDa1 : DifferentiableAt ℝ Da1 x) (hT : DifferentiableAt ℝ T x)
    (hTd : DifferentiableAt ℝ Td x) (hInv : DifferentiableAt ℝ Inv x)
    (hInvertible : ∀ p ∈ U,(M1 p).IsInvertible)
    (hActualInv : ∀ p ∈ U,Inv p = (M1 p).inverse)
    (hFirst : ∀ p ∈ U,Da1 p = D1 p+(M01 p).comp D0-D0.comp (M11 p))
    (hNM0 : ‖M0 x‖ ≤ C) (hND0 : ‖D0‖ ≤ 2) (hND1 : ‖D1 x‖ ≤ C) (hNDa1 : ‖Da1 x‖ ≤ C)
    (hNJ : ‖D x-D0-r • D1 x‖ ≤ C*r^2)
    (hQ0 : ‖M0 x-ContinuousLinearMap.id ℝ E-r • M01 x‖ ≤ C*r^2)
    (hQ1 : ‖M1 x-ContinuousLinearMap.id ℝ H-r • M11 x‖ ≤ C*r^2)
    (hDel : ‖M0 x-ContinuousLinearMap.id ℝ E‖ ≤ C*r)
    (hNT : ‖T x‖ ≤ C*r^2) (hNTd : ‖Td x‖ ≤ C*r^2)
    (hNI : ‖Inv x‖ ≤ C) (hIDiff : ‖Inv x-ContinuousLinearMap.id ℝ H‖ ≤ C*r)
    (hDM0 : ‖fderiv ℝ M0 x‖ ≤ q*r) (hDM1 : ‖fderiv ℝ M1 x‖ ≤ q*r)
    (hDJ : ‖fderiv ℝ (fun p => D p-D0-r • D1 p) x‖ ≤ q*r^2)
    (hDQ0 : ‖fderiv ℝ (fun p => M0 p-ContinuousLinearMap.id ℝ E-r • M01 p) x‖ ≤ q*r^2)
    (hDQ1 : ‖fderiv ℝ (fun p => M1 p-ContinuousLinearMap.id ℝ H-r • M11 p) x‖ ≤ q*r^2)
    (hDD1 : ‖fderiv ℝ D1 x‖ ≤ q) (hDDa1 : ‖fderiv ℝ Da1 x‖ ≤ q)
    (hDT : ‖fderiv ℝ T x‖ ≤ q*r^2) (hDTd : ‖fderiv ℝ Td x‖ ≤ q*r^2) :
    ‖fderiv ℝ (fun p => ((M0 p).comp (D p)+T p-Td p).comp (Inv p)-D0-r • Da1 p) x‖ ≤
      radialAdjointJetBudget C*q*r^2 := by
  let F := fun p => radialAdjointTaylorForcing (M0 p) (M01 p) (M1 p) (M11 p) (D p) D0 (D1 p) (T p) (Td p) r
  have hF : DifferentiableAt ℝ F x := by
    unfold F radialAdjointTaylorForcing
    fun_prop
  have hNF := norm_radialAdjointTaylorForcing_le (M0 x) (M01 x) (M1 x) (M11 x)
    (D x) D0 (D1 x) (T x) (Td x) r C hr hC hNM0 hND0 hND1 hNJ hQ0 hQ1 hDel hNT hNTd
  have hDF := norm_radialAdjointTaylorForcing_derivative_le M0 M01 M1 M11 D D1 T Td D0 x r C q
    hr hr1 hC hq hM0 hM01 hM1 hM11 hD hD1 hT hTd hNM0 hND0 hND1 hNJ hDel hDM0 hDJ hDQ0 hDQ1 hDD1 hDT hDTd
  have hI : (fun p => (M1 p).comp (Inv p)) =ᶠ[𝓝 x] (fun _ : P => ContinuousLinearMap.id ℝ H) := by
    filter_upwards [hU.mem_nhds hx] with p hp
    rw [hActualInv p hp]
    exact (hInvertible p hp).self_comp_inverse
  have hNI' : ‖(M1 x).inverse‖ ≤ C := by rw [← hActualInv x hx];exact hNI
  have hDI := norm_operator_derivative_of_rectangular_left_identity M1 Inv
    (fun _ : P => ContinuousLinearMap.id ℝ H) x hM1 hInv hI (hInvertible x hx)
      C (q*r) C 0 hC (by positivity) hC le_rfl hNI' hDM1 hNI (by simp)
  have hDI' : ‖fderiv ℝ Inv x‖ ≤ C^2*q*r := hDI.trans_eq (by ring)
  have hIdentity : (fun p => ((M0 p).comp (D p)+T p-Td p).comp (Inv p)-D0-r • Da1 p) =ᶠ[𝓝 x]
      (fun p => (F p).comp (Inv p)+r • (Da1 p).comp (Inv p-ContinuousLinearMap.id ℝ H)) := by
    filter_upwards [hU.mem_nhds hx] with p hp
    apply radial_adjoint_taylor_cancellation
    · rw [hActualInv p hp]
      exact (hInvertible p hp).self_comp_inverse
    · exact hFirst p hp
  exact norm_adjoint_cancelled_remainder_derivative_le F Da1 _ Inv x r C q hr hr1 hC hq hF hDa1 hInv
    hIdentity hNF hDF hNI hDI' hIDiff hNDa1 hDDa1

end ShrinkingSpheres

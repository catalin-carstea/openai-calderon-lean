import Proof.CovariantHalfCoarseBridge
import Proof.BalancedCoarsePotential
import Proof.UniformActualFirstErrorCovariant
import Proof.UniformActualFirstAdjointEndpoints
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual covariant derivative in the Green formula inherits the
    existing uniform physical radius-beta estimate, for ANY already selected
    smooth low endpoint and compatible genuine higher endpoint. -/
theorem uniform_actual_first_error_half_covariant_derivative {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) → ∀ a : X,
      ∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ContDiffOn ℝ ∞ Lo Y →
      (∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
        (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) →
      (∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi x)=
        (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
        ‖halfOperatorCovariantDerivativeL d Lo Hi y b‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
  obtain ⟨η,CE,hη,hη1,hCE,hCov⟩ := uniform_actual_first_error_covariant hY hΩ hSub hm
    K ρ c₀ M Cj hK hρ
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG Lo Hi hLS hLow hHigh y hy b hb
  obtain ⟨S,hS,hSN⟩ := hCov floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG y hy b hb
  have hHS := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  have hCompat : ∀ᶠ x in 𝓝 y,
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
        (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hLow x hx
  have hEq := halfOperatorCovariantDerivativeL_eq_coarse (actualFirstAdjointErrorFamily d a A G) Lo Hi S
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hLS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hCompat (hHigh y hy) hS
  calc
    _ ≤ ‖S‖ := by
      rw [hEq]
      exact norm_balancedCoarsePotentialL_le S
    _ ≤ _ := hSN
end ShrinkingSpheres

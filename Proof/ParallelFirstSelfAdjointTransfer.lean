import Proof.ParallelFirstSelfNativeAdjointPacket
import Proof.ActualTrueAdjointHigherTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Transport only: the native packet is an abstract input, so no large
uniform selection term is unfolded while checking the physical graph. -/
theorem FirstSelfNativeAdjointPacket.physical_transfer
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} {K ρ c₀ floor ε CE : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y a : X} (hy : y ∈ Y) (q : FirstSelfNativeAdjointPacket Y Ω d y a CE ε)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAS : ContDiffOn ℝ ∞ A Y) (hGS : ContDiffOn ℝ ∞ G Y)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (Hi AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLS : ContDiffAt ℝ ∞ Lo y)
    (hLow : ∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (actualFirstAdjointErrorFamily d a A G x)=(Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hHigh : (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi y)=
      (actualFirstAdjointErrorFamily d a A G y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hAdj : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
      (Lo y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (b : X) (hb : ‖b‖ ≤ 1) :
    ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y b=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧
      ‖H‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖H‖ ≤ CE*‖a‖*ε := by
  obtain ⟨H,hH,hHN,hHE⟩ := q.jet b hb
  refine ⟨H,?_,hHN,hHE⟩
  exact NativeRelativeHorizontalTaylorData.true_adjoint_covariant_higher_transfer
    hY hΩ hSub hd hK hy q.native q.coefficients q.domain q.flat R A G hAS hGS hR hA hG
    Lo Hi AH hLS hLow hHigh hAdj b H hH

end ShrinkingSpheres.ParallelEnergy

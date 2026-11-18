import Proof.ParallelFirstSelfAdjointTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- ANY compatible actual physical true-adjoint higher family retains a
true higher covariant derivative with the original radius-beta/epsilon
bounds. The native degree graph supplies genuine adjoint regularity. -/
theorem uniform_actual_first_error_true_adjoint_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ _hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) →
      ∀ a : X,∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∀ Lo : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      ∀ Hi : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      ContDiffOn ℝ ∞ Lo Y →
      (∀ x ∈ Y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (actualFirstAdjointErrorFamily d a A G x)=
        (Lo x).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))) →
      (∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (Hi x)=
        (actualFirstAdjointErrorFamily d a A G x).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))) →
      ∀ AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      (∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH x)=
        (Lo x).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) →
      ∀ y ∈ Y,∀ b : X,‖b‖ ≤ 1 →
      ∃ L : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        halfOperatorCovariantDerivativeL d (fun x => (Lo x).adjoint) AH y b=
          (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp L ∧
        ‖L‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y ∧ ‖L‖ ≤ CE*‖a‖*ε := by
  obtain ⟨η,CE,hη,hη1,hCE,hPacket⟩ :=
    uniform_first_self_native_adjoint_packet hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CE,hη,hη1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG Lo Hi hLS hLow hHigh AH hAdj y hy b hb
  obtain ⟨q⟩ := hPacket floor hf ε hε hSmall d hd y hy a
  exact q.physical_transfer hY hΩ hSub hd (zero_lt_one.trans_le hK) hy R A G hAS hGS
    hR hA hG Lo Hi AH (hLS.contDiffAt (hY.mem_nhds hy)) hLow (hHigh y hy) (hAdj y hy) b hb

end ShrinkingSpheres.ParallelEnergy

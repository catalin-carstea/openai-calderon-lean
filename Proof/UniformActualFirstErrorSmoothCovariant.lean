import Proof.UniformActualFirstAdjointAngular
import Proof.CoarseCovariantJetFamily
import Proof.UniformActualFirstErrorCovariant
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- A globally smooth actual covariant derivative for the SAME physical error,
    linear in every physical direction, with a common radius-beta gain. -/
theorem uniform_actual_first_error_smooth_covariant {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ R A : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ A Y →
      (∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x)) →
      (∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ) → ∀ a : X,
      ∀ G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ContDiffOn ℝ ∞ G Y →
      (∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) →
      ∃ S : X → X →L[ℝ] (SphereSobolev 1 →L[ℝ] SphereSobolev 0),
        ContDiffOn ℝ ∞ S Y ∧ ∀ y ∈ Y,
          (∀ b : X,CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G) (S y b)) ∧
          ‖S y‖ ≤ CE*‖a‖*d.radius y*beta d.γ d.radius y := by
  classical
  obtain ⟨ηA,CA,hηA,hηA1,hCA,hAngular⟩ :=
    uniform_actual_first_adjoint_error_angular hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηC,CE,hηC,hηC1,hCE,hCov⟩ :=
    uniform_actual_first_error_covariant hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨min ηA ηC,CE,lt_min hηA hηC,(min_le_right _ _).trans hηC1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd R A hAS hR hA a G hGS hG
  have hSmallA := hSmall.trans (min_le_left _ _)
  have hSmallC := hSmall.trans (min_le_right _ _)
  choose C hCS hC using hAngular floor hf ε hε hSmallA d hd a R A G hR hA hG
  let E := actualFirstAdjointErrorFamily d a A G
  let S := coarseCovariantJetFamily d E C
  have hES : ContDiffOn ℝ ∞ E Y := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1
    (zero_lt_one.trans_le hK) hd.2.2.2.2.1.1 (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  refine ⟨S,contDiffOn_coarseCovariantJetFamily hY hΩ hSub d hd.1.1 (zero_lt_one.trans_le hK)
    hd.1.2.2.2.2.2.2.1 E C hES hCS,?_⟩
  intro y hy
  have hGraph (b : X) : CoarseCovariantRotationGraph d y b E (S y b) :=
    coarseCovariantJetFamily_graph d E C y b (fun i j => (hC i j y hy).2)
  refine ⟨hGraph,?_⟩
  have hβ : 0 ≤ beta d.γ d.radius y := zero_le_one.trans (hf.trans (hd.2.2.2.2.1.2 y hy).2.1)
  have hr : 0 ≤ d.radius y := (hd.2.2.2.2.1.2 y hy).1.le
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro b hb
  obtain ⟨T,hT,hTN⟩ := hCov floor hf ε hε hSmallC d hd R A hAS hR hA a G hGS hG y hy b hb.le
  have hEq := coarseCovariantRotationGraph_unique (hGraph b) hT
  exact (congrArg norm hEq).trans_le hTN
end ShrinkingSpheres

import Proof.UniformEffectiveFirstCovariantBalanced
import Proof.StrongHalfCovariantAdjoint
import Proof.EffectiveFirstCovariantCoarseBridge
import Proof.UniformEffectiveFirstAngularCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def EffectiveFirstBalancedDerivativeBound
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (W : PhysicalFirstCommutatorPacket P CB CS ε) (CE : ℝ) : Prop :=
  ∀ y ∈ Y,∀ b i : I,
    ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
    ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
      halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b)
          (P.firstCovariantCoordinateHigherL b) y (axis i)=
        L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
          (W.covariantCoordinateAdjointHigher b) y (axis i)=
        L.adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b)
          (P.firstCovariantCoordinateHigherL b) y (axis i)=
        (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧
      ‖L‖ ≤ CE*ε ∧ ‖L.adjoint‖ ≤ CE*ε ∧ ‖H‖ ≤ CE*ε

/-- The complete SAME effective first coefficient and the true adjoint
of ANY already selected physical packet retain genuine low AND higher-domain
covariant derivative bounds for the forward family, and a true-adjoint low extension. No test-dependent replacement is selected. -/
theorem uniform_effective_first_balanced_derivative_bound
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ W : PhysicalFirstCommutatorPacket P CB CS ε,EffectiveFirstBalancedDerivativeBound W CE := by
  obtain ⟨ηS,CE,hηS,hηS1,hCE,hStrong⟩ :=
    uniform_effective_first_covariant_balanced hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηB,hηB,hηB1,hBalanced⟩ :=
    uniform_full_first_derivative_balanced_endpoints hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets hY hΩ (by omega) K ρ c₀ M Cj hK
  refine ⟨min ηS ηB,CE,lt_min hηS hηB,(min_le_left _ _).trans hηS1,hCE,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P CB CS W
  have hε1 : ε ≤ 1 := hSmall.trans ((min_le_left _ _).trans hηS1)
  obtain ⟨S,hS⟩ := hStrong floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P
  have hW := hWeight floor hf ε hε hε1 d hd
  intro y hy b i
  obtain ⟨hSG,L,H,hSL,hSH,hLN,hHN⟩ := (hS b i).2 y hy
  have hWS : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y := (hW b).1
  have hC := P.firstCovariantCoordinateHalfL_smooth hd hY hΩ (zero_lt_one.trans_le hK) b hWS
  have hH : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y :=
    (P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ hSub (zero_lt_one.trans_le hK) b).sub
      (hWS.smul contDiffOn_const)
  have hRaw := P.firstDerivativeCoordinate_balanced y
    (hBalanced floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P y hy) b
  have hForward := P.firstCovariantCoordinateHigherL_balanced b y hRaw
  have hCoarse := P.firstCovariantCoordinate_covariant_eq_coarse hd hY hΩ (zero_lt_one.trans_le hK)
    b hWS hH hy (axis i) (P.firstCovariantCoordinateHigherL b) hForward (S b i y) hSG
  have hD : halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b)
      (P.firstCovariantCoordinateHigherL b) y (axis i)=
      L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
    rw [hCoarse]
    apply ContinuousLinearMap.ext
    intro u
    have hh := DFunLike.congr_fun hSL (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
    simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh
  have hA := half_covariant_adjoint_strong_extension d (P.firstCovariantCoordinateHalfL b)
    (P.firstCovariantCoordinateHigherL b) (W.covariantCoordinateAdjointHigher b)
    (hC.contDiffAt (hY.mem_nhds hy)) (axis i) hForward
    (W.covariantCoordinateAdjointHigher_balanced b hy) L hD
  have hDH : halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b)
      (P.firstCovariantCoordinateHigherL b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H := by
    rw [hCoarse]
    apply ContinuousLinearMap.ext
    intro u
    have hh := DFunLike.congr_fun hSH u
    simp only [ContinuousLinearMap.comp_apply] at hh
    change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (S b i y (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))=_
    rw [← hh,sphereSobolevInclusionL_trans_apply]
    rfl
  exact ⟨L,H,hD,hA,hDH,hLN,by simpa only [ContinuousLinearMap.adjoint.norm_map] using hLN,hHN⟩

end ShrinkingSpheres

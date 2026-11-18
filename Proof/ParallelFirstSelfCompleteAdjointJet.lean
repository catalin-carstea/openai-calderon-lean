import Proof.ParallelFirstSelfCompleteAdjointParts
import Proof.ParallelFirstSelfErrorCoordinateAdjointJet
import Proof.ParallelFirstSelfModelAdjointDerivative
import Proof.ParallelFirstSelfHalfLinearExtras
import Proof.UniformEffectiveFirstDerivativeProductIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.PrincipalCommutator

/-- Genuine HIGH first-covariant jets of the COMPLETE effective true
adjoint, for the already fixed physical WF. -/
structure FirstSelfCompleteAdjointJetBound
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (CE : ℝ) : Prop where
  jet : ∀ b i y,y ∈ Y → ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
    WF.effectiveAdjointCovariantDerivative b i y=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp H ∧ ‖H‖ ≤ CE*ε

/-- Model, geometric correction, native error and scalar drift are
assembled in their exact true-adjoint orientations. The SAME WF is retained;
no HIGH regularity is inferred from a forward norm or phantom carrier. -/
theorem uniform_complete_first_adjoint_covariant_higher
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {m : ℕ} (hm : 10 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CE : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CE ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ CF CT : ℝ,
      ∀ P : PhysicalPrincipalData Y d CF CT,∀ CB CS : ℝ,
      ∀ WF : PhysicalFirstCommutatorPacket P CB CS ε,FirstSelfCompleteAdjointJetBound WF CE := by
  obtain ⟨ηM,CM,hηM,hηM1,hCM,hModelJet⟩ := uniform_model_coordinate_first_jet_adjoint_higher
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηE,CErr,hηE,hηE1,hCErr,hError⟩ := uniform_actual_error_coordinate_adjoint_jet_packet
    hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  obtain ⟨CC,hCC,hCorrJet⟩ := uniform_correction_coordinate_true_adjoint_covariant_higher
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨CW,hCW,hWeight⟩ := uniform_scalar_principal_connection_two_jets
    hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨C0,hC0,hModel⟩ := uniform_principal_model_coordinate_data hY hΩ (by omega) K ρ c₀ M Cj hK
  obtain ⟨C1,hC1,hCorr⟩ := uniform_principal_first_correction_coordinate_data hY hΩ (by omega) K ρ c₀ M Cj hK
  let CE := CM+CC+CErr+CW
  refine ⟨min ηM ηE,CE,lt_min hηM hηE,(min_le_left _ _).trans hηM1,by dsimp only [CE];positivity,?_⟩
  intro floor hf ε hε hSmall d hd CF CT P CB CS WF
  have hε1 := (hSmall.trans (min_le_left _ _)).trans hηM1
  have hKpos := zero_lt_one.trans_le hK
  obtain ⟨Ep⟩ := hError floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd CF CT P
  let ML := fun (b : I) (x : X) => (principalModelCoordinateHalfL d x b).adjoint
  let CL := fun (b : I) (x : X) => (principalFirstCorrectionCoordinateHalfL d x b).adjoint
  let EL := fun (b : I) (x : X) => (P.first.principalFirstErrorCoordinateHalfL x b).adjoint
  let DL := fun (b : I) (x : X) => scalarPrincipalConnectionWeight d b x •
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let MH := completeAdjointModelHigherFamily WF Ep
  let CH := correctionCoordinateAdjointHigherL d
  let EH := Ep.higher
  let DH := fun (b : I) (x : X) => scalarPrincipalConnectionWeight d b x •
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Adj : (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) →L[ℝ]
      (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hMD (b : I) := hModel floor hf ε hε hε1 d hd b
  have hCD (b : I) := hCorr floor hf ε hε hε1 d hd b
  have hWD (b : I) := hWeight floor hf ε hε hε1 d hd b
  have hMS (b : I) : ContDiffOn ℝ ∞ (ML b) Y := Adj.contDiff.comp_contDiffOn (hMD b).1
  have hCS (b : I) : ContDiffOn ℝ ∞ (CL b) Y := Adj.contDiff.comp_contDiffOn (hCD b).1
  have hES (b : I) : ContDiffOn ℝ ∞ (EL b) Y := Ep.low_smooth b
  have hDS (b : I) : ContDiffOn ℝ ∞ (DL b) Y := (hWD b).1.smul contDiffOn_const
  refine ⟨?_⟩
  intro b i y hy
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  have hModelGraph := completeAdjointModelHigherFamily_graph WF Ep b hy hFrame
  have hModelPoint := principal_model_adjoint_covariant_eq_first_jet hY hΩ hd hKpos b i hy (MH b)
    ((hMD b).1.contDiffAt (hY.mem_nhds hy)) (((hMD b).2.2 y hy).1) hModelGraph
  obtain ⟨HM,hHM,hHMN⟩ := hModelJet floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd CF CT P b i y hy
  have hHM' : halfOperatorCovariantDerivativeL d (ML b) (MH b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp HM := hModelPoint.trans hHM.symm
  obtain ⟨HC,hHC,hHCN⟩ := hCorrJet floor hf ε hε hε1 d hd b (CH b) y hy
    (correctionCoordinateAdjointHigherL_graph d y hFrame b) i
  obtain ⟨HE,hHE,hHEN⟩ := Ep.jet b i y hy
  let HW := directionalFDeriv (axis i) (scalarPrincipalConnectionWeight d b) y •
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  have hHW : halfOperatorCovariantDerivativeL d (DL b) (DH b) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp HW :=
    half_covariant_scalar_inclusion_higher d (scalarPrincipalConnectionWeight d b) y (axis i)
      ((hWD b).1.contDiffAt (hY.mem_nhds hy))
  have hHWN : ‖HW‖ ≤ CW*ε := by
    have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
    exact (norm_scalar_higher_inclusion_le _).trans
      ((((hWD b).2 y hy i i).2.1).trans (div_le_self (mul_nonneg hCW hε) hβ))
  let T := HM+HC+HE-HW
  refine ⟨T,?_,?_⟩
  · change halfOperatorCovariantDerivativeL d (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)
      (WF.covariantCoordinateAdjointHigher b) y (axis i)=_
    have hLow : (fun x => (P.firstCovariantCoordinateHalfL b x).adjoint)=ᶠ[𝓝 y]
        (fun x => ML b x+CL b x+EL b x-DL b x) :=
      Eventually.of_forall (fun x => complete_first_adjoint_low_split P b x)
    rw [halfOperatorCovariantDerivativeL_congr_germ d _ _ (WF.covariantCoordinateAdjointHigher b) y (axis i) hLow,
      completeAdjointHigherFamily_split WF Ep b]
    rw [half_covariant_sub d (fun x => ML b x+CL b x+EL b x) (DL b)
      (fun x => MH b x+CH b x+EH b x) (DH b) y (axis i)
      ((((hMS b).add (hCS b)).add (hES b)).contDiffAt (hY.mem_nhds hy))
      ((hDS b).contDiffAt (hY.mem_nhds hy))]
    rw [halfOperatorCovariantDerivativeL_add d (fun x => ML b x+CL b x) (EL b)
      (fun x => MH b x+CH b x) (EH b) y (axis i)
      (((hMS b).add (hCS b)).contDiffAt (hY.mem_nhds hy)) ((hES b).contDiffAt (hY.mem_nhds hy)),
      halfOperatorCovariantDerivativeL_add d (ML b) (CL b) (MH b) (CH b) y (axis i)
      ((hMS b).contDiffAt (hY.mem_nhds hy)) ((hCS b).contDiffAt (hY.mem_nhds hy)),hHM',hHC,hHE,hHW]
    rw [ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_add]
  · have hN := (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hHMN hHCN)) hHEN)) hHWN)
    exact hN.trans_eq (by dsimp only [CE];ring)

end ShrinkingSpheres.ParallelEnergy

import Proof.RadialDilationAffineModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

/-- A dilation parameter packages all mixed relative-radius directions
    together with the original parameters in one quadratic remainder bound. -/
theorem exists_dilated_affine_residual_parameter_jet_bound
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (F : P × ℝ → V) (p : P) (δ : ℝ),0 ≤ δ → δ ≤ 1 →
      (∀ t : ℝ,|t| ≤ δ → ∃ U : Set (P × ℝ),IsOpen U ∧ (p,t) ∈ U ∧ ContDiffOn ℝ ∞ F U) →
      (∀ t : ℝ,|t| ≤ δ → ∀ j : ℕ,j ≤ n+2 → ‖iteratedFDeriv ℝ j F (p,t)‖ ≤ B) →
      ∀ r : ℝ,|r| ≤ δ →
      ‖iteratedFDeriv ℝ n (fun q : P × ℝ => radialAffineResidual F (q.1,(1+q.2)*r)) (p,0)‖ ≤ C*r^2 := by
  let N := n+2
  obtain ⟨D,hD,hInput⟩ := uniform_radialDilationInput_positive_jet_bounds (P:=P) N
  let C := 1+(N.factorial:ℝ)*B*D^N
  have hC : 1 ≤ C := by
    have hh : 0 ≤ (N.factorial:ℝ)*B*D^N := by positivity
    dsimp only [C]
    linarith only [hh]
  refine ⟨C,hC,?_⟩
  intro F p δ hδ hδ1 hLocal hBound r hr
  let G := radialDilationFamily F
  let q0 : P × ℝ := (p,0)
  have hGLocal (t : ℝ) (ht : |t| ≤ δ) :
      ∃ U : Set ((P × ℝ) × ℝ),IsOpen U ∧ (q0,t) ∈ U ∧ ContDiffOn ℝ ∞ G U := by
    obtain ⟨U,hU,hMem,hF⟩ := hLocal t ht
    refine ⟨radialDilationInput ⁻¹' U,hU.preimage contDiff_radialDilationInput.continuous,?_,?_⟩
    · change radialDilationInput ((p,0),t) ∈ U
      rwa [radialDilationInput_zero_parameter]
    · exact hF.comp contDiff_radialDilationInput.contDiffOn (fun x hx => hx)
  have hGBound (t : ℝ) (ht : |t| ≤ δ) : ‖iteratedFDeriv ℝ (n+2) G (q0,t)‖ ≤ C := by
    obtain ⟨U,hU,hMem,hF⟩ := hLocal t ht
    have hSmooth : ContDiffAt ℝ ∞ F (radialDilationInput (q0,t)) := by
      rw [show radialDilationInput (q0,t) = (p,t) from radialDilationInput_zero_parameter p t]
      exact hF.contDiffAt (hU.mem_nhds hMem)
    have hOuter (j : ℕ) (hj : j ≤ N) : ‖iteratedFDeriv ℝ j F (radialDilationInput (q0,t))‖ ≤ B := by
      rw [show radialDilationInput (q0,t) = (p,t) from radialDilationInput_zero_parameter p t]
      exact hBound t ht j hj
    have hh := iteratedFDeriv_comp_common_bound (radialDilationInput (P:=P)) F (q0,t)
      contDiff_radialDilationInput.contDiffAt hSmooth N B D hB hD hOuter
      (fun j hj hjN => hInput p t (ht.trans hδ1) j hj hjN) N le_rfl
    exact hh.trans (by change (N.factorial:ℝ)*B*D^N ≤ C;dsimp only [C];linarith)
  have hTaylor := norm_parameterJetField_sub_affine_of_local_joint_bound G q0 n δ C hδ
    (zero_le_one.trans hC) hGLocal hGBound r hr
  have h0 : |(0:ℝ)| ≤ δ := by simpa only [abs_zero] using hδ
  obtain ⟨U0,hU0,hMem0,hF0⟩ := hLocal 0 h0
  obtain ⟨V0,hV0,hVmem0,hG0⟩ := hGLocal 0 h0
  obtain ⟨Vr,hVr,hVmemr,hGr⟩ := hGLocal r hr
  have hGerm := radialAffineResidual_dilation_eq_germ F hU0 hF0 p hMem0 r
  rw [(hGerm.iteratedFDeriv ℝ n).eq_of_nhds]
  have hMemR : (q0,r) ∈ smoothOpenLocus G := ⟨Vr,hVr,hVmemr,hGr⟩
  have hMemZero : (q0,0) ∈ smoothOpenLocus G := ⟨V0,hV0,hVmem0,hG0⟩
  change ‖iteratedFDeriv ℝ n (fun q => G (q,r)-G (q,0)-r • radialFirstDerivative G (q,0)) q0‖ ≤ C*r^2
  rw [iteratedFDeriv_parameter_affine_remainder_eq G (isOpen_smoothOpenLocus G)
    (contDiffOn_smoothOpenLocus G) q0 r hMemR hMemZero n]
  exact hTaylor

end ShrinkingSpheres

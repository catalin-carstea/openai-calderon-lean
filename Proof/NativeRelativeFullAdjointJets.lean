import Proof.UniformNativeRelativeHorizontalTaylorData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The full genuine adjoint family, before subtracting its flat and first
    Taylor terms. -/
def NormalFrameRelativeResponsePacket.fullAdjoint
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C}
    (s : NormalFrameRelativeResponsePacket q) (p : NormalFrameRelativeParameter) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  radialAdjointFromResponseL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p)
    (s.response p+sphereSobolevDegreeL)

/-- All ordinary finite jets of the full adjoint have a coarse common bound
    from the SAME Taylor remainder and scalar first-model data. -/
theorem NormalFrameRelativeResponsePacket.full_adjoint_jet_bound
    {Y Ω : Set X} {d : Data} {y : X} (N : ℕ) {Z C CA : ℝ}
    {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) (N+1) Z C}
    (s : NormalFrameRelativeResponsePacket q) (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCA : 0 ≤ CA)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (hTaylor : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n s.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2) :
    ContDiffAt ℝ ∞ s.fullAdjoint ((y,frameVectorLinear d.frame y),0) ∧
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n s.fullAdjoint ((y,frameVectorLinear d.frame y),0)‖ ≤
      ‖sphereSobolevDegreeL‖+6*C+CA := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let ell := normalFrameRelativeFirstCovector d.γ d.g₁
  let B := fun p => radialCorrectionCovectorL (ell p)
  let BA := fun p => (B p).adjoint
  let Incl := sphereSobolevInclusionL 1 0 (by norm_num)
  let A1 := fun p => (BA p).comp Incl
  let Adj := (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0))
  have hEll : ContDiffAt ℝ ∞ ell p0 := q.covectorSmooth.contDiffAt (q.domainOpen.mem_nhds q.pointMem)
  have hB : ContDiffAt ℝ ∞ B p0 := radialCorrectionCovectorL.contDiff.contDiffAt.comp p0 hEll
  have hBA : ContDiffAt ℝ ∞ BA p0 := Adj.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=B) p0 hB
  have hA1 : ContDiffAt ℝ ∞ A1 p0 := hBA.clm_comp contDiffAt_const
  have hBJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n B p0‖ ≤ 6*C :=
    (norm_iteratedFDeriv_clm_comp_le radialCorrectionCovectorL ell p0 hEll n).trans
      ((mul_le_mul norm_radialCorrectionCovectorL_le (q.firstCovectorJets hZ n hn) (norm_nonneg _) (by norm_num)).trans_eq (by ring))
  have hBAJ (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n BA p0‖ ≤ 6*C := by
    change ‖iteratedFDeriv ℝ n (Adj ∘ B) p0‖ ≤ _
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hBJ n hn
  have hA1J (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n A1 p0‖ ≤ 6*C :=
    (norm_iteratedFDeriv_operator_precomp_fixed_le BA Incl p0 hBA n).trans
      ((mul_le_mul (norm_sphereSobolevInclusionL_le 1 0 (by norm_num)) (hBAJ n hn)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hEq : s.fullAdjoint = fun p => (s.adjointTaylor p+sphereSobolevDegreeL)+d.radius y • A1 p := by
    funext p
    change s.fullAdjoint p = (s.fullAdjoint p-sphereSobolevDegreeL-d.radius y • A1 p+sphereSobolevDegreeL)+d.radius y • A1 p
    abel
  have hT := s.contDiffAt_adjointTaylor
  refine ⟨s.adjointSmooth.contDiffAt (s.domainOpen.mem_nhds s.pointMem),?_⟩
  intro n hn
  rw [hEq]
  have hConst : ‖iteratedFDeriv ℝ n (fun _ : NormalFrameRelativeParameter => sphereSobolevDegreeL) p0‖ ≤ ‖sphereSobolevDegreeL‖ := by
    cases n with
    | zero => simp only [norm_iteratedFDeriv_zero,le_refl]
    | succ n => simpa only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n),Pi.zero_apply,norm_zero] using norm_nonneg sphereSobolevDegreeL
  have hOne : (d.radius y)^2 ≤ 1 := by nlinarith only [hr,hr1]
  have hTJ : ‖iteratedFDeriv ℝ n s.adjointTaylor p0‖ ≤ CA :=
    (hTaylor n hn).trans ((mul_le_mul_of_nonneg_left hOne hCA).trans_eq (mul_one _))
  have hScaled : ‖iteratedFDeriv ℝ n (fun p => d.radius y • A1 p) p0‖ ≤ 6*C := by
    rw [norm_iteratedFDeriv_const_smul_at A1 p0 hA1 (d.radius y) n,abs_of_nonneg hr]
    exact (mul_le_mul hr1 (hA1J n hn) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hh := norm_iteratedFDeriv_add_at_le (fun p => s.adjointTaylor p+sphereSobolevDegreeL)
    (fun p => d.radius y • A1 p) p0 (hT.add contDiffAt_const) (hA1.const_smul (d.radius y)) n
  exact hh.trans ((add_le_add ((norm_iteratedFDeriv_add_at_le s.adjointTaylor
    (fun _ => sphereSobolevDegreeL) p0 hT contDiffAt_const n).trans (add_le_add hTJ hConst)) hScaled).trans_eq (by ring))

end ShrinkingSpheres

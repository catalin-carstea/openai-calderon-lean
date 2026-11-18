import Proof.UniformFlatRaisingConstantAdjointHigher
import Proof.StrongHalfCovariantAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Background raising has a genuine strong half-domain covariant jet.
This reuses the actual coarse graph and the checked SAME half extension;
no bound on derivatives of the arbitrary moving frame is introduced. -/
lemma framed_raising_strong_half_graph {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (i b : I) :
    halfOperatorCovariantDerivativeL d
      (fun x => framedRaisingHalfL d x (axis b)) (fun x => framedRaisingHigherL d x (axis b)) y (axis i)=
      (framedRaisingFirstHalfJet d i b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hSmooth := hd.framedRaisingHalf_smooth (axis b)
  have hCoarse := halfOperatorCovariantDerivativeL_eq_coarse
    (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x (axis b))
    (fun x => framedRaisingHalfL d x (axis b))
    (fun x => framedRaisingHigherL d x (axis b)) (framedRaisingFirstCoarseJet d i b y)
    ((hSmooth.2.2.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hSmooth.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (Eventually.of_forall (fun x => framedRaisingHalfL_coarse d x (axis b)))
    (framedRaisingHigherL_coarse d y (axis b))
    (hd.framedRaising_first_second_covariant_graphs hY hΩ hK hy i i b).1
  rw [hCoarse]
  apply ContinuousLinearMap.ext
  intro u
  have hh := DFunLike.congr_fun (framedRaisingFirstHalfJet_coarse d i b y)
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh

/-- A sharp scalar times a symmetric background angular coefficient has
exactly the epsilon/beta scale needed by the generic third-base reduction. -/
lemma symmetric_background_weighted_jet_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R D : E →L[ℝ] E) (w dw A0 A1 QR QD ε β : ℝ)
    (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1) (hQR : 0 ≤ QR) (hQD : 0 ≤ QD)
    (hε : 0 ≤ ε) (hβ : 1 ≤ β) (hR : ‖R‖ ≤ QR) (hD : ‖D‖ ≤ QD)
    (hw : |w| ≤ A0*ε/β^2) (hdw : |dw| ≤ A1*ε/β) :
    ‖w • (R+R.adjoint)‖ ≤ (2*A0*QR)*ε/β ∧
    ‖dw • (R+R.adjoint)+w • (D+D.adjoint)‖ ≤ (2*A1*QR+2*A0*QD)*ε/β := by
  have hβP := zero_lt_one.trans_le hβ
  have hInv : 1/β^2 ≤ 1/β := by
    have h := mul_le_mul_of_nonneg_left hβ (inv_nonneg.mpr hβP.le)
    have hβN : β ≠ 0 := hβP.ne'
    field_simp at h ⊢
    nlinarith only [hβ]
  have hw1 : |w| ≤ A0*ε/β := hw.trans (by
    simpa only [div_eq_mul_inv,mul_assoc,one_mul] using mul_le_mul_of_nonneg_left hInv (mul_nonneg hA0 hε))
  have hsR : ‖R+R.adjoint‖ ≤ 2*QR := by
    calc
      _ ≤ ‖R‖+‖R.adjoint‖ := norm_add_le _ _
      _ = 2*‖R‖ := by rw [ContinuousLinearMap.adjoint.norm_map];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hR (by norm_num)
  have hsD : ‖D+D.adjoint‖ ≤ 2*QD := by
    calc
      _ ≤ ‖D‖+‖D.adjoint‖ := norm_add_le _ _
      _ = 2*‖D‖ := by rw [ContinuousLinearMap.adjoint.norm_map];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by norm_num)
  constructor
  · rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul hw1 hsR (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · calc
      _ ≤ ‖dw • (R+R.adjoint)‖+‖w • (D+D.adjoint)‖ := norm_add_le _ _
      _ = |dw| *‖R+R.adjoint‖+|w| *‖D+D.adjoint‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ (A1*ε/β)*(2*QR)+(A0*ε/β)*(2*QD) :=
        add_le_add (mul_le_mul hdw hsR (norm_nonneg _) (by positivity))
          (mul_le_mul hw1 hsD (norm_nonneg _) (by positivity))
      _ = _ := by ring

end ShrinkingSpheres.ParallelEnergy

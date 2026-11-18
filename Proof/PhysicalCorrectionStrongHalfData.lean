import Proof.BoundedCorrectionStrongHalf
import Proof.StrongHalfCovariantDirectionAssembly
import Proof.PhysicalCorrectionCoframeData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.physicalFirstCorrection_strong_half_frame_extension
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (i b : I) :
    halfOperatorCovariantDerivativeL d
      (fun x => physicalFirstCorrectionHalfL d x (axis b))
      (fun x => physicalFirstCorrectionHigherL d x (axis b)) y (d.frame y i)=
    (halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d y (d.frame y i) (axis b))).comp
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hCS : ContDiffOn ℝ ∞ (physicalFirstCorrectionCoarseFamily d (axis b)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK 0 (axis b)).clm_comp contDiffOn_const
  have hLS : ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionHalfL d x (axis b)) Y :=
    (hd.contDiffOn_physicalFirstCorrectionAtL hY hΩ hK (-(1/2:ℝ)) (axis b)).clm_comp contDiffOn_const
  have hStrong : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (physicalFirstCorrectionCovariantJetL d y (d.frame y i) (axis b))=
      (halfLiftOfBoundedL2Operator (physicalFirstCorrectionBoundedCovariantJetL d y (d.frame y i) (axis b))).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    rw [← physicalFirstCorrectionBoundedCovariantJetL_coarse]
    exact halfLiftOfBoundedL2Operator_coarse _
  exact halfOperatorCovariantDerivativeL_eq_strong_extension
    (physicalFirstCorrectionCoarseFamily d (axis b))
    (fun x => physicalFirstCorrectionHalfL d x (axis b))
    (fun x => physicalFirstCorrectionHigherL d x (axis b)) _ _
    ((hCS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((hLS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (Eventually.of_forall (fun x => physicalFirstCorrectionHalfL_coarse d x (axis b)))
    (physicalFirstCorrectionHigherL_coarse d y (axis b))
    (hd.physicalFirstCorrection_covariant_graph hY hΩ hK hy (d.frame y i) (axis b)) hStrong

/-- The bounded geometric correction retains an actual strong half-domain
covariant extension in every physical coordinate direction. -/
theorem uniform_physical_first_correction_strong_half_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ b i : I,
      ∃ L : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        halfOperatorCovariantDerivativeL d
          (fun x => physicalFirstCorrectionHalfL d x (axis b))
          (fun x => physicalFirstCorrectionHigherL d x (axis b)) y (axis i)=
          L.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧ ‖L‖ ≤ Q := by
  let CJ := physicalFirstCorrectionJetBudget K (M 0) (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2)
  let Q := 3*K*CJ
  have hCJ : 0 ≤ CJ := physicalFirstCorrectionJetBudget_nonneg _ _ _ _ _ (zero_le_one.trans hK)
  refine ⟨Q,by dsimp only [Q];positivity,?_⟩
  intro floor hf ε hε hε1 d hd y hy b i
  let L := fun j : I => halfLiftOfBoundedL2Operator
    (physicalFirstCorrectionBoundedCovariantJetL d y (d.frame y j) (axis b))
  have hL (j : I) := hd.physicalFirstCorrection_strong_half_frame_extension hY hΩ (zero_lt_one.trans_le hK) hy j b
  have hLN (j : I) : ‖L j‖ ≤ CJ := (norm_halfLiftOfBoundedL2Operator_le _).trans
    (hd.norm_physicalFirstCorrectionBoundedCovariantJetL_frame_le hY hΩ hm hK hf hε hε1 hy j b)
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun a c => (hd.1.1.1 a c).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  exact exists_strong_half_covariant_axis_extension d hg hK hy (hd.1.2.2.2.2.2.2.2 y (hSub hy))
    (fun x => physicalFirstCorrectionHalfL d x (axis b))
    (fun x => physicalFirstCorrectionHigherL d x (axis b)) L hL CJ hLN i

end ShrinkingSpheres

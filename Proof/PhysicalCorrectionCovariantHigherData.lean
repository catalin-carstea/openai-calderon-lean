import Proof.CovariantCorrectionGradedJets
import Proof.PhysicalCorrectionCoframeData
import Proof.PhysicalFirstCorrectionSmoothCovariant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def physicalFirstCorrectionCovariantHigherFrameL (d : Data) (y : X) (i b : I) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (physicalFirstCorrectionCovariantJetAtL (1/2:ℝ) d y (d.frame y i) (axis b)).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

lemma physicalFirstCorrectionCovariantHigherFrameL_coarse (d : Data) (y : X) (i b : I) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
      (physicalFirstCorrectionCovariantHigherFrameL d y i b)=
    (physicalFirstCorrectionCovariantJetL d y (d.frame y i) (axis b)).comp
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (physicalFirstCorrectionCovariantJetAtL (1/2:ℝ) d y (d.frame y i) (axis b)
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=_
  rw [physicalFirstCorrectionCovariantJetAtL_inclusion,
    physicalFirstCorrectionCovariantJetAtL_zero]
  have h := DFunLike.congr_fun
    (physicalFirstCorrectionBoundedCovariantJetL_coarse d y (d.frame y i) (axis b))
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using h

/-- The actual smooth coarse correction jet has a genuine higher endpoint
in each physical coordinate direction. The constant precedes all profiles. -/
theorem uniform_physical_first_correction_covariant_higher_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) :
    ∃ Q : ℝ,0 ≤ Q ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ 1 → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ y ∈ Y,∀ b i : I,
      ∃ H : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ),
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
          (physicalFirstCorrectionCovariantFamily d (axis b) y (axis i)).comp
            (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) ∧ ‖H‖ ≤ Q := by
  classical
  obtain ⟨CT,hCT,hBound⟩ := uniform_physical_correction_covariant_grade_bound
    hY hΩ (1/2:ℝ) hm K ρ c₀ M Cj hK
  refine ⟨3*K*CT,by positivity,?_⟩
  intro floor hf ε hε hε1 d hd y hy b i
  have hKpos := zero_lt_one.trans_le hK
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hg : Elliptic Y K d.γ :=
    ⟨fun a c => (hd.1.1.1 a c).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hSub hy)
  let V := physicalFirstCorrectionCovariantFamily d (axis b) y
  let c := fun j => frameCoordinateLinear d.γ d.frame y j (axis i)
  let H := ∑ j : I,c j • physicalFirstCorrectionCovariantHigherFrameL d y j b
  have hSame (j : I) : V (d.frame y j)=
      physicalFirstCorrectionCovariantJetL d y (d.frame y j) (axis b) :=
    coarseCovariantRotationGraph_unique
      ((hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hKpos (axis b)).2
        y hy (d.frame y j))
      (hd.physicalFirstCorrection_covariant_graph hY hΩ hKpos hy (d.frame y j) (axis b))
  have hMap := congrArg V (frameCoordinateLinear_reconstruct d.γ d.frame y (axis i) hFrame)
  have hAxis : V (axis i)=∑ j : I,c j • V (d.frame y j) := by
    simpa only [map_sum,map_smul] using hMap.symm
  refine ⟨H,?_,?_⟩
  · change (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp H=
      (V (axis i)).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num))
    rw [hAxis]
    apply ContinuousLinearMap.ext
    intro u
    have hEach (j : I) := DFunLike.congr_fun (physicalFirstCorrectionCovariantHigherFrameL_coarse d y j b) u
    simp only [ContinuousLinearMap.comp_apply] at hEach
    simp only [H,ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,
      map_sum,map_smul,hEach,hSame]
  · apply norm_weighted_sum_three_le _ _ K CT (zero_le_one.trans hK)
    · intro j
      dsimp only [c]
      rw [frameCoordinateLinear_apply]
      exact hg.frame_coordinate_abs_bound hK d.frame hy hFrame i j
    · intro j
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans
          ((mul_one _).le.trans (hBound floor hf ε hε hε1 d hd y hy j b)))

end ShrinkingSpheres

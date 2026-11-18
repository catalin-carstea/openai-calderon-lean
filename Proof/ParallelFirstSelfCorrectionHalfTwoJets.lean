import Proof.ParallelFirstSelfCorrectionHalfGraph
import Proof.ParallelFirstSelfCorrectionNativeHalfJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

lemma correctionNativeHalfFamily_actual_point {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (b : X) :
    physicalFirstCorrectionHalfL d y b=
      correctionNativeHalfFamily d (d.radius y) b ((y,frameVectorLinear d.frame y),0) := by
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hPoint : physicalFirstCorrectionCoarseFamily d b y=
      nativePhysicalFirstCorrectionFamily d (d.radius y) b ((y,frameVectorLinear d.frame y),0) := by
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using
      (hd.nativePhysicalFirstCorrectionFamily_actual_germ hY hΩ hSub hK (d.radius y) hr0 hy b).eq_of_nhds
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  have hL := physicalFirstCorrectionHalfL_coarse d y b
  rw [hPoint] at hL
  exact hL.symm.trans (correctionNativeHalfFamily_coarse d (d.radius y) b _)

/-- The actual primitive geometric correction has ONE smooth first
strong-half family and compatible second covariant jets with beta squared
control. Constants are chosen before all profiles, frames, and centers. -/
theorem uniform_correction_strong_half_two_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ C ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ b i : I,
      ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionCovariantFamily d (axis b) x (axis i)) Y ∧
      ContDiffOn ℝ ∞ (correctionHalfCovariantFamily d (axis b) (axis i)) Y ∧ ∀ y ∈ Y,
      CoarseCovariantRotationGraph d y (axis i) (physicalFirstCorrectionCoarseFamily d (axis b))
        (physicalFirstCorrectionCovariantFamily d (axis b) y (axis i)) ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
        (physicalFirstCorrectionCovariantFamily d (axis b) y (axis i))=
        (correctionHalfCovariantFamily d (axis b) (axis i) y).comp
          (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      ‖physicalFirstCorrectionHalfL d y (axis b)‖ ≤ C ∧
      ‖correctionHalfCovariantFamily d (axis b) (axis i) y‖ ≤ C*beta d.γ d.radius y ∧
      ∀ j : I,∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        CoarseCovariantRotationGraph d y (axis j)
          (fun x => physicalFirstCorrectionCovariantFamily d (axis b) x (axis i)) T ∧
        (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
          N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
        ‖N‖ ≤ C*(beta d.γ d.radius y)^2 := by
  obtain ⟨η,C,hη,hη1,hC,hHorizontal⟩ :=
    uniform_correction_native_half_horizontal_two_jets hY hΩ hSub hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd b i
  have hKpos := zero_lt_one.trans_le hK
  have hS := hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hKpos (axis b)
  refine ⟨hS.1.clm_apply contDiffOn_const,
    correctionHalfCovariantFamily_smooth hY hΩ hSub hd hKpos (axis i) (axis b),?_⟩
  intro y hy
  obtain ⟨h0,h1,h2⟩ := hHorizontal floor hf ε hε hSmall d hd y hy (axis b)
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hFirst : correctionHalfCovariantFamily d (axis b) (axis i) y=
      fderiv ℝ (correctionNativeHalfFamily d (d.radius y) (axis b)) ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius (axis i) ((y,frameVectorLinear d.frame y),0)) := by
    simpa only [normalFrameRelativeActualParameter_point d y hr0] using
      (correctionHalfCovariantFamily_native_germ hY hΩ hSub hd hKpos (d.radius y) hr0 hy (axis i) (axis b)).eq_of_nhds
  refine ⟨hS.2 y hy (axis i),correctionHalfCovariantFamily_coarse hY hΩ hSub hd hKpos hy (axis i) (axis b),?_,?_,?_⟩
  · rw [correctionNativeHalfFamily_actual_point hY hΩ hSub hd hKpos hy]
    simpa only [norm_axis,mul_one] using h0
  · rw [hFirst]
    simpa only [norm_axis,mul_one] using h1 (axis i) (by simp only [norm_axis,le_refl])
  · intro j
    have hGraph := correctionHalfCovariantFamily_second_graph hY hΩ hSub hd hKpos hy (axis i) (axis j) (axis b)
    refine ⟨_,_,hGraph.1,hGraph.2,?_⟩
    simpa only [norm_axis,mul_one] using h2 (axis i) (axis j)
      (by simp only [norm_axis,le_refl]) (by simp only [norm_axis,le_refl])

end ShrinkingSpheres.ParallelEnergy

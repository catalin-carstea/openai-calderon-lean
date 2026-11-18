import Proof.NativeFirstCorrectionRotationGraph
import Proof.PhysicalFirstCorrectionSmoothCovariant
import Proof.CoarseHorizontalCovariantGerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma Admissible.physicalFirstCorrectionCovariantFamily_eq_native_horizontal {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a b : X) :
    physicalFirstCorrectionCovariantFamily d b y a =
      fderiv ℝ (nativePhysicalFirstCorrectionFamily d (d.radius y) b) ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius a ((y,frameVectorLinear d.frame y),0)) := by
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hD := isOpen_nativeFirstCorrectionDomain hY hΩ
  have hp := hd.1.nativeFirstCorrectionDomain_actual_parameter hSub (d.radius y) hy
  have hF := hd.nativePhysicalFirstCorrectionFamily_smooth hY hΩ hK (d.radius y) b
  have hFrame (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i j
  have heS := hd.1.2.2.2.2.2.2.1
  have heF := hd.1.2.2.2.2.2.2.2
  have hE (i : I) := (heS i).contDiffAt (hΩ.mem_nhds (hSub hy))
  have hL := (contDiffAt_frameVectorLinear d.frame y hE).differentiableAt (by simp)
  have hFPoint := (hF.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp)
  have hNative := fixed_relative_covariant_rotation_graph_of_germ d (d.radius y) y a
    (physicalFirstCorrectionCoarseFamily d b) (nativePhysicalFirstCorrectionFamily d (d.radius y) b)
    (hd.nativePhysicalFirstCorrectionFamily_actual_germ hY hΩ hSub hK (d.radius y) hr0 hy b)
    ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hr0 hL
    (fun i => (hE i).differentiableAt (by simp)) (heF y (hSub hy))
    (frameConnection_skew hΩ hd.1.1 hK d.frame heS heF (hSub hy) a) hFPoint
    (fun i j u => by
      have hFix := normalFrameRelativeNormalization_eq_self d.γ
        (normalFrameRelativeActualParameter d (d.radius y) y) hFrame
      have hFD : DifferentiableAt ℝ (nativePhysicalFirstCorrectionFamily d (d.radius y) b)
          (normalFrameRelativeNormalization d.γ (normalFrameRelativeActualParameter d (d.radius y) y)) := by
        rw [hFix]
        exact hFPoint
      exact nativePhysicalFirstCorrection_normalized_rotation_graph hΩ d hd.1.1 hK (d.radius y) b _ hp.1 hFrame hFD i j u)
  have hSame := coarseCovariantRotationGraph_unique
    ((hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK b).2 y hy a) hNative
  simpa only [normalFrameRelativeActualParameter_point d y hr0] using hSame

/-- The actual correction's second covariant graph is the second ordered
horizontal derivative of its SAME native family. -/
theorem Admissible.physicalFirstCorrection_second_covariant_graph {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a c b : X) :
    CoarseCovariantRotationGraph d y c (fun x => physicalFirstCorrectionCovariantFamily d b x a)
      (fderiv ℝ (fun p => fderiv ℝ (nativePhysicalFirstCorrectionFamily d (d.radius y) b) p
        (normalFrameRelativeHorizontalField d.γ d.radius a p)) ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius c ((y,frameVectorLinear d.frame y),0))) := by
  have hr0 := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hD := isOpen_nativeFirstCorrectionDomain hY hΩ
  have hp := hd.1.nativeFirstCorrectionDomain_actual_parameter hSub (d.radius y) hy
  have hF := hd.nativePhysicalFirstCorrectionFamily_smooth hY hΩ hK (d.radius y) b
  have hGerm := hd.nativePhysicalFirstCorrectionFamily_actual_germ hY hΩ hSub hK (d.radius y) hr0 hy b
  have hS := (hd.physicalFirstCorrectionCovariantFamily_data hY hΩ hSub hK b).2
  have hCall := coarse_second_covariant_graph_of_native_germ hY hΩ hSub hd hK (d.radius y) y hy a c
    (physicalFirstCorrectionCoarseFamily d b) (fun x => physicalFirstCorrectionCovariantFamily d b x a)
    (nativePhysicalFirstCorrectionFamily d (d.radius y) b) (nativeFirstCorrectionDomain Y Ω) hD
    inter_subset_left hp hF hGerm (fun x hx => hS x hx a)
    (fun p hp he i j u => by
      have hpN : normalFrameRelativeNormalization d.γ p ∈ nativeFirstCorrectionDomain Y Ω :=
        ⟨hd.1.1.normalFrameRelativeNormalization_mem hK p hp.1,hp.2⟩
      exact nativePhysicalFirstCorrection_normalized_rotation_graph hΩ d hd.1.1 hK (d.radius y) b p hp.1 he
        ((hF.contDiffAt (hD.mem_nhds hpN)).differentiableAt (by simp)) i j u)
  simpa only [normalFrameRelativeActualParameter_point d y hr0] using hCall

end ShrinkingSpheres

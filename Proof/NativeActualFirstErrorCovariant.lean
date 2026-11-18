import Proof.NativeFirstErrorRotationGraph
import Proof.ActualFirstAdjointErrorGerm
import Proof.ActualCovariantRotationGraph
import Proof.ActualSmoothRadialTaylorPair
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}
lemma NativeRelativeHorizontalTaylorData.actual_first_error_covariant_graph
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (V : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hAS : ContDiffOn ℝ ∞ A Y) (hGS : ContDiffOn ℝ ∞ G Y)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x)) (b : X) :
    CoarseCovariantRotationGraph d y b (actualFirstAdjointErrorFamily d a A G)
      (fderiv ℝ (s.firstAdjointErrorFamily C) ((y,frameVectorLinear d.frame y),0)
        (normalFrameRelativeHorizontalField d.γ d.radius b ((y,frameVectorLinear d.frame y),0))) := by
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hrS := hd.2.2.2.2.1.1
  have heS := hd.1.2.2.2.2.2.2.1
  have heF := hd.1.2.2.2.2.2.2.2
  have hE (i : I) := (heS i).contDiffAt (hΩ.mem_nhds (hSub hy))
  have hL := (contDiffAt_frameVectorLinear d.frame y hE).differentiableAt (by simp)
  have hHS := contDiffOn_actualFirstAdjointErrorFamily a hY hΩ hSub hd.1 hK hrS
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1) A G hAS hGS
  have hFS := (s.firstErrorAngularFields_smoothAt C V hY hΩ hd.1.1 hK hd.2.2.2.2.1
    _ (s.centerDegreeDomain_pointMem V)).operator
  have hOp : (fun p => (s.firstErrorAngularFields C p).operator)=s.firstAdjointErrorFamily C := by
    funext p
    exact s.firstErrorAngularFields_operator C p
  rw [hOp] at hFS
  apply actual_covariant_rotation_graph_of_germ d y b (actualFirstAdjointErrorFamily d a A G)
    (s.firstAdjointErrorFamily C)
    (s.actual_first_adjoint_error_germ V hY hΩ hSub hd.1 hK hy hr hrS C R A G hR hA hG)
    ((hrS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) hr hL
    (fun i => (hE i).differentiableAt (by simp)) (heF y (hSub hy))
    (frameConnection_skew hΩ hd.1.1 hK d.frame heS heF (hSub hy) b)
    ((hHS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)) (hFS.differentiableAt (by simp))
  intro i j u
  apply s.firstError_normalized_rotation_graph C V hY hΩ hd.1.1 hK hd.2.2.2.2.1
    _ (s.centerDegreeDomain_pointMem V) (fun k => (C k).point) _ i j u
  intro k l
  simpa only [frameVectorLinear_apply,frameVector_axis] using heF y (hSub hy) k l
end ShrinkingSpheres

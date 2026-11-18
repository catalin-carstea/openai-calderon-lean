import Proof.NativeAngularGraphEndpoints
import Proof.NativeFirstAngularErrorEndpoints
import Proof.ActualFirstAdjointErrorGerm
import Proof.NativeFirstErrorAngularGraph
import Proof.CoarseRotationGraphUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace NativeRelativeHorizontalTaylorData
variable {Y Ω : Set X} {d : Data} {y a : X} {F0 : SmoothCoefficientMatrix 2}
  {CQ CI CW CF CA CM CC CH : ℝ}

/-- Identify an already selected actual rotation commutator by its graph,
    retaining that SAME coarse operator in both genuine endpoint squares. -/
lemma actual_angular_error_endpoints
    (s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM)
    (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (Vt Vc : s.response.SymmetricAdjointDomain)
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    {K ρ c₀ floor ε : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hy : y ∈ Y)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (R A G : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hR : ∀ x ∈ Y,RealizesActualMidpointRadialError d x (R x))
    (hA : ∀ x ∈ Y,∀ u v,⟪(R x+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ=
      ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,A x v⟫_ℝ)
    (hG : ∀ x ∈ Y,RealizesActualCenterGradientAdjoint d x a (A x) (G x))
    (i j : I) (S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (hS : ∀ u : SphereSobolev 2,
      sphereSobolevRotationL 0 i j (actualFirstAdjointErrorFamily d a A G y
        (sphereSobolevInclusionL 2 1 (by norm_num) u))=
      sphereSobolevInclusionL 0 (-1) (by norm_num)
        (S (sphereSobolevInclusionL 2 1 (by norm_num) u)+
          actualFirstAdjointErrorFamily d a A G y (sphereSobolevRotationL 2 i j u))) :
    let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
    let v := normalFrameRelativeAngularTangent d.γ p i j
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      (fderiv ℝ (s.firstAdjointHalfErrorFamily C) p v).comp
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
        (fderiv ℝ (s.firstAdjointHigherErrorFamily C Vt Vc hd.1.1 hK) p v)=
      S.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  dsimp only
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hr := (hd.2.2.2.2.1.2 y hy).1.ne'
  have hGerm := s.actual_first_adjoint_error_germ Vt hY hΩ hSub hd.1 hK
    hy hr hd.2.2.2.2.1.1 C R A G hR hA hG
  have hE := hGerm.self_of_nhds
  change actualFirstAdjointErrorFamily d a A G y=
    s.firstAdjointErrorFamily C (normalFrameRelativeActualParameter d (d.radius y) y) at hE
  rw [normalFrameRelativeActualParameter_point d y hr] at hE
  have he (k l : I) : metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0 := by
    simpa only [p,frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) k l
  apply s.angular_error_endpoints_of_graph C Vt Vc hY hΩ hd.1.1 hK
    hd.2.2.2.2.1 hF0 p (s.centerDegreeDomain_pointMem Vt) (s.centerDegreeDomain_pointMem Vc)
    (fun k => (C k).point) he i j S
  intro u
  rw [← hE]
  exact hS u
end NativeRelativeHorizontalTaylorData
end ShrinkingSpheres

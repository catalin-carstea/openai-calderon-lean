import Proof.NativeAdjointHalfTaylor
import Proof.UniformNativeAntisymmetricTaylorData
import Proof.DenseOperatorRestrictionUnique
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2600
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

lemma half_endpoint_difference_of_coarse
    (R S : SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (L M : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hL : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp R=
      L.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hM : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp S=
      M.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)))
    (hDef : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (R-S)=
      KN.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    L-M=KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  apply clm_eq_of_dense_restriction (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
    (denseRange_sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  apply ContinuousLinearMap.ext
  intro u
  have hLv := DFunLike.congr_fun hL u
  have hMv := DFunLike.congr_fun hM u
  have hDv := DFunLike.congr_fun hDef u
  simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,map_sub] at hLv hMv hDv ⊢
  rw [← hLv,← hMv,hDv,sphereSobolevInclusionL_trans_apply]

namespace NormalFrameRelativeResponsePacket
variable {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z CQ : ℝ}
  {q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) N Z CQ}
lemma adjointHalfTaylor_transpose_defect (t : NormalFrameRelativeResponsePacket q)
    (V : t.SymmetricAdjointDomain) (hZ : 2 ≤ Z) (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (p : NormalFrameRelativeParameter) (hp : p ∈ V.domain)
    (KN : SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (hKN : (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (t.adjointTaylor p-t.forwardTaylor p)=KN.comp (sphereSobolevInclusionL 1 (-(1/2:ℝ)) (by norm_num))) :
    (t.adjointHalfTaylor p).adjoint=t.adjointHalfTaylor p-
      KN.comp (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  have hD := half_endpoint_difference_of_coarse (t.adjointTaylor p) (t.forwardTaylor p)
    (t.adjointHalfTaylor p) (q.halfTaylor p) KN
    (V.adjointHalfTaylor_coarse_compatible hZ F0 hF0 p hp)
    (V.halfTaylor_coarse_compatible hZ F0 hF0 p hp) hKN
  have hA : (t.adjointHalfTaylor p).adjoint=q.halfTaylor p := by
    unfold adjointHalfTaylor
    exact ContinuousLinearMap.adjoint_adjoint _
  rw [hA]
  calc
    _ = t.adjointHalfTaylor p-(t.adjointHalfTaylor p-q.halfTaylor p) := by abel
    _ = _ := congrArg (fun T => t.adjointHalfTaylor p-T) hD
end NormalFrameRelativeResponsePacket

theorem uniform_native_adjoint_half_taylor_defect {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ)
    (CQ CI CW : ℝ) (hCQ : 0 ≤ CQ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z=1)
    (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ))) :
    ∃ η CK : ℝ,0 < η ∧ η ≤ 1 ∧ 0 ≤ CK ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      ∀ hd : Admissible Y Ω K ρ c₀ M Cj floor ε d,∀ y ∈ Y,∀ CF CA CM : ℝ,
      ∀ s : NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM,
      ∃ KN : NormalFrameRelativeParameter → SphereSobolev (-(1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
        SmoothFiniteJetBound KN ((y,frameVectorLinear d.frame y),0) 3 (CK*(d.radius y)^2) ∧
        (s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)).adjoint=
          s.response.adjointHalfTaylor ((y,frameVectorLinear d.frame y),0)-
            (KN ((y,frameVectorLinear d.frame y),0)).comp
              (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)) := by
  obtain ⟨η,CR,CK,hη,hη1,hCR,hCK,hSkew⟩ := uniform_native_antisymmetric_taylor_data
    hY hΩ hm K ρ c₀ M Cj hK hρ CQ CI CW hCQ hCI hCW F0 hF0 Q0 hQ0
  refine ⟨η,CK,hη,hη1,hCK,?_⟩
  intro floor hf ε hε hSmall d hd y hy CF CA CM s
  obtain ⟨R,ha0,V,hJets,hGraph⟩ := hSkew floor hf ε hε hSmall d hd y hy CF CA CM s
  let KN := fun p => s.response.antisymmetricTaylorKernel F0 ha0 (R.normalCoefficient Q0 p)
    (linearScalarClosedCoefficientL Q0 (normalFrameRelativeFirstCovector d.γ d.g₁ p)) p
  refine ⟨KN,hJets,?_⟩
  exact s.response.adjointHalfTaylor_transpose_defect V (by norm_num) F0 hF0 _ V.pointMem _ hGraph
end ShrinkingSpheres

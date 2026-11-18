import Proof.ParallelModelFirstRaisingSource

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

/-- A genuine pointwise higher source is sufficient for the balanced
operator/source rule. Only the actual lower operator family is differentiated. -/
lemma balanced_positive_half_operator_source_product
    {Y : Set X} (hY : IsOpen Y) (d : Data)
    (C : X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)))
    (A : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (V : X → SphereSobolev (3/2:ℝ)) (H : X → SphereSobolev (3/2:ℝ))
    (hC : ContDiffOn ℝ ∞ C Y) (hA : ContDiffOn ℝ ∞ A Y) (hV : ContDiffOn ℝ ∞ V Y)
    (hGraph : ∀ x ∈ Y,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A x)=
      (C x).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    {y : X} (hy : y ∈ Y) (a : X)
    (hH : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (H y)=A y (V y))
    (G : SphereSobolev (3/2:ℝ))
    (hG : sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) G=halfSectionCovariantDerivativeL d V y a)
    (JH : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hJet : halfOperatorCovariantDerivativeL d C A y a=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp JH) :
    balancedPositiveHalfDerivative d (fun x => A x (V x)) H y a=A y G+JH (V y) := by
  let L := fun x => A x (V x)
  let T := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hL : ContDiffOn ℝ ∞ L Y := hA.clm_apply hV
  have hNear : (fun x => T (L x))=ᶠ[𝓝 y]
      (fun x => C x (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (V x))) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact DFunLike.congr_fun (hGraph x hx) (V x)
  have hLD := ((hL.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
  have hDer := (T.hasFDerivAt.comp y hLD).congr_of_eventuallyEq hNear.symm
  have hFD := DFunLike.congr_fun hDer.fderiv a
  have hRaw := half_covariant_operator_source_product d C A V y a
    (hC.contDiffAt (hY.mem_nhds hy)) (hV.contDiffAt (hY.mem_nhds hy))
  rw [hFD,hJet] at hRaw
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  rw [balanced_positive_half_derivative_weak_graph d L H y a hH,map_add]
  have hAG := DFunLike.congr_fun (hGraph y hy) G
  simp only [ContinuousLinearMap.comp_apply,hG] at hAG
  simpa only [weakHalfSourceCovariantDerivative,L,T,ContinuousLinearMap.comp_apply,hAG] using hRaw

lemma model_first_raising_adjoint_source_product
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (Q : OAI.AnisotropicCalderon.DirichletFamily.SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,
      OAI.AnisotropicCalderon.DirichletFamily.coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiffOn ℝ ∞ U Y)
    {y : X} (hy : y ∈ Y) (c i : I) :
    balancedPositiveHalfDerivative d
      (fun x => scalarModelRaisingAdjointHigher A d c x
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x)))
      (modelFirstRaisingAdjointSourceHigher d U c) y (axis i)=
      scalarModelRaisingAdjointHigher A d c y (fiveHalfCovariantDerivative d U (axis i) y)+
      modelFirstRaisingAdjointJet A d c i y
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  exact balanced_positive_half_operator_source_product hY d
    (fun x => (framedRaisingHalfL d x (axis c)).adjoint) (scalarModelRaisingAdjointHigher A d c)
    (fun x => sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U x))
    (modelFirstRaisingAdjointSourceHigher d U c) (scalarModelRaisingAdjoint_smooth hd c)
    (scalarModelRaisingAdjointHigher_smooth hd A c)
    ((sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).contDiff.comp_contDiffOn hU)
    (fun x _ => scalarModelRaisingAdjointHigher_balanced A d c x hA) hy (axis i)
    (modelFirstRaisingAdjointSourceHigher_graph Q hQ A hA d U c y)
    (fiveHalfCovariantDerivative d U (axis i) y)
    (fiveHalfCovariantDerivative_half_inclusion d U y (axis i)
      ((hU.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp)))
    (modelFirstRaisingAdjointJet A d c i y)
    (modelFirstRaisingAdjointJet_weak_graph hY hΩ hd hK A hA hy c i)

end ShrinkingSpheres.ParallelEnergy

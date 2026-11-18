import Proof.ParallelModelFirstModelHalf
import Proof.ParallelFirstSelfAdjointSourceProduct
import Proof.ParallelScalarModelAngularAdjunction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.DirichletFamily

lemma model_first_flat_lower_half_graph (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ))) (i : I) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (flatLoweringSobolevL (3/2:ℝ) i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hL := flatLoweringSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) i
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  rw [hI] at hL
  apply ContinuousLinearMap.ext
  intro u
  have hLu := DFunLike.congr_fun hL u
  have hA := DFunLike.congr_fun (flat_lowering_coarse_half_graph Q hQ i)
    (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
  simp only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] at hLu hA ⊢
  rw [hLu] at hA
  simpa only [sphereSobolevInclusionL_trans_apply] using hA

lemma model_first_flat_lower_half_eq (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (i : I) (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp A=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    flatLoweringSobolevL (3/2:ℝ) i=A := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  exact DFunLike.congr_fun ((model_first_flat_lower_half_graph Q hQ i).trans hA.symm) u

def modelFirstRaisingAdjointSourceHigher (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (c : I) (y : X) :
    SphereSobolev (3/2:ℝ) :=
  ∑ i : I,frameCoordinateLinear d.γ d.frame y i (axis c) • flatLoweringSobolevL (5/2:ℝ) i (U y)

lemma modelFirstRaisingAdjointSourceHigher_graph
    (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ i,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A i)=
      (flatHalfRaisingL i).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (d : Data) (U : X → SphereSobolev (5/2:ℝ)) (c : I) (y : X) :
    sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) (modelFirstRaisingAdjointSourceHigher d U c y)=
      scalarModelRaisingAdjointHigher A d c y (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) (U y)) := by
  have hL (i : I) := DFunLike.congr_fun (flatLoweringSobolevL_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) i) (U y)
  have hI : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) := by congr 1 <;> norm_num
  simp only [ContinuousLinearMap.comp_apply,hI,model_first_flat_lower_half_eq Q hQ _ _ (hA _)] at hL
  simp only [modelFirstRaisingAdjointSourceHigher,scalarModelRaisingAdjointHigher,map_sum,map_smul,
    _root_.sum_apply,_root_.smul_apply,←hL]

lemma scalarModelRaisingAdjointHigher_smooth
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) (c : I) :
    ContDiffOn ℝ ∞ (scalarModelRaisingAdjointHigher A d c) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hC (j : I) : ContDiffOn ℝ ∞ (fun x => frameCoordinateLinear d.γ d.frame x j (axis c)) Y := by
    have hh := ((hd.1.1.contDiffOn_metricPair (fun _ => axis c) (fun x => d.frame x j)
      contDiffOn_const (hd.1.2.2.2.2.2.2.1 j)).mono hSub)
    exact hh.congr (fun x _ => frameCoordinateLinear_apply d.γ d.frame x (axis c) j)
  exact ContDiffOn.sum (fun j _ => (hC j).smul contDiffOn_const)

def modelFirstRaisingAdjointJet
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (d : Data) (c i : I) (y : X) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ a : I,christoffel d.γ y a i c • scalarModelRaisingAdjointHigher A d a y

lemma modelFirstRaisingAdjointJet_weak_graph
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (A : I → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hA : ∀ j,(sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (A j)=
      (flatHalfRaisingL j).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    {y : X} (hy : y ∈ Y) (c i : I) :
    halfOperatorCovariantDerivativeL d (fun x => (framedRaisingHalfL d x (axis c)).adjoint)
      (scalarModelRaisingAdjointHigher A d c) y (axis i)=
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (modelFirstRaisingAdjointJet A d c i y) := by
  have hStrong := half_covariant_adjoint_strong_extension d
    (fun x => framedRaisingHalfL d x (axis c)) (fun x => framedRaisingHigherL d x (axis c))
    (scalarModelRaisingAdjointHigher A d c) (((hd.framedRaisingHalf_smooth (axis c)).1).contDiffAt (hY.mem_nhds hy))
    (axis i) (framedRaisingHalf_balanced d y (axis c))
    (scalarModelRaisingAdjointHigher_balanced A d c y hA) (framedRaisingFirstHalfJet d i c y)
    (framed_raising_strong_half_graph hY hΩ hd hK hy i c)
  rw [hStrong]
  apply ContinuousLinearMap.ext
  intro u
  have hR (a : I) := DFunLike.congr_fun (scalarModelRaisingAdjointHigher_balanced A d a y hA) u
  simp only [ContinuousLinearMap.comp_apply] at hR
  simp only [framedRaisingFirstHalfJet,modelFirstRaisingAdjointJet,map_sum,map_smul,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply,hR]

end ShrinkingSpheres.ParallelEnergy

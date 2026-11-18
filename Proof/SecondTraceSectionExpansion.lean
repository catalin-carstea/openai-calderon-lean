import Proof.CovariantTensorSectionApplication
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma oneSectionCovariantDerivative_add (d : Data) (U V : X → SphereSobolev 1) (y a : X)
    (hU : DifferentiableAt ℝ U y) (hV : DifferentiableAt ℝ V y) :
    oneSectionCovariantDerivative d (fun x => U x+V x) y a=
      oneSectionCovariantDerivative d U y a+oneSectionCovariantDerivative d V y a := by
  have hD : fderiv ℝ (fun x => U x+V x) y a=fderiv ℝ U y a+fderiv ℝ V y a := by
    rw [fderiv_fun_add hU hV]
    rfl
  simp only [oneSectionCovariantDerivative,hD,map_add,smul_add,Finset.sum_add_distrib]
  abel

/-- Exact second moving-trace algebra on genuine sections: its tensor-index
    connection cancels before the actual angular products are collected. -/
theorem second_trace_section_expansion (d : Data) (y : X) (i j : I)
    (C : I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (J : I → SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    (U : X → SphereSobolev 2) (D V W : I → X → SphereSobolev 1)
    (hC : ∀ k,DifferentiableAt ℝ (C k) y) (hU : DifferentiableAt ℝ U y)
    (hD : ∀ k,DifferentiableAt ℝ (D k) y) (hV : ∀ k,DifferentiableAt ℝ (V k) y)
    (hOut : ∀ k,(fun x => sphereSobolevInclusionL 1 0 (by norm_num) (V k x)) =ᶠ[𝓝 y]
      (fun x => C k x (sphereSobolevInclusionL 2 1 (by norm_num) (U x))))
    (hFirst : ∀ k,W k =ᶠ[𝓝 y] (fun x => D k x+V k x))
    (hHorizontal : D i y=highSectionCovariantDerivative d U y (d.frame y i))
    (hGraph : ∀ k,CoarseCovariantRotationGraph d y (d.frame y i) (C k)
      ((∑ l : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) k l • C l y)+J k)) :
    oneSectionCovariantDerivative d (W j) y (d.frame y i)-
      (∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
        sphereSobolevInclusionL 1 0 (by norm_num) (W k y))+C i y (W j y)=
    (oneSectionCovariantDerivative d (D j) y (d.frame y i)-
      ∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
        sphereSobolevInclusionL 1 0 (by norm_num) (D k y))+
      C i y (D j y)+C j y (D i y)+C i y (V j y)+
      J j (sphereSobolevInclusionL 2 1 (by norm_num) (U y)) := by
  have hJet := covariant_tensor_section_application d y (d.frame y i) C J U V hC hU hV hOut hGraph j
  have hW := oneSectionCovariantDerivative_congr_germ (d:=d) (a:=d.frame y i) (hFirst j)
  rw [oneSectionCovariantDerivative_add d (D j) (V j) y (d.frame y i) (hD j) (hV j)] at hW
  have hPoint (k : I) : W k y=D k y+V k y := (hFirst k).eq_of_nhds
  rw [hW]
  simp only [hPoint,map_add,smul_add,Finset.sum_add_distrib]
  rw [← hHorizontal] at hJet
  exact (show _ =
    (oneSectionCovariantDerivative d (D j) y (d.frame y i)-
      ∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
        sphereSobolevInclusionL 1 0 (by norm_num) (D k y))+
      C i y (D j y)+C i y (V j y)+
      (oneSectionCovariantDerivative d (V j) y (d.frame y i)-
        ∑ k : I,frameConnectionCoefficient d.γ d.frame y (d.frame y i) j k •
          sphereSobolevInclusionL 1 0 (by norm_num) (V k y)) by abel).trans
    (by rw [hJet];abel)
end ShrinkingSpheres

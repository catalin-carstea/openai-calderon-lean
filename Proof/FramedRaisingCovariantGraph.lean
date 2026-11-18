import Proof.FlatRaisingCoarseRotation
import Proof.FrameCoframeCovariantDerivative
import Proof.SkewRotationCoefficientContraction
import Proof.ActualCovariantRotationGraph
import Proof.FramedFlatRaisingSobolev
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

/-- The physical coframe raising map is parallel with its tangent index.
    The actual connection of a fixed physical direction is the only remaining
    derivative. Arbitrary frame derivatives cancel exactly. -/
theorem framedFlatRaising_covariant_graph {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    (d : Data) (h : Elliptic Ω K d.γ) (hK : 0 < K)
    (he : ∀ j,ContDiffOn ℝ ∞ (fun x => d.frame x j) Ω)
    (hFrame : ∀ x ∈ Ω,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j)=if i=j then 1 else 0)
    {y : X} (hy : y ∈ Ω) (a b : X) :
    CoarseCovariantRotationGraph d y a (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x b)
      (framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y a b)) := by
  let F : X → SphereSobolev 1 →L[ℝ] SphereSobolev 0 := fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x b
  let c : I → X → ℝ := fun j x => frameCoordinateLinear d.γ d.frame x j b
  let Γ : I → I → ℝ := frameConnectionCoefficient d.γ d.frame y a
  let C : I → I → SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    fun i j => c j y • flatOneRaisingL i-c i y • flatOneRaisingL j
  have hΓ (i j : I) : Γ i j= -Γ j i := frameConnection_skew hΩ h hK d.frame he hFrame hy a i j
  have hFApply (x : X) (v : SphereSobolev 1) : F x v=∑ j : I,c j x • flatOneRaisingL j v := by
    simp only [F,c,framedFlatRaisingSobolevL,flatOneRaisingL,_root_.sum_apply,_root_.smul_apply]
  have hCD (j : I) : DifferentiableAt ℝ (c j) y := by
    have hh := h.contDiffOn_metricPair (fun _ => b) (fun x => d.frame x j) contDiffOn_const (he j)
    have hEq : c j=(fun x => metricPair d.γ x b (d.frame x j)) := by
      funext x
      exact frameCoordinateLinear_apply d.γ d.frame x b j
    rw [hEq]
    exact (hh.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)
  have hD : fderiv ℝ F y a=∑ j : I,fderiv ℝ (c j) y a • flatOneRaisingL j := by
    have hEach (j : I) : HasFDerivAt (fun x => c j x • flatOneRaisingL j)
        ((fderiv ℝ (c j) y).smulRight (flatOneRaisingL j)) y := (hCD j).hasFDerivAt.smul_const _
    have hFull := HasFDerivAt.sum (u:=Finset.univ) (fun j _ => hEach j)
    have hh := DFunLike.congr_fun hFull.fderiv a
    change fderiv ℝ F y a=_ at hh
    simpa only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply] using hh
  have hJet : fderiv ℝ F y a-∑ i : I,∑ j : I,((1/2:ℝ)*Γ i j) • C i j=
      framedFlatRaisingSobolevL 1 d.γ d.frame y (connection d.γ y a b) := by
    rw [hD]
    change (∑ j : I,fderiv ℝ (c j) y a • flatOneRaisingL j)-
      (∑ i : I,∑ j : I,((1/2:ℝ)*Γ i j) • (c j y • flatOneRaisingL i-c i y • flatOneRaisingL j))=_
    rw [skew_rotation_coefficient_contraction Γ hΓ (fun j => c j y) flatOneRaisingL]
    change (∑ j : I,fderiv ℝ (c j) y a • flatOneRaisingL j)-
      (∑ j : I,(∑ k : I,Γ j k*c k y) • flatOneRaisingL j)=
      ∑ j : I,frameCoordinateLinear d.γ d.frame y j (connection d.γ y a b) • flatOneRaisingL j
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← sub_smul]
    exact congrArg (fun t : ℝ => t • flatOneRaisingL j)
      (frameCoordinateLinear_covariant_derivative hΩ h hK d.frame he hy (hFrame y hy) a b j)
  apply coarseCovariantRotationGraph_of_angular d y a F C _ hJet
  intro i j u
  simp only [hFApply,map_sum,map_smul]
  simp_rw [flatOneRaisingL_coarse_rotation]
  simp only [map_add,map_sum,map_smul,map_sub,clm_apply_ite_zero,smul_add,Finset.sum_add_distrib,C,
    _root_.sub_apply,_root_.smul_apply,flatRaisingRotationCommutatorL,clm_ite_zero_apply,
    smul_sub,smul_ite,smul_zero,Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]
end ShrinkingSpheres

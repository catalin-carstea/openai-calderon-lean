import Proof.FramedFlatRaisingSobolev
import Proof.FramedRaisingCovariantGraph
import Proof.FrameErrorMatrixRaisingCross
import Proof.BalancedDegreeCommutator
import Proof.NormalGeodesicBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def framedRaisingHalfL (d : Data) (y a : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  ∑ j : I,frameCoordinateLinear d.γ d.frame y j a • flatHalfRaisingL j

def framedRaisingHigherL (d : Data) (y a : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  ∑ j : I,frameCoordinateLinear d.γ d.frame y j a • flatThreeHalfRaisingL j

lemma framedRaisingHalfL_coarse (d : Data) (y a : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (framedFlatRaisingSobolevL 1 d.γ d.frame y a)=
        (framedRaisingHalfL d y a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [framedRaisingHalfL,framedFlatRaisingSobolevL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg
    (fun v => frameCoordinateLinear d.γ d.frame y j a • v) (flatOneRaisingL_half j u))

lemma framedRaisingHigherL_coarse (d : Data) (y a : X) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (framedRaisingHigherL d y a)=
      (framedFlatRaisingSobolevL 1 d.γ d.frame y a).comp
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  have hI : sphereSobolevInclusionL ((3/2:ℝ)-1) ((1:ℝ)-1) (by norm_num)=
      sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num) := by congr 1 <;> norm_num
  have hFlat (j : I) := (flatRaisingSobolevL_inclusion (3/2:ℝ) 1 (by norm_num) j).symm
  rw [hI] at hFlat
  apply ContinuousLinearMap.ext
  intro u
  simp only [framedRaisingHigherL,framedFlatRaisingSobolevL,ContinuousLinearMap.comp_apply,
    _root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg
    (fun v => frameCoordinateLinear d.γ d.frame y j a • v) (DFunLike.congr_fun (hFlat j) u))

lemma framedRaisingHalf_balanced (d : Data) (y a : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (framedRaisingHigherL d y a)=
      (framedRaisingHalfL d y a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_endpoint_pair_of_coarse _ _ _ (framedRaisingHalfL_coarse d y a) (framedRaisingHigherL_coarse d y a)

lemma framedRaisingHalfL_axis_expansion (d : Data) (y a : X) :
    framedRaisingHalfL d y a=∑ k : I,a k • framedRaisingHalfL d y (axis k) := by
  let T : X →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ∑ j : I,(frameCoordinateLinear d.γ d.frame y j).smulRight (flatHalfRaisingL j)
  have hT (v : X) : T v=framedRaisingHalfL d y v := by
    simp only [T,framedRaisingHalfL,ContinuousLinearMap.smulRight_apply,_root_.sum_apply]
  have hMap : T a=∑ k : I,a k • T (axis k) := by
    simpa only [map_sum,map_smul] using (congrArg T (axis_expansion a)).symm
  exact (hT a).symm.trans (hMap.trans (Finset.sum_congr rfl
    (fun k _ => congrArg (fun v => a k • v) (hT (axis k)))))

lemma framedRaisingHalfL_frame (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (i : I) :
    framedRaisingHalfL d y (d.frame y i)=flatHalfRaisingL i := by
  unfold framedRaisingHalfL
  rw [Finset.sum_eq_single i]
  · rw [frameCoordinateLinear_apply,hFrame,ite_eq_left rfl,one_smul]
  · intro j _ hji
    rw [frameCoordinateLinear_apply,hFrame,ite_eq_right (Ne.symm hji),zero_smul]
  · simp only [Finset.mem_univ,not_true_eq_false,IsEmpty.forall_iff]

lemma Admissible.framedRaisingHalf_smooth {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (a : X) :
    ContDiffOn ℝ ∞ (fun x => framedRaisingHalfL d x a) Y ∧
      ContDiffOn ℝ ∞ (fun x => framedRaisingHigherL d x a) Y ∧
      ContDiffOn ℝ ∞ (fun x => framedFlatRaisingSobolevL 1 d.γ d.frame x a) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  have hC (j : I) : ContDiffOn ℝ ∞ (fun x => frameCoordinateLinear d.γ d.frame x j a) Y := by
    have hh := ((hd.1.1.contDiffOn_metricPair (fun _ => a) (fun x => d.frame x j)
      contDiffOn_const (hd.1.2.2.2.2.2.2.1 j)).mono hSub)
    exact hh.congr (fun x _ => frameCoordinateLinear_apply d.γ d.frame x a j)
  exact ⟨ContDiffOn.sum (fun j _ => (hC j).smul contDiffOn_const),
    ContDiffOn.sum (fun j _ => (hC j).smul contDiffOn_const),
    ContDiffOn.sum (fun j _ => (hC j).smul contDiffOn_const)⟩
end ShrinkingSpheres

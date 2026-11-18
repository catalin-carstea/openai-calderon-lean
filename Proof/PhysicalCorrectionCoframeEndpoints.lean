import Proof.PrincipalFirstDerivativeHalfCoefficient
import Proof.BalancedDegreeCommutator
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

/-- The same bounded first correction in a fixed physical direction,
    at an arbitrary genuine Sobolev grade. -/
def physicalFirstCorrectionAtL (s : ℝ) (d : Data) (y a : X) :
    SphereSobolev s →L[ℝ] SphereSobolev s :=
  ∑ j : I,frameCoordinateLinear d.γ d.frame y j a • firstFrameAdjointCorrectionAtL s d y j

def physicalFirstCorrectionHalfL (d : Data) (y a : X) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  (physicalFirstCorrectionAtL (-(1/2:ℝ)) d y a).comp
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num))

def physicalFirstCorrectionHigherL (d : Data) (y a : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  (physicalFirstCorrectionAtL (1/2:ℝ) d y a).comp
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))

def physicalFirstCorrectionCoarseFamily (d : Data) (a x : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (physicalFirstCorrectionAtL 0 d x a).comp (sphereSobolevInclusionL 1 0 (by norm_num))

lemma physicalFirstCorrectionAtL_inclusion (s t : ℝ) (hst : t ≤ s) (d : Data) (y a : X)
    (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hst (physicalFirstCorrectionAtL s d y a u)=
      physicalFirstCorrectionAtL t d y a (sphereSobolevInclusionL s t hst u) := by
  simp only [physicalFirstCorrectionAtL,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
  exact Finset.sum_congr rfl (fun j _ => congrArg
    (fun v => frameCoordinateLinear d.γ d.frame y j a • v)
    (firstFrameAdjointCorrectionAtL_inclusion s t hst d y j u))

lemma physicalFirstCorrectionHalfL_coarse (d : Data) (y a : X) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (physicalFirstCorrectionCoarseFamily d a y)=
      (physicalFirstCorrectionHalfL d y a).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (physicalFirstCorrectionAtL 0 d y a (sphereSobolevInclusionL 1 0 (by norm_num) u))=
    physicalFirstCorrectionAtL (-(1/2:ℝ)) d y a
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u))
  have hArg : sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevInclusionL 1 0 (by norm_num) u)=
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) u) := by
    rw [sphereSobolevInclusionL_trans_apply,sphereSobolevInclusionL_trans_apply]
  exact (physicalFirstCorrectionAtL_inclusion 0 (-(1/2:ℝ)) (by norm_num) d y a
    (sphereSobolevInclusionL 1 0 (by norm_num) u)).trans
      (congrArg (physicalFirstCorrectionAtL (-(1/2:ℝ)) d y a) hArg)

lemma physicalFirstCorrectionHigherL_coarse (d : Data) (y a : X) :
    (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (physicalFirstCorrectionHigherL d y a)=
      (physicalFirstCorrectionCoarseFamily d a y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  change sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (physicalFirstCorrectionAtL (1/2:ℝ) d y a
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u))=
    physicalFirstCorrectionAtL 0 d y a
      (sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u))
  have hArg : sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)
      (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)=
    sphereSobolevInclusionL 1 0 (by norm_num) (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u) := by
    rw [sphereSobolevInclusionL_trans_apply,sphereSobolevInclusionL_trans_apply]
  exact (physicalFirstCorrectionAtL_inclusion (1/2:ℝ) 0 (by norm_num) d y a
    (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num) u)).trans
      (congrArg (physicalFirstCorrectionAtL 0 d y a) hArg)

lemma physicalFirstCorrection_balanced (d : Data) (y a : X) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (physicalFirstCorrectionHigherL d y a)=
      (physicalFirstCorrectionHalfL d y a).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) :=
  balanced_endpoint_pair_of_coarse _ _ _ (physicalFirstCorrectionHalfL_coarse d y a)
    (physicalFirstCorrectionHigherL_coarse d y a)

lemma physicalFirstCorrectionCoarseFamily_eq (d : Data) (a x : X) :
    physicalFirstCorrectionCoarseFamily d a x=
      ∑ j : I,frameCoordinateLinear d.γ d.frame x j a • firstFrameCorrectionCoarseFamily d j x := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [physicalFirstCorrectionCoarseFamily,physicalFirstCorrectionAtL,
    firstFrameAdjointCorrectionAtL_zero,firstFrameCorrectionCoarseFamily,
    ContinuousLinearMap.comp_apply,_root_.sum_apply,_root_.smul_apply]

lemma physicalFirstCorrectionHalfL_axis_expansion (d : Data) (y a : X) :
    physicalFirstCorrectionHalfL d y a=∑ k : I,a k • physicalFirstCorrectionHalfL d y (axis k) := by
  let T : X →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))) :=
    ∑ j : I,(frameCoordinateLinear d.γ d.frame y j).smulRight (firstFrameLowerCorrectionL d y j)
  have hh := congrArg T (axis_expansion a)
  have hT (v : X) : T v=physicalFirstCorrectionHalfL d y v := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [T,physicalFirstCorrectionHalfL,physicalFirstCorrectionAtL,firstFrameLowerCorrectionL,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,_root_.sum_apply,_root_.smul_apply]
  have hMap : T a=∑ k : I,a k • T (axis k) := by
    simpa only [map_sum,map_smul] using hh.symm
  calc
    _ = T a := (hT a).symm
    _ = ∑ k : I,a k • T (axis k) := hMap
    _ = _ := Finset.sum_congr rfl (fun k _ => congrArg (fun v => a k • v) (hT (axis k)))

lemma physicalFirstCorrectionHalfL_frame (d : Data) (y : X)
    (hFrame : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) (i : I) :
    physicalFirstCorrectionHalfL d y (d.frame y i)=firstFrameLowerCorrectionL d y i := by
  have hAt : physicalFirstCorrectionAtL (-(1/2:ℝ)) d y (d.frame y i)=
      firstFrameAdjointCorrectionAtL (-(1/2:ℝ)) d y i := by
    unfold physicalFirstCorrectionAtL
    rw [Finset.sum_eq_single i]
    · rw [frameCoordinateLinear_apply,hFrame,ite_eq_left rfl,one_smul]
    · intro j _ hji
      rw [frameCoordinateLinear_apply,hFrame,ite_eq_right (Ne.symm hji),zero_smul]
    · simp only [Finset.mem_univ,not_true_eq_false,IsEmpty.forall_iff]
  unfold physicalFirstCorrectionHalfL firstFrameLowerCorrectionL
  rw [hAt]

lemma Admissible.contDiffOn_physicalFirstCorrectionAtL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (s : ℝ) (a : X) :
    ContDiffOn ℝ ∞ (fun x => physicalFirstCorrectionAtL s d x a) Y := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  apply ContDiffOn.sum
  intro j _
  have hc := (hd.1.1.contDiffOn_metricPair (fun _ => a) (fun x => d.frame x j) contDiffOn_const
    (hd.1.2.2.2.2.2.2.1 j)).mono hSub
  have hh := hc.smul (hd.contDiffOn_firstFrameAdjointCorrectionAtL hY hΩ hK s j)
  apply hh.congr
  intro x hx
  change frameCoordinateLinear d.γ d.frame x j a • firstFrameAdjointCorrectionAtL s d x j=
    metricPair d.γ x a (d.frame x j) • firstFrameAdjointCorrectionAtL s d x j
  rw [frameCoordinateLinear_apply]

lemma Admissible.norm_physicalFirstCorrectionAtL_axis_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (s : ℝ) {y : X} (hy : y ∈ Y) (a : I) :
    ‖physicalFirstCorrectionAtL s d y (axis a)‖ ≤ 3*K*firstCorrectionGradeBound s K (M ⟨1,by omega⟩) := by
  exact norm_weighted_sum_three_le _ _ K _ (zero_le_one.trans hK)
    (fun j => by
      rw [frameCoordinateLinear_apply]
      exact hd.1.1.frame_coordinate_abs_bound hK d.frame (hd.2.1.center_mem hy)
        (hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)) a j)
    (fun j => hd.norm_firstFrameAdjointCorrectionAtL_le_gradeBound hΩ hm hK hf hε hε1 s hy j)
end ShrinkingSpheres

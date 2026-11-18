import Proof.UniformNormalFrameParallelCenterHigherJets
import Proof.NormalFrameRadialReorder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma contDiffAt_joint_normalizedParallelCenterJacobian
    (g : MetricField) (E : X × X → X) (p : X × X)
    (hE : ContDiffAt ℝ ∞ E p) (hG : ContDiffAt ℝ ∞ (connectionBilinear g) p.1)
    (hInv : (normalVerticalJacobian E p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q : X × X => normalizedParallelCenterJacobian g E q.1 q.2) p := by
  let DE := fderiv ℝ E
  let J := fun q : X × X => (DE q).comp (ContinuousLinearMap.inr ℝ X X)
  let A := fun q : X × X => (DE q).comp (ContinuousLinearMap.inl ℝ X X)
  let G := connectionBilinear g ∘ (ContinuousLinearMap.fst ℝ X X)
  let Flip := (ContinuousLinearMap.flipₗᵢ ℝ X X X).toContinuousLinearEquiv.toContinuousLinearMap
  let GV := fun q : X × X => Flip (G q) q.2
  let C := fun q => A q-(J q).comp (GV q)
  have hDE : ContDiffAt ℝ ∞ DE p := hE.fderiv_right (m:=∞) (by simp)
  have hJ : ContDiffAt ℝ ∞ J p := hDE.clm_comp contDiffAt_const
  have hA : ContDiffAt ℝ ∞ A p := hDE.clm_comp contDiffAt_const
  have hG' : ContDiffAt ℝ ∞ G p := hG.comp p (ContinuousLinearMap.fst ℝ X X).contDiff.contDiffAt
  have hGF : ContDiffAt ℝ ∞ (Flip ∘ G) p := Flip.contDiff.contDiffAt.comp p hG'
  have hGV : ContDiffAt ℝ ∞ GV p := hGF.clm_apply contDiffAt_snd
  have hC : ContDiffAt ℝ ∞ C p := hA.sub (hJ.clm_comp hGV)
  have hInvJ : (J p).IsInvertible := hInv
  have hI : ContDiffAt ℝ ∞ (fun q => (J q).inverse) p := hInvJ.contDiffAt_map_inverse.comp (f:=J) p hJ
  have hCeq : C = fun q : X × X => normalParallelCenterJacobian g E q.1 q.2 := by
    funext q
    apply ContinuousLinearMap.ext
    intro a
    change A q a-J q (GV q a) = _
    rw [normalParallelCenterJacobian_apply]
    change fderiv ℝ E q (a,0)-fderiv ℝ E q (0,connectionBilinear g q.1 a q.2) =
      fderiv ℝ E q (a,-connection g q.1 a q.2)
    rw [← map_sub,← connectionBilinear_apply]
    congr 1
    simp only [Prod.mk_sub_mk,sub_zero,zero_sub]
  have hSmooth := hI.clm_comp hC
  rw [hCeq] at hSmooth
  exact hSmooth

/-- A genuine open smooth domain around every admitted normal-frame point.
    The vertical inverse is restricted to its open invertibility locus. -/
theorem Background.exists_normalFrameParallelCenter_smooth_domain {Y Ω : Set X}
    (hΩ : IsOpen Ω) {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K)
    {E : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g E R)
    {y : X} (hy : y ∈ Y) (s : ℝ) (L : X →L[ℝ] X) (z : X)
    (hv : s • L z ∈ disk g y (R y)) :
    ∃ U : Set (NormalFrameParameter × X),IsOpen U ∧ ((y,(s,L)),z) ∈ U ∧
      ContDiffOn ℝ ∞ (normalFrameParallelCenterJacobian g E) U := by
  obtain ⟨S,hS,hTube,hE⟩ := hN.1
  let D := S ∩ (ContinuousLinearMap.fst ℝ X X) ⁻¹' Ω
  have hD : IsOpen D := hS.inter (hΩ.preimage (ContinuousLinearMap.fst ℝ X X).continuous)
  have hED : ContDiffOn ℝ ∞ E D := hE.mono inter_subset_left
  let J := fun q : X × X => normalVerticalJacobian E q.1 q.2
  have hJ : ContDiffOn ℝ ∞ J D :=
    (hED.fderiv_of_isOpen hD (m:=∞) (by simp)).clm_comp contDiffOn_const
  let V := D ∩ J ⁻¹' {A : X →L[ℝ] X | A.IsInvertible}
  have hV : IsOpen V := hJ.continuousOn.isOpen_inter_preimage hD ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hMem : (y,s • L z) ∈ V :=
    ⟨⟨hTube ⟨hy,hv⟩,hN.center_mem hy⟩,hN.normalVerticalJacobian_isInvertible hy _ hv⟩
  have hW : ContDiffOn ℝ ∞ (fun q : X × X => normalizedParallelCenterJacobian g E q.1 q.2) V := by
    intro q hq
    exact (contDiffAt_joint_normalizedParallelCenterJacobian g E q
      (hE.contDiffAt (hS.mem_nhds hq.1.1))
      ((h.1.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hq.1.2)) hq.2).contDiffWithinAt
  refine ⟨normalFrameInput ⁻¹' V,hV.preimage contDiff_normalFrameInput.continuous,hMem,?_⟩
  exact hW.comp contDiff_normalFrameInput.contDiffOn (fun q hq => hq)

end ShrinkingSpheres

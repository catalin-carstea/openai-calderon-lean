module

public import Proof.Manuscript.ScalarCylinderSweep
public import Proof.Manuscript.ScalarProductExtensionLocal

import Proof.CalderonN.ProductPropagation
import Proof.CalderonN.CompactBounds
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Set Filter Metric
open CalderonPaper.ScalarElliptic
open scoped Topology ContDiff

namespace CalderonPaper

variable {n : ℕ} [NeZero n]

set_option maxHeartbeats 5500000 in
/-- The compact two-arm criterion supplies a finite-sweep collar.
A small fixed shift places the complete analytic input in every nearby
higher reached domain. Vertical uniqueness identifies the full overlap. -/
theorem exists_reference_scalar_cylinder_local
    {Z : Type*} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph (X n × X n) (Z × ℝ))
    {B : Set Z} {lo a hi : ℝ} (hla : lo < a) (hah : a < hi)
    (hChart : B ×ˢ Ioo lo hi ⊆ e.target)
    {D₁ D₂ : Set (X n)} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    (hChartD : e.symm '' (B ×ˢ Ioo lo hi) ⊆ D₁ ×ˢ D₂)
    {S : Set (X n × X n)} (hS : IsOpen S)
    (hUp : ∀ z ∈ B, ∀ s t : ℝ, s ∈ Ioo lo hi → t ∈ Ioo lo hi →
      s ≤ t → e.symm (z,s) ∈ S → e.symm (z,t) ∈ S)
    {L₁₀ L₂₀ : ScalarElliptic n} (hL₁₀ : L₁₀.SmoothOn D₁) (hL₂₀ : L₂₀.SmoothOn D₂)
    {ρ : X n × X n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ (e.symm '' (interior B ×ˢ Ioo lo hi)))
    (hSign : ∀ z ∈ interior B, ∀ t ∈ Ioo lo hi, 0 < ρ (e.symm (z,t)) ↔ a < t)
    (z : Z) (hz : z ∈ interior B) (hZero : ρ (e.symm (z,a)) = 0)
    (hStrict : ProductStrictHessianAt L₁₀.metric L₂₀.metric ρ (e.symm (z,a))) :
    ∃ (B' : Set Z) (d b₀ : ℝ), IsOpen B' ∧ z ∈ B' ∧ B' ⊆ interior B ∧
      0 < d ∧ a < b₀ ∧ Ioo (a-d) (a+d) ⊆ Ioo lo hi ∧
      ∀ b ∈ Ico a b₀,
        CompactDataExtension (ScalarSweepPath.solves (D₁ := D₁) (D₂ := D₂) (L₁₀ := L₁₀) (L₂₀ := L₂₀))
          (productAbove e B S b hi) (e.symm '' (B' ×ˢ Ioo (a-d) (a+d))) := by
  let T := interior B ×ˢ Ioo lo hi
  have hTgt : T ⊆ e.target := fun q hq => hChart ⟨interior_subset hq.1,hq.2⟩
  have hT : IsOpen T := isOpen_interior.prod isOpen_Ioo
  let Q := e.symm '' T
  have hQ : IsOpen Q := e.isOpen_image_symm_of_subset_target hT hTgt
  have hQD : Q ⊆ D₁ ×ˢ D₂ :=
    (image_mono (Set.prod_mono interior_subset Subset.rfl)).trans hChartD
  let p := e.symm (z,a)
  have hp : p ∈ Q := ⟨(z,a),⟨hz,hla,hah⟩,rfl⟩
  obtain ⟨r₀,hr₀,hBall⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hp)
  let r := r₀/2
  have hr : 0 < r := half_pos hr₀
  let J := closedBall p r
  let U := ball p r
  have hU : IsOpen U := isOpen_ball
  have hJQ : J ⊆ Q := (closedBall_subset_ball (half_lt_self hr₀)).trans hBall
  have hUJ : U ⊆ J := ball_subset_closedBall
  have hUQ : U ⊆ Q := hUJ.trans hJQ
  obtain ⟨V,K₁,K₂,K₃,K₄,ε,hV,hpV,hVU,hε,hK₁,hK₂,hK₃,hK₄,hArm,_,hExtend⟩ :=
    exists_reference_scalar_productExtension hD₁ hD₂ hL₁₀ hL₂₀ hU (hUQ.trans hQD)
      p (mem_ball_self hr) (hρ.mono hUQ) hZero hStrict
  have hN : {q : Z × ℝ | q ∈ T ∧ e.symm q ∈ V} ∈ 𝓝 (z,a) :=
    inter_mem (hT.mem_nhds ⟨hz,hla,hah⟩)
      ((e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (hTgt ⟨hz,hla,hah⟩))).preimage_mem_nhds
        (hV.mem_nhds hpV))
  obtain ⟨B₀,d,hB₀,hz₀,hd,hBox⟩ := exists_open_vertical_box_of_mem_nhds hN
  let I := Ioo (a-d) (a+d)
  have haI : a ∈ I := by
    change a-d < a ∧ a < a+d
    constructor <;> linarith
  have hBase : B₀ ⊆ interior B := fun w hw =>
    (hBox (show (w,a) ∈ B₀ ×ˢ I from ⟨hw,haI⟩)).1.1
  have hI : I ⊆ Ioo lo hi := fun s hs =>
    (hBox (show (z,s) ∈ B₀ ×ˢ I from ⟨hz₀,hs⟩)).1.2
  let top := a + d/2
  have haTop : a < top := by dsimp [top]; linarith
  have hTopI : top ∈ I := by
    change a-d < a+d/2 ∧ a+d/2 < a+d
    constructor <;> linarith
  have hRtop : 0 < ρ (e.symm (z,top)) := (hSign z hz top (hI hTopI)).mpr haTop
  let c := min (ε/2) (ρ (e.symm (z,top))/2)
  have hc : 0 < c := lt_min (half_pos hε) (half_pos hRtop)
  have hcε : c ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hcTop : c < ρ (e.symm (z,top)) := (min_le_right _ _).trans_lt (half_lt_self hRtop)
  let B' := B₀ ∩ (fun w : Z => ρ (e.symm (w,top))) ⁻¹' Ioi c
  have hTopCont : ContinuousOn (fun w : Z => ρ (e.symm (w,top))) B₀ := by
    apply hρ.continuousOn.comp
      (e.continuousOn_symm.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun w hw => hTgt ((hBox ⟨hw,hTopI⟩).1)))
    intro w hw
    exact ⟨(w,top),(hBox ⟨hw,hTopI⟩).1,rfl⟩
  have hB' : IsOpen B' := hTopCont.isOpen_inter_preimage hB₀ isOpen_Ioi
  have hz' : z ∈ B' := ⟨hz₀,hcTop⟩
  let W := e.symm '' (B' ×ˢ I)
  have hWChart : B' ×ˢ I ⊆ e.target := fun q hq => hTgt (hBox ⟨hq.1.1,hq.2⟩).1
  have hW : IsOpen W := e.isOpen_image_symm_of_subset_target (hB'.prod isOpen_Ioo) hWChart
  have hWV : W ⊆ V := by
    rintro _ ⟨q,hq,rfl⟩
    exact (hBox ⟨hq.1.1,hq.2⟩).2
  let EqPositive := {q ∈ U | 0 < ρ q - c}
  have hPos : IsOpen EqPositive := ((hρ.mono hUQ).sub contDiffOn_const).continuousOn.isOpen_inter_preimage
    hU (t := Ioi 0) isOpen_Ioi
  let R := J ∩ ρ ⁻¹' Ici c
  have hRJ : R ⊆ J := inter_subset_left
  have hRQ : R ⊆ Q := hRJ.trans hJQ
  have hR : IsCompact R :=
    ((hρ.continuousOn.mono hJQ).upperSemicontinuousOn.isCompact_inter_preimage_Ici
      (isCompact_closedBall _ _) c)
  have hTime : ContinuousOn (fun x => (e x).2 - a) R := by
    have hRS : R ⊆ e.source := by
      intro x hx
      obtain ⟨q,hq,rfl⟩ := hRQ hx
      exact e.map_target (hTgt hq)
    exact (continuous_snd.continuousOn.comp (e.continuousOn.mono hRS)
      (fun x hx => mem_univ _)).sub continuousOn_const
  have hTimePos (x : X n × X n) (hx : x ∈ R) : 0 < (e x).2 - a := by
    have hp' : 0 < ρ x := hc.trans_le hx.2
    obtain ⟨q,hq,he⟩ := hRQ hx
    rw [← he,e.right_inv (hTgt hq)]
    exact sub_pos.mpr ((hSign q.1 hq.1 q.2 hq.2).mp (he ▸ hp'))
  obtain ⟨η,hη,hTimeMargin⟩ := Carleman.exists_pos_lower_of_compact hR hTime hTimePos
  let b₀ := min top (a+η/2)
  have hb₀ : a < b₀ := lt_min haTop (by linarith)
  refine ⟨B',d,b₀,hB',hz',inter_subset_left.trans hBase,hd,hb₀,hI,?_⟩
  intro b hb
  let A := productAbove e B S b hi
  have hbTop : b < top := hb.2.trans_le (min_le_left _ _)
  have hA : IsOpen A := isOpen_productAbove e hS (hla.le.trans hb.1) hChart
  have hSideA : EqPositive ⊆ A := by
    intro x hx
    have hxR : x ∈ R := ⟨hUJ hx.1,(sub_pos.mp hx.2).le⟩
    have ht := hTimeMargin x hxR
    have hba : b < a+η/2 := hb.2.trans_le (min_le_right _ _)
    obtain ⟨q,hq,rfl⟩ := hRQ hxR
    rw [e.right_inv (hTgt hq)] at ht
    have hbq : b < q.2 := by linarith
    exact Or.inr ⟨q,⟨hq.1,hbq,hq.2.2⟩,rfl⟩
  let ρt (_ : ℝ) (x : X n × X n) := ρ x - c
  have hρt : ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) :=
    ((hρ.mono hUQ).comp contDiff_snd.contDiffOn (fun _ hq => hq.2)).sub contDiffOn_const
  have hConstAdm : SmoothFamilyOn (fun _ => L₁₀) D₁ ∧ SmoothFamilyOn (fun _ => L₂₀) D₂ ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
      L₁₀ = L₁₀ ∧ L₂₀ = L₂₀ ∧ ∃ c' : ℝ, 0 ≤ c' ∧ c' ≤ ε ∧ ρt 0 = (fun q => ρ q - c') :=
    ⟨smoothFamilyOn_const hL₁₀,smoothFamilyOn_const hL₂₀,hρt,rfl,rfl,c,hc.le,hcε,rfl⟩
  let K := (K₁ ×ˢ K₂) ∪ (K₃ ×ˢ K₄)
  have hKc : IsCompact K := (hK₁.prod hK₂).union (hK₃.prod hK₄)
  obtain ⟨t,ht⟩ := (hArm (fun _ => L₁₀) (fun _ => L₂₀) ρt hConstAdm).exists
  have hKA : K ⊆ A := fun x hx => hSideA ⟨(ht hx).1,hε.trans (ht hx).2⟩
  intro J' hJ' hJc
  obtain ⟨C,hC,hCext⟩ := hExtend J' (hJ'.trans hWV) hJc 0
  refine ⟨K,C,hKc,hKA,hC,fun path => ?_⟩
  have hAdm : SmoothFamilyOn path.left D₁ ∧ SmoothFamilyOn path.right D₂ ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) ∧
      path.left 0 = L₁₀ ∧ path.right 0 = L₂₀ ∧
      ∃ c' : ℝ, 0 ≤ c' ∧ c' ≤ ε ∧ ρt 0 = (fun q => ρ q - c') :=
    ⟨path.smoothLeft,path.smoothRight,hρt,path.referenceLeft,path.referenceRight,c,hc.le,hcε,rfl⟩
  filter_upwards [hCext path.left path.right ρt hAdm] with t hExt F hF M hM hKF
  obtain ⟨G,hG,hEq,hJBound⟩ := hExt F (hF.2.mono hSideA) M hM hKF
  refine ⟨G,⟨hWV.trans (hVU.trans (hUQ.trans hQD)),hG.mono hWV⟩,?_,
    fun x hx => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hJBound 0 le_rfl x hx⟩
  apply scalar_product_eqOn_of_interval_to_seed (hA.inter hW) (hW.inter hPos)
    (inter_subset_left.trans hF.1) (path.smoothLeft.1 t) (path.smoothRight.1 t)
    (hG.mono (inter_subset_right.trans hWV)) (hF.2.mono inter_subset_left)
    (hEq.mono (inter_subset_inter_left _ hWV))
  rintro _ ⟨hqa,⟨q,hqw,rfl⟩⟩
  let f (s : ℝ) := e.symm (q.1,s)
  have hSegI : uIcc q.2 top ⊆ I := by
    rcases le_total q.2 top with h | h
    · rw [uIcc_of_le h]
      exact Icc_subset_Ioo hqw.2.1 hTopI.2
    · rw [uIcc_of_ge h]
      exact Icc_subset_Ioo hTopI.1 hqw.2.2
  have hSegTarget : MapsTo (fun s : ℝ => (q.1,s)) (uIcc q.2 top) e.target :=
    fun s hs => hWChart ⟨hqw.1,hSegI hs⟩
  have hSegW (s : ℝ) (hs : s ∈ uIcc q.2 top) : f s ∈ W := ⟨(q.1,s),⟨hqw.1,hSegI hs⟩,rfl⟩
  have hSegA (s : ℝ) (hs : s ∈ uIcc q.2 top) : f s ∈ A := by
    by_cases hqb : b < q.2
    · have hs' : b < s := (lt_min hqb hbTop).trans_le hs.1
      exact Or.inr ⟨(q.1,s),⟨hBase hqw.1.1,hs',(hI (hSegI hs)).2⟩,rfl⟩
    · have hSeed : e.symm q ∈ S := by
        rcases hqa with h | ⟨q',hq',he⟩
        · exact h
        · have hq'T := hChart ⟨interior_subset hq'.1,(hla.trans_le hb.1).trans hq'.2.1,hq'.2.2⟩
          have hqeq := e.symm.injOn hq'T (hWChart hqw) he
          exact (hqb (hqeq ▸ hq'.2.1)).elim
      have hqt : q.2 ≤ top := (le_of_not_gt hqb).trans hbTop.le
      have hqs : q.2 ≤ s := (uIcc_of_le hqt ▸ hs : s ∈ Icc q.2 top).1
      exact Or.inl (hUp q.1 (interior_subset (hBase hqw.1.1)) q.2 s (hI hqw.2) (hI (hSegI hs)) hqs hSeed)
  refine ⟨q.2,top,f,
    e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn hSegTarget,
    rfl,fun s hs => ⟨hSegA s hs,hSegW s hs⟩,?_⟩
  have hTopW := hSegW top right_mem_uIcc
  exact ⟨hTopW,hVU (hWV hTopW),sub_pos.mpr hqw.1.2⟩

end CalderonPaper

module

public import Proof.Manuscript.ScalarProductGluing
public import Proof.CalderonN.PhaseVertical

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric CalderonN
open scoped Topology ContDiff

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ} [NeZero n]

open Elliptic.PhaseCoordinates

set_option maxHeartbeats 2800000 in
/-- The released second-height direction has a uniform positive slope
on a fixed reference room, also for nearby members of each smooth phase
family matching the reference at parameter zero. -/
theorem exists_reference_monotone_second_height {U : Set (X n × X n)} (hU : IsOpen U)
    (z₀ : X n × X n) (hz₀ : z₀ ∈ U) {ρ : X n × X n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U)
    {θ : X n → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθ₀ : θ z₀.2 = 0)
    (hℓ : fderiv ℝ θ z₀.2 ≠ 0)
    (hjet : fderiv ℝ θ z₀.2 = (fderiv ℝ ρ z₀).comp (ContinuousLinearMap.inr ℝ (X n) (X n)))
    (e : OpenPartialHomeomorph (X n) (ℝ × (fderiv ℝ θ z₀.2).ker)) (he₀ : z₀.2 ∈ e.source)
    (he : ∀ y, e y = (θ y, (fderiv ℝ θ z₀.2).ker.orthogonalProjectionOnto (y-z₀.2))) :
    ∃ d : ℝ, 0 < d ∧ ∀ ρt : ℝ → X n × X n → ℝ,
      ContDiffOn ℝ ∞ (fun q : ℝ × (X n × X n) => ρt q.1 q.2) (univ ×ˢ U) → ρt 0 = ρ →
      ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ ball z₀.1 d,
        ∀ w : (fderiv ℝ θ z₀.2).ker, ‖w‖ < d →
          StrictMonoOn (fun s => ρt t (x,e.symm (s,w))) (Ioo (-d) d) := by
  let K := (fderiv ℝ θ z₀.2).ker
  let p : (X n) × (ℝ × K) := (z₀.1,0,0)
  let H (q : (X n) × (ℝ × K)) := ρ (q.1,e.symm q.2)
  let v : (X n) × (ℝ × K) := (0,1,0)
  obtain ⟨hval,htarget⟩ := chart_symm_zero e he (map_zero _) hθ₀ he₀
  have heSmooth := contDiffAt_tangent_chart_symm hθ z₀.2 hθ₀ hℓ e he₀ he
  have hInner : ContDiffAt ℝ ∞ (fun q : (X n) × (ℝ × K) => (q.1,e.symm q.2)) p :=
    contDiff_fst.contDiffAt.prodMk (heSmooth.comp p contDiff_snd.contDiffAt)
  have hPoint : (p.1,e.symm p.2) = z₀ := Prod.ext rfl hval
  have hSmooth : ContDiffAt ℝ ∞ H p := by
    have hR : ContDiffAt ℝ ∞ ρ (p.1,e.symm p.2) := hPoint.symm ▸ hρ.contDiffAt (hU.mem_nhds hz₀)
    exact hR.comp p hInner
  have hInv : (fun q : ℝ × K => θ (e.symm q)) =ᶠ[𝓝 ((0 : ℝ),(0 : K))] Prod.fst := by
    filter_upwards [e.open_target.mem_nhds htarget] with q hq
    exact (congrArg Prod.fst (he (e.symm q))).symm.trans
      (congrArg Prod.fst (e.right_inv hq))
  have hE := (heSmooth.differentiableAt (by simp)).hasFDerivAt
  have hFirst : (fderiv ℝ θ z₀.2) (fderiv ℝ e.symm (0,0) (1,0)) = 1 := by
    have hθ' : HasFDerivAt θ (fderiv ℝ θ z₀.2) (e.symm (0,0)) :=
      hval.symm ▸ (hθ.differentiable (by simp) z₀.2).hasFDerivAt
    have h := (hθ'.comp ((0 : ℝ),(0 : K)) hE).fderiv
    change fderiv ℝ (fun q => θ (e.symm q)) ((0 : ℝ),(0 : K)) = _ at h
    rw [hInv.fderiv_eq, fderiv_fst] at h
    exact (congrArg (fun D : ℝ × K →L[ℝ] ℝ => D (1,0)) h).symm
  have hPartial : fderiv ℝ H p v = 1 := by
    have hR : HasFDerivAt ρ (fderiv ℝ ρ z₀) (p.1,e.symm p.2) :=
      hPoint.symm ▸ ((hρ.contDiffAt (hU.mem_nhds hz₀)).differentiableAt (by simp)).hasFDerivAt
    have hi : HasFDerivAt (fun q : (X n) × (ℝ × K) => (q.1,e.symm q.2))
        ((ContinuousLinearMap.fst ℝ (X n) (ℝ × K)).prod
          ((fderiv ℝ e.symm (0,0)).comp (ContinuousLinearMap.snd ℝ (X n) (ℝ × K)))) p :=
      (ContinuousLinearMap.fst ℝ (X n) (ℝ × K)).hasFDerivAt.prodMk
        (hE.comp p (ContinuousLinearMap.snd ℝ (X n) (ℝ × K)).hasFDerivAt)
    have hh := (hR.comp p hi).fderiv
    rw [show fderiv ℝ H p = _ from hh]
    change fderiv ℝ ρ z₀ (0, fderiv ℝ e.symm (0,0) (1,0)) = 1
    exact (congrArg (fun d : (X n) →L[ℝ] ℝ => d (fderiv ℝ e.symm (0,0) (1,0))) hjet).symm.trans hFirst

  let E := X n × (ℝ × K)
  let F (q : E) := (q.1,e.symm q.2)
  obtain ⟨V,hV,hFV⟩ := hInner.contDiffOn (m := (2 : ℕ∞ω)) (by simp) (by simp)
  have hpre : F ⁻¹' U ∈ 𝓝 p :=
    hInner.continuousAt.preimage_mem_nhds (hU.mem_nhds (hPoint.symm ▸ hz₀))
  obtain ⟨W,hWV',hW,hpW⟩ := _root_.mem_nhds_iff.mp (inter_mem hV hpre)
  have hFW : ContDiffOn ℝ 2 F W := hFV.mono (fun q hq => (hWV' hq).1)
  have hWU : MapsTo F W U := fun q hq => (hWV' hq).2
  have hpos : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ H q v :=
    (((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp
      (hSmooth.fderiv_right (m := ∞) (by simp)).continuousAt)
      (Ioi_mem_nhds (by change 0 < fderiv ℝ H p v; rw [hPartial]; norm_num))
  obtain ⟨d₀,hd₀,hRoom⟩ := Metric.eventually_nhds_iff.mp (hpos.and (hW.mem_nhds hpW))
  let d := d₀/2
  have hd : 0 < d := half_pos hd₀
  let C := closedBall p d
  have hC : IsCompact C := isCompact_closedBall _ _
  have hCW (q : E) (hq : q ∈ C) : 0 < fderiv ℝ H q v ∧ q ∈ W :=
    hRoom ((mem_closedBall.mp hq).trans_lt (half_lt_self hd₀))
  refine ⟨d,hd,fun ρt hρt heq => ?_⟩
  let Ht (q : ℝ × E) := ρt q.1 (F q.2)
  have hHt : ContDiffOn ℝ 2 Ht (univ ×ˢ W) :=
    (hρt.of_le (by simp)).comp (contDiff_fst.contDiffOn.prodMk
      (hFW.comp contDiff_snd.contDiffOn (fun q hq => hq.2)))
      (fun q hq => ⟨mem_univ _,hWU hq.2⟩)
  have hAt (t : ℝ) (q : E) (hq : q ∈ W) : ContDiffAt ℝ 2 Ht (t,q) :=
    hHt.contDiffAt ((isOpen_univ.prod hW).mem_nhds ⟨mem_univ _,hq⟩)
  have hSlice (t : ℝ) (q : E) (hq : q ∈ W) :
      HasFDerivAt (fun y => Ht (t,y))
        ((fderiv ℝ Ht (t,q)).comp (ContinuousLinearMap.inr ℝ ℝ E)) q :=
    ((hAt t q hq).differentiableAt (by norm_num)).hasFDerivAt.comp q
      ((hasFDerivAt_const t q).prodMk (hasFDerivAt_id q))
  have hEq0 (q : E) (hq : q ∈ W) : fderiv ℝ Ht (0,q) (0,v) = fderiv ℝ H q v := by
    have hEq : (fun y => Ht (0,y)) = H := by funext y; simp [Ht,F,H,heq]
    have h := congrArg (fun T : E →L[ℝ] ℝ => T v) (hSlice 0 q hq).fderiv
    rw [hEq] at h
    exact h.symm
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ q ∈ C, 0 < fderiv ℝ Ht (t,q) (0,v) := by
    apply hC.eventually_forall_of_forall_eventually
    intro q hq
    have hCont : ContinuousAt (fun z : ℝ × E => fderiv ℝ Ht z (0,v)) (0,q) :=
      ((ContinuousLinearMap.apply ℝ ℝ (0,v)).continuous.continuousAt).comp
        ((hAt 0 q (hCW q hq).2).fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuousAt
    exact hCont.preimage_mem_nhds (Ioi_mem_nhds ((hEq0 q (hCW q hq).2).symm ▸ (hCW q hq).1))
  filter_upwards [hev] with t ht x hx w hw
  have hq (s : ℝ) (hs : s ∈ Ioo (-d) d) : (x,s,w) ∈ C := by
    apply mem_closedBall.mpr
    change dist (x,s,w) (z₀.1,0,0) ≤ d
    rw [Prod.dist_eq,Prod.dist_eq,max_le_iff,max_le_iff,dist_zero_right,Real.norm_eq_abs,abs_le,dist_zero_right]
    exact ⟨(mem_ball.mp hx).le,⟨hs.1.le,hs.2.le⟩,hw.le⟩
  have hDeriv (s : ℝ) (hs : s ∈ Ioo (-d) d) :
      HasDerivAt (fun r => ρt t (x,e.symm (r,w))) (fderiv ℝ Ht (t,x,s,w) (0,v)) s := by
    have hLine : HasDerivAt (fun r : ℝ => (x,r,w)) v s :=
      (hasDerivAt_const s x).prodMk ((hasDerivAt_id s).prodMk (hasDerivAt_const s w))
    exact (hSlice t (x,s,w) (hCW _ (hq s hs)).2).comp_hasDerivAt s hLine
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact fun s hs => (hDeriv s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [isOpen_Ioo.interior_eq] at hs
    rw [(hDeriv s hs).deriv]
    exact ht (x,s,w) (hq s hs)

omit [NeZero n] in
/-- The upper input arm intersects every path obtained by increasing
the second height inside the output cylinder. -/
theorem eqOn_scalar_output_positive_side {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph (X n) (ℝ × K)) {A : Set (X n)} (hA : IsOpen A)
    {l ε R : ℝ} (hε : 0 < ε) (_hl : 4 * ε < l) (hR : 0 < R)
    (hOtarget : (roomO l ε R : Set (ℝ × K)) ⊆ e.target)
    {U : Set ((X n) × (X n))} (hU : IsOpen U)
    {ρ : (X n) × (X n) → ℝ} (hρ : ContinuousOn ρ U)
    (hUbox : A ×ˢ (e.symm '' roomO l ε R) ⊆ U)
    (hmono : ∀ x ∈ A, ∀ w ∈ ball (0 : K) (R / 2),
      StrictMonoOn (fun s => ρ (x,e.symm (s,w))) (Ioo (-ε) (l + 3 * ε / 2)))
    {L₁ L₂ : ScalarElliptic n} (hL₁ : L₁.SmoothOn univ) (hL₂ : L₂.SmoothOn univ)
    {F G : (X n) × (X n) → ℝ}
    (hF : L₁.ProductSolvesOn L₂ {q ∈ U | 0 < ρ q} F)
    (hG : L₁.ProductSolvesOn L₂ (A ×ˢ (e.symm '' roomO l ε R)) G)
    {S : Set (X n)} (hS : IsOpen S) (hStop : e.symm '' roomStop l ε R ⊆ S)
    (heq : EqOn G F (A ×ˢ (e.symm '' roomO l ε R ∩ S))) :
    EqOn G F ((A ×ˢ (e.symm '' roomO l ε R)) ∩ {q ∈ U | 0 < ρ q}) := by
  have hO : IsOpen (e.symm '' roomO l ε R) :=
    e.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_ball) hOtarget
  let V := {q ∈ U | 0 < ρ q}
  have hV : IsOpen V := hρ.isOpen_inter_preimage hU (t := Ioi 0) isOpen_Ioi
  refine scalar_product_eqOn_of_interval_to_seed ((hA.prod hO).inter hV) (hA.prod (hO.inter hS))
    (fun _ _ => ⟨mem_univ _,mem_univ _⟩) hL₁ hL₂ (hG.mono inter_subset_left) (hF.mono inter_subset_right) heq ?_
  rintro ⟨x,y⟩ ⟨⟨hx,⟨⟨s,w⟩,hsw,rfl⟩⟩,hy⟩
  have hs : s ∈ Ioo (-ε) (l + 3 * ε / 2) := hsw.1
  have hw : w ∈ ball (0 : K) (R / 2) := hsw.2
  let b := max s (l + 5 * ε / 4)
  let f (t : ℝ) := (x,e.symm (t,w))
  have hsb : s ≤ b := le_max_left _ _
  have hb : b ∈ Ioo (-ε) (l + 3 * ε / 2) :=
    ⟨hs.1.trans_le hsb, max_lt hs.2 (by linarith)⟩
  have hI : uIcc s b ⊆ Ioo (-ε) (l + 3 * ε / 2) := by
    rw [uIcc_of_le hsb]
    exact Icc_subset_Ioo hs.1 hb.2
  have hfO (t : ℝ) (ht : t ∈ uIcc s b) : f t ∈ A ×ˢ (e.symm '' roomO l ε R) :=
    ⟨hx,⟨(t,w),⟨hI ht,hw⟩,rfl⟩⟩
  refine ⟨s,b,f,?_,rfl,?_,?_⟩
  · exact continuousOn_const.prodMk
      ((e.continuousOn_symm).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => hOtarget ⟨hI ht,hw⟩))
  · intro t ht
    have hst : s ≤ t := (uIcc_of_le hsb ▸ ht : t ∈ Icc s b).1
    refine ⟨hfO t ht,hUbox (hfO t ht),hy.2.trans_le ((hmono x hx w hw).monotoneOn hs (hI ht) hst)⟩
  · refine ⟨hx,(hfO b right_mem_uIcc).2,hStop ⟨(b,w),?_,rfl⟩⟩
    change (b,w) ∈ Ioo (l + ε / 2) (l + 7 * ε / 2) ×ˢ ball (0 : K) (7 * R / 8)
    refine ⟨⟨(show l + ε / 2 < l + 5 * ε / 4 by linarith).trans_le (le_max_right _ _),
      hb.2.trans (by linarith)⟩, ball_subset_ball (by linarith) hw⟩

end CalderonPaper.ScalarElliptic

module

public import Proof.CalderonN.PhaseRooms
public import Proof.CalderonN.ProductGluing

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace CalderonN.Elliptic.PhaseCoordinates

variable {dim : ℕ} [NeZero dim]

/-- The second chart coordinate points strictly into the old side on
a whole box. Its derivative at the centre is one, by the prescribed
first jet and the right inverse identity for the chart. -/
theorem exists_monotone_second_height {U : Set ((X dim) × (X dim))} (hU : IsOpen U)
    (z₀ : (X dim) × (X dim)) (hz₀ : z₀ ∈ U) {ρ : (X dim) × (X dim) → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U)
    {θ : (X dim) → ℝ} (hθ : ContDiff ℝ ∞ θ) (hθ₀ : θ z₀.2 = 0)
    (hℓ : fderiv ℝ θ z₀.2 ≠ 0)
    (hjet : fderiv ℝ θ z₀.2 = (fderiv ℝ ρ z₀).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim)))
    (e : OpenPartialHomeomorph (X dim) (ℝ × (fderiv ℝ θ z₀.2).ker)) (he₀ : z₀.2 ∈ e.source)
    (he : ∀ y, e y = (θ y, (fderiv ℝ θ z₀.2).ker.orthogonalProjectionOnto (y-z₀.2))) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ ball z₀.1 d, ∀ w : (fderiv ℝ θ z₀.2).ker, ‖w‖ < d →
      StrictMonoOn (fun s => ρ (x,e.symm (s,w))) (Ioo (-d) d) := by
  let K := (fderiv ℝ θ z₀.2).ker
  let p : (X dim) × (ℝ × K) := (z₀.1,0,0)
  let H (q : (X dim) × (ℝ × K)) := ρ (q.1,e.symm q.2)
  let v : (X dim) × (ℝ × K) := (0,1,0)
  obtain ⟨hval,htarget⟩ := chart_symm_zero e he (map_zero _) hθ₀ he₀
  have heSmooth := contDiffAt_tangent_chart_symm hθ z₀.2 hθ₀ hℓ e he₀ he
  have hInner : ContDiffAt ℝ ∞ (fun q : (X dim) × (ℝ × K) => (q.1,e.symm q.2)) p :=
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
    have hi : HasFDerivAt (fun q : (X dim) × (ℝ × K) => (q.1,e.symm q.2))
        ((ContinuousLinearMap.fst ℝ (X dim) (ℝ × K)).prod
          ((fderiv ℝ e.symm (0,0)).comp (ContinuousLinearMap.snd ℝ (X dim) (ℝ × K)))) p :=
      (ContinuousLinearMap.fst ℝ (X dim) (ℝ × K)).hasFDerivAt.prodMk
        (hE.comp p (ContinuousLinearMap.snd ℝ (X dim) (ℝ × K)).hasFDerivAt)
    have hh := (hR.comp p hi).fderiv
    rw [show fderiv ℝ H p = _ from hh]
    change fderiv ℝ ρ z₀ (0, fderiv ℝ e.symm (0,0) (1,0)) = 1
    exact (congrArg (fun d : (X dim) →L[ℝ] ℝ => d (fderiv ℝ e.symm (0,0) (1,0))) hjet).symm.trans hFirst
  have hpos : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ H q v :=
    (((ContinuousLinearMap.apply ℝ ℝ v).continuous.continuousAt).comp
      (hSmooth.fderiv_right (m := ∞) (by simp)).continuousAt) (Ioi_mem_nhds (by change 0 < fderiv ℝ H p v; rw [hPartial]; norm_num))
  have hdiff : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ H q :=
    ((hSmooth.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)).mono
      (fun _ h => h.differentiableAt (by simp))
  obtain ⟨d,hd,hball⟩ := Metric.eventually_nhds_iff.mp (hpos.and hdiff)
  refine ⟨d,hd,fun x hx w hw => ?_⟩
  have hAt (s : ℝ) (hs : s ∈ Ioo (-d) d) : 0 < fderiv ℝ H (x,s,w) v ∧ DifferentiableAt ℝ H (x,s,w) := by
    apply hball
    change dist (x,s,w) (z₀.1,0,0) < d
    rw [Prod.dist_eq,Prod.dist_eq,max_lt_iff,max_lt_iff,dist_zero_right,Real.norm_eq_abs,abs_lt,dist_zero_right]
    exact ⟨mem_ball.mp hx,hs,hw⟩
  have hDeriv (s : ℝ) (hs : s ∈ Ioo (-d) d) :
      HasDerivAt (fun t => ρ (x,e.symm (t,w))) (fderiv ℝ H (x,s,w) v) s := by
    have hLine : HasDerivAt (fun t : ℝ => (x,t,w)) v s :=
      (hasDerivAt_const s x).prodMk ((hasDerivAt_id s).prodMk (hasDerivAt_const s w))
    exact (hAt s hs).2.hasFDerivAt.comp_hasDerivAt s hLine
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · exact fun s hs => (hDeriv s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [isOpen_Ioo.interior_eq] at hs
    rw [(hDeriv s hs).deriv]
    exact (hAt s hs).1

/-- The upper input arm intersects every path obtained by increasing
the second height inside the output cylinder. -/
theorem eqOn_output_positive_side {K : Type*} [NormedAddCommGroup K]
    (e : OpenPartialHomeomorph (X dim) (ℝ × K)) {A : Set (X dim)} (hA : IsOpen A)
    {l ε R : ℝ} (hε : 0 < ε) (_hl : 4 * ε < l) (hR : 0 < R)
    (hOtarget : (roomO l ε R : Set (ℝ × K)) ⊆ e.target)
    {U : Set ((X dim) × (X dim))} (hU : IsOpen U)
    {ρ : (X dim) × (X dim) → ℝ} (hρ : ContinuousOn ρ U)
    (hUbox : A ×ˢ (e.symm '' roomO l ε R) ⊆ U)
    (hmono : ∀ x ∈ A, ∀ w ∈ ball (0 : K) (R / 2),
      StrictMonoOn (fun s => ρ (x,e.symm (s,w))) (Ioo (-ε) (l + 3 * ε / 2)))
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    {F G : (X dim) × (X dim) → ℝ}
    (hF : ProductSolutionOn g₁ g₂ {q ∈ U | 0 < ρ q} F)
    (hG : ProductSolutionOn g₁ g₂ (A ×ˢ (e.symm '' roomO l ε R)) G)
    {S : Set (X dim)} (hS : IsOpen S) (hStop : e.symm '' roomStop l ε R ⊆ S)
    (heq : EqOn G F (A ×ˢ (e.symm '' roomO l ε R ∩ S))) :
    EqOn G F ((A ×ˢ (e.symm '' roomO l ε R)) ∩ {q ∈ U | 0 < ρ q}) := by
  have hO : IsOpen (e.symm '' roomO l ε R) :=
    e.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_ball) hOtarget
  let V := {q ∈ U | 0 < ρ q}
  have hV : IsOpen V := hρ.isOpen_inter_preimage hU (t := Ioi 0) isOpen_Ioi
  refine product_eqOn_of_interval_to_seed ((hA.prod hO).inter hV) (hA.prod (hO.inter hS))
    (fun _ _ => ⟨mem_univ _,mem_univ _⟩) hg₁ hg₂ (hG.mono inter_subset_left) (hF.mono inter_subset_right) heq ?_
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

end CalderonN.Elliptic.PhaseCoordinates

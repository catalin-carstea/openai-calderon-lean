module

public import Proof.CalderonN.ConnectionSecondBounds
public import Proof.CalderonN.LocalFlowVariation
public import Proof.CalderonN.CoordinateSprayBounds

import Mathlib.Tactic

/-! Adapted from `CoordinateSpraySecondBounds` in the checked Proposition 5.3 release. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- The exact second derivative of the genuine coordinate geodesic spray. -/
lemma Elliptic.second_fderiv_coordinateGeodesicSpray {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (p : (X dim) × (X dim)) (hp : p.1 ∈ Ω)
    (a b c d : (X dim)) :
    fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p (c,d) (a,b) =
      (0,-((connectionBilinear g p.1 d b+
          fderiv ℝ (connectionBilinear g) p.1 c p.2 b)+
        ((connectionBilinear g p.1 b d+
          fderiv ℝ (connectionBilinear g) p.1 c b p.2)+
        (fderiv ℝ (connectionBilinear g) p.1 a p.2 d+
          (fderiv ℝ (connectionBilinear g) p.1 a d p.2+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 p.2))))) := by
  have hΓ := (hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hp)
  have hDΓ := hΓ.fderiv_right (m:=∞) (by simp)
  have hdΓ := hΓ.differentiableAt (by simp)
  have hddΓ := hDΓ.differentiableAt (by simp)
  have hFst := hasFDerivAt_fst (𝕜:=ℝ) (p:=p)
  have hV := hasFDerivAt_snd (𝕜:=ℝ) (p:=p)
  have hA := hdΓ.hasFDerivAt.comp p hFst
  have hDA := hddΓ.hasFDerivAt.comp p hFst
  have hT1 := (hA.clm_apply hV).clm_apply (hasFDerivAt_const b p)
  have hT2 := (hA.clm_apply (hasFDerivAt_const b p)).clm_apply hV
  have hT3 := ((hDA.clm_apply (hasFDerivAt_const a p)).clm_apply hV).clm_apply hV
  have hR := (hasFDerivAt_const b p).prodMk ((hT1.add (hT2.add hT3)).neg)
  let G : (X dim) × (X dim) → (X dim) × (X dim) := fun q =>
    (b,-(connectionBilinear g q.1 q.2 b+
      (connectionBilinear g q.1 b q.2+fderiv ℝ (connectionBilinear g) q.1 a q.2 q.2)))
  have hNear : (fun q => fderiv ℝ (coordinateGeodesicSpray g) q (a,b)) =ᶠ[𝓝 p] G := by
    filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hp] with q hq
    exact fderiv_coordinateGeodesicSpray g q
      (((hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hq)).differentiableAt (by simp)) a b
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK p hp
  rw [← fderiv_apply_const_of_contDiffAt (coordinateGeodesicSpray g) p (a,b) (c,d) hSpray,
    hNear.fderiv_eq]
  have hRG : HasFDerivAt G _ p := hR
  rw [hRG.fderiv]
  simp only [ContinuousLinearMap.prod_apply,_root_.neg_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.fst,ContinuousLinearMap.snd,
    Function.comp_def,map_zero,zero_add,zero_apply]
  rfl

lemma norm_quadrilinear_apply_le (L : (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim) →L[ℝ] (X dim)) (a b c d : (X dim)) :
    ‖L a b c d‖ ≤ ‖L‖*‖a‖*‖b‖*‖c‖*‖d‖ :=
  (norm_trilinear_apply_le (L a) b c d).trans (by gcongr; exact L.le_opNorm a)

/-- A pointwise second-spray bound using only the actual connection jets and speed. -/
theorem Elliptic.norm_second_coordinateGeodesicSpray_apply_le {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ}
    {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (p J L : (X dim) × (X dim)) (hp : p.1 ∈ Ω)
    (C D E V : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) (hV : 0 ≤ V)
    (hΓ0 : ‖connectionBilinear g p.1‖ ≤ C)
    (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hΓ2 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖ ≤ E)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) p L J‖ ≤
      (2*C+4*D*V+E*V^2)*‖J‖*‖L‖ := by
  rcases J with ⟨a,b⟩
  rcases L with ⟨c,d⟩
  have ha : ‖a‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_fst_le ((a,b):(X dim) × (X dim))
  have hb : ‖b‖ ≤ ‖((a,b):(X dim) × (X dim))‖ := norm_snd_le ((a,b):(X dim) × (X dim))
  have hc : ‖c‖ ≤ ‖((c,d):(X dim) × (X dim))‖ := norm_fst_le ((c,d):(X dim) × (X dim))
  have hd : ‖d‖ ≤ ‖((c,d):(X dim) × (X dim))‖ := norm_snd_le ((c,d):(X dim) × (X dim))
  have hZero (u v : (X dim)) (hu : ‖u‖ ≤ ‖((a,b):(X dim) × (X dim))‖) (hv : ‖v‖ ≤ ‖((c,d):(X dim) × (X dim))‖) :
      ‖connectionBilinear g p.1 u v‖ ≤ C*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ :=
    (norm_bilinear_apply_le _ u v).trans (by gcongr)
  have hOne (u v w : (X dim)) (hu : ‖u‖ ≤ ‖((a,b):(X dim) × (X dim))‖)
      (hv : ‖v‖ ≤ ‖((c,d):(X dim) × (X dim))‖) (hw : ‖w‖ ≤ V) :
      ‖fderiv ℝ (connectionBilinear g) p.1 u v w‖ ≤
        D*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖*V :=
    (norm_trilinear_apply_le _ u v w).trans (by gcongr)
  have hT1 : ‖connectionBilinear g p.1 d b‖ ≤ C*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ := by
    have hh : ‖connectionBilinear g p.1 d b‖ ≤ C*‖((c,d):(X dim) × (X dim))‖*‖((a,b):(X dim) × (X dim))‖ :=
      (norm_bilinear_apply_le _ d b).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT2 : ‖fderiv ℝ (connectionBilinear g) p.1 c p.2 b‖ ≤
      D*V*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 c p.2 b‖ ≤
        D*‖((c,d):(X dim) × (X dim))‖*V*‖((a,b):(X dim) × (X dim))‖ :=
      (norm_trilinear_apply_le _ c p.2 b).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT3 := hZero b d hb hd
  have hT4 : ‖fderiv ℝ (connectionBilinear g) p.1 c b p.2‖ ≤
      D*V*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 c b p.2‖ ≤
        D*‖((c,d):(X dim) × (X dim))‖*‖((a,b):(X dim) × (X dim))‖*V :=
      (norm_trilinear_apply_le _ c b p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT5 : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 d‖ ≤
      D*V*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 a p.2 d‖ ≤
        D*‖((a,b):(X dim) × (X dim))‖*V*‖((c,d):(X dim) × (X dim))‖ :=
      (norm_trilinear_apply_le _ a p.2 d).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT6 : ‖fderiv ℝ (connectionBilinear g) p.1 a d p.2‖ ≤
      D*V*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ :=
    (hOne a d p.2 ha hd hSpeed).trans_eq (by ring)
  have hT7 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 p.2‖ ≤
      E*V^2*‖((a,b):(X dim) × (X dim))‖*‖((c,d):(X dim) × (X dim))‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 p.2‖ ≤
        E*‖((c,d):(X dim) × (X dim))‖*‖((a,b):(X dim) × (X dim))‖*V*V :=
      (norm_quadrilinear_apply_le _ c a p.2 p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  rw [hg.second_fderiv_coordinateGeodesicSpray hΩ hK p hp a b c d,Prod.norm_mk,norm_zero,norm_neg]
  apply max_le (by positivity)
  refine ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
    ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
      ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))))))).trans ?_
  linarith only [hT1,hT2,hT3,hT4,hT5,hT6,hT7]

end CalderonN

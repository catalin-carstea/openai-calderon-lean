import Proof.CoordinateSpraySecondBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The actual third derivative of the coordinate spray, with joint position
    and velocity directions kept separate. -/
lemma Elliptic.third_fderiv_coordinateGeodesicSpray {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (p : X × X) (hp : p.1 ∈ Ω)
    (a b c d e f : X) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) p (e,f) (c,d) (a,b) =
      (0,-((fderiv ℝ (connectionBilinear g) p.1 e d b+
          (fderiv ℝ (connectionBilinear g) p.1 c f b+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c p.2 b))+
        ((fderiv ℝ (connectionBilinear g) p.1 e b d+
          (fderiv ℝ (connectionBilinear g) p.1 c b f+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c b p.2))+
        ((fderiv ℝ (connectionBilinear g) p.1 a f d+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a p.2 d)+
          ((fderiv ℝ (connectionBilinear g) p.1 a d f+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a d p.2)+
            (fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 f+
              (fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a f p.2+
                fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) p.1 e c a p.2 p.2))))))) := by
  have hΓ := (hg.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hp)
  have hDΓ := hΓ.fderiv_right (m:=∞) (by simp)
  have hDDΓ := hDΓ.fderiv_right (m:=∞) (by simp)
  have hFst := hasFDerivAt_fst (𝕜:=ℝ) (p:=p)
  have hV := hasFDerivAt_snd (𝕜:=ℝ) (p:=p)
  have hA := (hΓ.differentiableAt (by simp)).hasFDerivAt.comp p hFst
  have hDA := (hDΓ.differentiableAt (by simp)).hasFDerivAt.comp p hFst
  have hDDA := (hDDΓ.differentiableAt (by simp)).hasFDerivAt.comp p hFst
  have hT1 := (hA.clm_apply (hasFDerivAt_const d p)).clm_apply (hasFDerivAt_const b p)
  have hT2 := ((hDA.clm_apply (hasFDerivAt_const c p)).clm_apply hV).clm_apply (hasFDerivAt_const b p)
  have hT3 := (hA.clm_apply (hasFDerivAt_const b p)).clm_apply (hasFDerivAt_const d p)
  have hT4 := ((hDA.clm_apply (hasFDerivAt_const c p)).clm_apply (hasFDerivAt_const b p)).clm_apply hV
  have hT5 := ((hDA.clm_apply (hasFDerivAt_const a p)).clm_apply hV).clm_apply (hasFDerivAt_const d p)
  have hT6 := ((hDA.clm_apply (hasFDerivAt_const a p)).clm_apply (hasFDerivAt_const d p)).clm_apply hV
  have hT7 := (((hDDA.clm_apply (hasFDerivAt_const c p)).clm_apply (hasFDerivAt_const a p)).clm_apply hV).clm_apply hV
  have hR := (hasFDerivAt_const (0:X) p).prodMk ((hT1.add hT2).add
    ((hT3.add hT4).add (hT5.add (hT6.add hT7)))).neg
  let G : X × X → X × X := fun q =>
    (0,-((connectionBilinear g q.1 d b+fderiv ℝ (connectionBilinear g) q.1 c q.2 b)+
      ((connectionBilinear g q.1 b d+fderiv ℝ (connectionBilinear g) q.1 c b q.2)+
        (fderiv ℝ (connectionBilinear g) q.1 a q.2 d+
          (fderiv ℝ (connectionBilinear g) q.1 a d q.2+
            fderiv ℝ (fderiv ℝ (connectionBilinear g)) q.1 c a q.2 q.2)))))
  have hNear : (fun q => fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g)) q (c,d) (a,b)) =ᶠ[𝓝 p] G := by
    filter_upwards [(hΩ.preimage continuous_fst).mem_nhds hp] with q hq
    exact hg.second_fderiv_coordinateGeodesicSpray hΩ hK q hq a b c d
  have hSpray := hg.contDiffAt_coordinateGeodesicSpray hΩ hK p hp
  have hDD := ((hSpray.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).differentiableAt (by simp)
  have hEval := (hDD.hasFDerivAt.clm_apply (hasFDerivAt_const (c,d) p)).clm_apply (hasFDerivAt_const (a,b) p)
  have hEvalValue := congrArg (fun L => L (e,f)) hEval.fderiv
  simp only [_root_.add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add] at hEvalValue
  rw [← hEvalValue,hNear.fderiv_eq]
  have hRG : HasFDerivAt G _ p := hR
  rw [hRG.fderiv]
  simp only [ContinuousLinearMap.prod_apply,_root_.neg_apply,_root_.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.fst,ContinuousLinearMap.snd,
    Function.comp_def,map_zero,zero_add,zero_apply]
  rfl

lemma norm_quintilinear_apply_le
    (L : X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] X →L[ℝ] X) (a b c d e : X) :
    ‖L a b c d e‖ ≤ ‖L‖*‖a‖*‖b‖*‖c‖*‖d‖*‖e‖ :=
  (norm_quadrilinear_apply_le (L a) b c d e).trans (by gcongr; exact L.le_opNorm a)

/-- The third spray derivative has a uniform trilinear bound from connection
    jets through three and a speed bound. -/
theorem Elliptic.norm_third_coordinateGeodesicSpray_apply_le {Ω : Set X} (hΩ : IsOpen Ω) {K : ℝ}
    {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K) (p J L M : X × X) (hp : p.1 ∈ Ω)
    (D E F V : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hV : 0 ≤ V)
    (hΓ1 : ‖fderiv ℝ (connectionBilinear g) p.1‖ ≤ D)
    (hΓ2 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1‖ ≤ E)
    (hΓ3 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) p.1‖ ≤ F)
    (hSpeed : ‖p.2‖ ≤ V) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (coordinateGeodesicSpray g))) p M L J‖ ≤
      (6*D+6*E*V+F*V^2)*‖J‖*‖L‖*‖M‖ := by
  rcases J with ⟨a,b⟩
  rcases L with ⟨c,d⟩
  rcases M with ⟨e,f⟩
  have ha : ‖a‖ ≤ ‖((a,b):X × X)‖ := norm_fst_le ((a,b):X × X)
  have hb : ‖b‖ ≤ ‖((a,b):X × X)‖ := norm_snd_le ((a,b):X × X)
  have hc : ‖c‖ ≤ ‖((c,d):X × X)‖ := norm_fst_le ((c,d):X × X)
  have hd : ‖d‖ ≤ ‖((c,d):X × X)‖ := norm_snd_le ((c,d):X × X)
  have he : ‖e‖ ≤ ‖((e,f):X × X)‖ := norm_fst_le ((e,f):X × X)
  have hf : ‖f‖ ≤ ‖((e,f):X × X)‖ := norm_snd_le ((e,f):X × X)
  have hT1 : ‖fderiv ℝ (connectionBilinear g) p.1 e d b‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 e d b‖ ≤ D*‖((e,f):X × X)‖*‖((c,d):X × X)‖*‖((a,b):X × X)‖ :=
      (norm_trilinear_apply_le _ e d b).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT2 : ‖fderiv ℝ (connectionBilinear g) p.1 c f b‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 c f b‖ ≤ D*‖((c,d):X × X)‖*‖((e,f):X × X)‖*‖((a,b):X × X)‖ :=
      (norm_trilinear_apply_le _ c f b).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT3 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c p.2 b‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c p.2 b‖ ≤ E*‖((e,f):X × X)‖*‖((c,d):X × X)‖*V*‖((a,b):X × X)‖ :=
      (norm_quadrilinear_apply_le _ e c p.2 b).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT4 : ‖fderiv ℝ (connectionBilinear g) p.1 e b d‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 e b d‖ ≤ D*‖((e,f):X × X)‖*‖((a,b):X × X)‖*‖((c,d):X × X)‖ :=
      (norm_trilinear_apply_le _ e b d).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT5 : ‖fderiv ℝ (connectionBilinear g) p.1 c b f‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 c b f‖ ≤ D*‖((c,d):X × X)‖*‖((a,b):X × X)‖*‖((e,f):X × X)‖ :=
      (norm_trilinear_apply_le _ c b f).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT6 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c b p.2‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e c b p.2‖ ≤ E*‖((e,f):X × X)‖*‖((c,d):X × X)‖*‖((a,b):X × X)‖*V :=
      (norm_quadrilinear_apply_le _ e c b p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT7 : ‖fderiv ℝ (connectionBilinear g) p.1 a f d‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 a f d‖ ≤ D*‖((a,b):X × X)‖*‖((e,f):X × X)‖*‖((c,d):X × X)‖ :=
      (norm_trilinear_apply_le _ a f d).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT8 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a p.2 d‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a p.2 d‖ ≤ E*‖((e,f):X × X)‖*‖((a,b):X × X)‖*V*‖((c,d):X × X)‖ :=
      (norm_quadrilinear_apply_le _ e a p.2 d).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT9 : ‖fderiv ℝ (connectionBilinear g) p.1 a d f‖ ≤ (D)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (connectionBilinear g) p.1 a d f‖ ≤ D*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ :=
      (norm_trilinear_apply_le _ a d f).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT10 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a d p.2‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 e a d p.2‖ ≤ E*‖((e,f):X × X)‖*‖((a,b):X × X)‖*‖((c,d):X × X)‖*V :=
      (norm_quadrilinear_apply_le _ e a d p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT11 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 f‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a p.2 f‖ ≤ E*‖((c,d):X × X)‖*‖((a,b):X × X)‖*V*‖((e,f):X × X)‖ :=
      (norm_quadrilinear_apply_le _ c a p.2 f).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT12 : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a f p.2‖ ≤ (E*V)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (connectionBilinear g)) p.1 c a f p.2‖ ≤ E*‖((c,d):X × X)‖*‖((a,b):X × X)‖*‖((e,f):X × X)‖*V :=
      (norm_quadrilinear_apply_le _ c a f p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  have hT13 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) p.1 e c a p.2 p.2‖ ≤ (F*V^2)*‖((a,b):X × X)‖*‖((c,d):X × X)‖*‖((e,f):X × X)‖ := by
    have hh : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (connectionBilinear g))) p.1 e c a p.2 p.2‖ ≤ F*‖((e,f):X × X)‖*‖((c,d):X × X)‖*‖((a,b):X × X)‖*V*V :=
      (norm_quintilinear_apply_le _ e c a p.2 p.2).trans (by gcongr)
    exact hh.trans_eq (by ring)
  rw [hg.third_fderiv_coordinateGeodesicSpray hΩ hK p hp a b c d e f,
    Prod.norm_mk,norm_zero,norm_neg]
  apply max_le (by positivity)
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)))) ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)))) ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)) ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)) ((norm_add_le _ _).trans (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)))))))))))).trans ?_
  linarith only [hT1,hT2,hT3,hT4,hT5,hT6,hT7,hT8,hT9,hT10,hT11,hT12,hT13]

end ShrinkingSpheres

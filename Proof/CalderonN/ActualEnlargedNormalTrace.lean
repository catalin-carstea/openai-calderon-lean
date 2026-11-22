module

public import Proof.CalderonN.ParametricMetricBallDirichlet
public import Proof.CalderonN.NormalizedBallMetric

import Proof.CalderonN.NormalInverse
import Proof.CalderonN.ChartBilinear
import Mathlib.Tactic

/-! Adapted from `ActualEnlargedNormalTrace` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2400000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

set_option maxHeartbeats 1900000 in
/-- The boundary trace of a solution on a slightly enlarged normal ball
approaches the prescribed data on the original sphere. All positive
enlargements give a harmonic function on a neighborhood of the original
closed ball. -/
theorem exists_enlarged_normalTrace_family
    {Y Ω : Set (X dim)} {γ g : (MetricField dim)} (hg : SmoothMetric univ g)
    {ρ : ℝ} {E : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => ρ))
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i = j then 1 else 0)
    {r : (X dim) → ℝ} (hr : 0 < r y) (hR : r y < ρ)
    {a : (X dim) → ℝ} (ha : smoothNear a (sphereAt γ y)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ u : ℝ → (X dim) → ℝ,
      ContinuousOn (fun p : ℝ × ↥(standardSphere dim) =>
        u p.1 (endpoint E r (y,frameVector e y p.2)))
        (Icc (0:ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))) ∧
      (∀ w : ↥(standardSphere dim),
        u 0 (endpoint E r (y,frameVector e y w)) = a (frameVector e y w)) ∧
      ∀ t ∈ Ioc (0:ℝ) ε, ∃ U : Set (X dim),
        IsOpen U ∧ closedBallImage γ E r y ⊆ U ∧ Harmonic U g (u t) := by
  let s (t : ℝ) := (1+t)*r y
  let F (t : ℝ) := normalBallChartMap E e y (s t)
  let M (q : ℝ × (X dim)) : (Mat dim) := pullbackMetric g (F q.1) q.2
  let U : Set (ℝ × (X dim)) := {q | 0 < s q.1 ∧ s q.1 < ρ ∧ s q.1 * ‖q.2‖ < ρ}
  let C := closedBall (0 : (X dim)) 1
  have hs : ContDiff ℝ ∞ s := (contDiff_const.add contDiff_id).mul contDiff_const
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (hs.continuous.comp continuous_fst)).inter
    ((isOpen_lt (hs.continuous.comp continuous_fst) continuous_const).inter
      (isOpen_lt ((hs.continuous.comp continuous_fst).mul continuous_snd.norm) continuous_const))
  have hUC : {(0:ℝ)} ×ˢ C ⊆ U := by
    intro q hq
    have ht : q.1 = 0 := hq.1
    have hn : ‖q.2‖ ≤ 1 := mem_closedBall_zero_iff.mp hq.2
    change 0 < s q.1 ∧ s q.1 < ρ ∧ s q.1 * ‖q.2‖ < ρ
    rw [ht,show s 0 = r y by simp [s]]
    exact ⟨hr,hR,((mul_le_mul_of_nonneg_left hn hr.le).trans_eq (mul_one _)).trans_lt hR⟩
  have hM (i j : (I dim)) : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => M q i j) := by
    let e' : (Frame dim) := fun _ => e y
    let p (q : ℝ × (X dim)) : ℝ × ((X dim) × (ℝ × (X dim))) := (0,(y,(s q.1,q.2)))
    have hp : ContDiff ℝ ∞ p := contDiff_const.prodMk
      (contDiff_const.prodMk ((hs.comp contDiff_fst).prodMk contDiff_snd))
    have h0 := contDiff_normalizedBallMetric_family_entry
      (E := fun _ => E) (e := fun _ => e') (g := fun _ => g)
      (hE.comp contDiff_snd) (fun _ => contDiff_const) (fun i j => (contDiffOn_univ.mp (hg.1 i j)).comp contDiff_snd) i j
    have hU := h0.comp hp
    change ContDiff ℝ ∞ (fun q : ℝ × (X dim) => normalizedBallMetric g E e y (s q.1) q.2 i j) at hU
    have hN₀ := hU
    have heq (q : ℝ × (X dim)) : M q i j = (s q.1)^2 * normalizedBallMetric g E e y (s q.1) q.2 i j := by
      change pullbackMetric g (normalBallChartMap E e y (s q.1)) q.2 i j = _
      rw [pullbackMetric_normalBallChartMap hE]
      rfl
    simp_rw [heq]
    exact ((hs.comp contDiff_fst).pow 2).mul hN₀
  have hPos (q : ℝ × (X dim)) (hq : q ∈ U) : (M q).PosDef := by
    have hp : 0 < s q.1 := hq.1
    obtain ⟨_,hMap,hD⟩ := normalBallChartMap_on_openBall hE hN hy he hp
    have hqB : q.2 ∈ ball (0 : (X dim)) (ρ/s q.1) := by
      apply mem_ball_zero_iff.mpr
      exact (lt_div_iff₀ hp).mpr (by simpa only [mul_comm] using hq.2.2)
    exact (smoothMetric_pullbackMetric hg (contDiff_normalBallChartMap hE e y (s q.1))
      (hMap.mono_right (subset_univ Ω)) (fun z hz => coordinateJacobian_det_ne_zero (hD z hz))).2 q.2 hqB
  let d (q : ℝ × (X dim)) := a (frameVector e y q.2)
  obtain ⟨S,hS,hAS,haS⟩ := ha
  let T : Set (ℝ × (X dim)) := (fun q : ℝ × (X dim) => frameVector e y q.2) ⁻¹' S
  have htVec : ContDiff ℝ ∞ (fun q : ℝ × (X dim) => frameVector e y q.2) :=
    by simpa only [Function.comp_def, frameVectorL_apply_frame] using
      (frameVectorL (e y)).contDiff.comp contDiff_snd
  have hT : IsOpen T := hS.preimage htVec.continuous
  have hTS : {(0:ℝ)} ×ˢ (standardSphere dim) ⊆ T :=
    fun q hq => hAS (frameVector_mem_sphere γ e y he ⟨q.2,hq.2⟩)
  have hd : ContDiffOn ℝ ∞ d T := haS.comp htVec.contDiffOn (fun q hq => hq)
  obtain ⟨V,hV,h0,b,hb,hBs,hBC,_⟩ := exists_local_parametric_metricBallDirichlet
    hU hT 0 hUC hTS (fun i j => (hM i j).contDiffOn) hPos hd
  let J := V ∩ {t | 0 < s t ∧ s t < ρ}
  have hJ : IsOpen J := hV.inter
    ((isOpen_lt continuous_const hs.continuous).inter (isOpen_lt hs.continuous continuous_const))
  have h0J : (0:ℝ) ∈ J := ⟨h0,by simpa [s] using And.intro hr hR⟩
  obtain ⟨η,hη,hηJ⟩ := Metric.isOpen_iff.mp hJ 0 h0J
  let ε := η/2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεJ : Icc (0:ℝ) ε ⊆ J := by
    intro t ht
    apply hηJ
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht.1]
    dsimp only [ε] at ht
    linarith [ht.2]
  have hExist (t : ℝ) (ht : t ∈ Icc (0:ℝ) ε) :
      ∃ u : (X dim) → ℝ, HarmonicOnBall g (closedBallImage γ E (fun _ => s t) y) u ∧
        EqOn (u ∘ F t) (b t) C := by
    have hR' := (hεJ ht).2
    have hgΩ : SmoothMetric Ω g :=
      ⟨fun i j => (hg.1 i j).mono (subset_univ _),fun z _ => hg.2 z (mem_univ _)⟩
    exact exists_harmonicOnBall_of_normalBallChartMap hgΩ hE hN hy he hR'.1 hR'.2
      ⟨univ,isOpen_univ,subset_univ _,(hb t).contDiffOn⟩ ((hBs t (hεJ ht).1).2)
  choose v hv hvEq using hExist
  classical
  let u (t : ℝ) : (X dim) → ℝ := if ht : t ∈ Icc (0:ℝ) ε then v t ht else fun _ => 0
  have hu (t : ℝ) (ht : t ∈ Icc (0:ℝ) ε) :
      HarmonicOnBall g (closedBallImage γ E (fun _ => s t) y) (u t) :=
    by simpa only [u,dite_eq_left ht] using hv t ht
  have hValues (t : ℝ) (ht : t ∈ Icc (0:ℝ) ε) (w : ↥(standardSphere dim)) :
      u t (endpoint E r (y,frameVector e y w)) = b t ((1+t)⁻¹ • (w:(X dim))) := by
    have hs₀ : 0 < 1+t := by linarith [ht.1]
    have hW : ‖(w : (X dim))‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    have hCW : (1+t)⁻¹ • (w:(X dim)) ∈ C := by
      apply mem_closedBall_zero_iff.mpr
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs₀.le),hW,mul_one]
      exact (inv_le_one₀ hs₀).mpr (by linarith [ht.1])
    have hFE : F t ((1+t)⁻¹ • (w:(X dim))) = endpoint E r (y,frameVector e y w) := by
      unfold F normalBallChartMap endpoint
      rw [← frameVectorL_apply_frame,map_smul,smul_smul]
      have hC : s t * (1+t)⁻¹ = r y := by dsimp [s]; field_simp
      rw [hC,frameVectorL_apply_frame]
    rw [← hFE]
    simpa only [u,dite_eq_left ht,Function.comp_apply] using hvEq t ht hCW
  refine ⟨ε,hε,u,?_,?_,?_⟩
  · have hm : MapsTo (fun q : ℝ × ↥(standardSphere dim) => (q.1,(1+q.1)⁻¹ • (q.2 : (X dim))))
        (Icc (0:ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))) (V ×ˢ C) := by
      intro q hq
      have hn : 0 < 1+q.1 := by linarith [hq.1.1]
      refine ⟨(hεJ hq.1).1, mem_closedBall_zero_iff.mpr ?_⟩
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le),
        mem_sphere_zero_iff_norm.mp q.2.property,mul_one]
      exact (inv_le_one₀ hn).mpr (by linarith [hq.1.1])
    let D := Icc (0:ℝ) ε ×ˢ (univ : Set ↥(standardSphere dim))
    have hBase : ContinuousOn (fun q : ℝ × ↥(standardSphere dim) => 1+q.1) D :=
      (continuous_const.add continuous_fst).continuousOn
    have hNZ (q : ℝ × ↥(standardSphere dim)) (hq : q ∈ D) : 1+q.1 ≠ 0 :=
      ne_of_gt (show 0 < 1+q.1 by linarith [hq.1.1])
    have hCont : ContinuousOn (fun q : ℝ × ↥(standardSphere dim) => (q.1,(1+q.1)⁻¹ • (q.2 : (X dim)))) D :=
      continuous_fst.continuousOn.prodMk ((hBase.inv₀ hNZ).smul
        (continuous_subtype_val.comp continuous_snd).continuousOn)
    exact (hBC.continuousOn.comp hCont hm).congr (fun p hp => hValues p.1 hp.1 p.2)
  · intro w
    rw [hValues 0 ⟨le_rfl,hε.le⟩ w,add_zero,inv_one,one_smul]
    exact (hBs 0 h0).1 w.property
  · intro t ht
    have ht' : t ∈ Icc (0:ℝ) ε := ⟨ht.1.le,ht.2⟩
    let O := F t '' ball (0 : (X dim)) 1
    have hs' := (hεJ ht').2
    have hSub : ball (0 : (X dim)) 1 ⊆ ball (0 : (X dim)) (ρ/s t) :=
      ball_subset_ball ((le_div_iff₀ hs'.1).mpr (by simpa using hs'.2.le))
    obtain ⟨hInj,_,hDer⟩ := normalBallChartMap_on_openBall hE hN hy he hs'.1
    have hO : IsOpen O := (exists_smooth_inverse_on_image isOpen_ball
      (contDiff_normalBallChartMap hE e y (s t)).contDiffOn (hInj.mono hSub)
      (fun z hz => hDer z (hSub hz))).1
    have hOC : O ⊆ closedBallImage γ E (fun _ => s t) y := by
      rw [closedBallImage_eq_scaledFrameImage γ E e y he hs'.1]
      exact image_mono ball_subset_closedBall
    have hI : O ⊆ interior (closedBallImage γ E (fun _ => s t) y) :=
      hO.subset_interior_iff.mpr hOC
    have ho : closedBallImage γ E r y ⊆ O := by
      change closedBallImage γ E (fun _ => r y) y ⊆ O
      rw [closedBallImage_eq_scaledFrameImage γ E e y he hr]
      rintro _ ⟨z,hz,rfl⟩
      have hs₀ : 0 < 1+t := by linarith [ht.1]
      have hB : (1+t)⁻¹ • z ∈ ball (0 : (X dim)) 1 := by
        apply mem_ball_zero_iff.mpr
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hs₀.le)]
        have hI' : (1+t)⁻¹ < 1 := (inv_lt_one₀ hs₀).mpr (by linarith [ht.1])
        exact ((mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz)
          (inv_nonneg.mpr hs₀.le)).trans_eq (mul_one _)).trans_lt hI'
      refine ⟨(1+t)⁻¹ • z,hB,?_⟩
      unfold F normalBallChartMap
      rw [← frameVectorL_apply_frame,map_smul,smul_smul]
      have hC : s t * (1+t)⁻¹ = r y := by dsimp [s]; field_simp
      rw [hC,frameVectorL_apply_frame]
    obtain ⟨⟨W,_,hW,hUW⟩,hLap⟩ := hu t ht'
    exact ⟨O,hO,ho,hUW.mono (hOC.trans hW),fun z hz => hLap z (hI hz)⟩

end CalderonN

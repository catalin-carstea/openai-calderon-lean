module

public import Proof.CalderonN.TraceCoframeJetBounds
public import Proof.CalderonN.ActualFramedCenterVelocityRemainder

import Proof.CalderonN.ActualGaussOperatorExpansion
import Proof.CalderonN.UniformLogRadiusChartJets
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! The quadratic center-velocity correction has a smooth physical
representative with uniform scaled base and angular derivatives. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_actual_centerCorrection_germs
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y)) (hSub : Y ⊆ Ω)
    {m : ℕ} (N : ℕ) (hN : N ≤ 8) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i,d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ (D : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim),∀ x ∈ Y,
        ∃ (V : Set (X dim)) (p : X dim × X dim → X dim),
          IsOpen V ∧ x ∈ V ∧ V ⊆ Y ∧ ContDiff ℝ ∞ p ∧
          (∀ y ∈ V,∀ hy : y ∈ Y,∀ z ∈ standardSphere dim,p (y,z) = ((D y hy).centerCorrection i).1 z) ∧
          ∀ z ∈ closedBall (0:X dim) 1,
            let β := beta d.γ d.radius x
            LocalSmoothJetBudget (fun q : X dim × X dim => p (x+β⁻¹ • q.1,z+q.2)) 0 N C := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η₀,C₀,hη₀,hC₀,hV⟩ := uniform_actual_framedCenterVelocity_radialRemainder hY hΩ hYc N hm
    K ρ c₀ M Cj hK hρ 2 (by norm_num)
  obtain ⟨C₁,hC₁,hCof⟩ := uniform_frameCoordinatesL_jets hΩ N (by omega) K hKp M
  obtain ⟨L,hL,hLog⟩ := uniform_background_logRadius_chart_jets hY hΩ hSub N hN (by omega) K M Cj hKp
  let L₀ := max 1 L
  obtain ⟨P,hP,hComp⟩ := uniform_physicalChart_angular_jet_composition (Z:=X dim) (F:=X dim)
    hY N L₀ (le_max_left _ _)
  let E := X dim
  let Ev : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E := (ContinuousLinearMap.apply ℝ E).flip
  let V₀ := (2:ℝ)^N*‖Ev‖*((N.factorial:ℝ)*C₁)*C₀
  have hV₀ : 0 ≤ V₀ := by dsimp only [V₀]; positivity
  refine ⟨min 1 η₀,P*V₀,lt_min zero_lt_one hη₀,mul_nonneg hP hV₀,?_⟩
  intro floor hFloor ε hε hs d hd hFrame D i x hx
  let β := beta d.γ d.radius x
  let r := d.radius
  have hβ := hFloor.trans (hd.2.2.2.2.1.2 x hx).2.1
  have hp (y : E) (hy : y ∈ Y) : 0 < r y := (hd.2.2.2.2.1.2 y hy).1
  have hr₁ : r x ≤ 1 := ((le_mul_of_one_le_right (hp x hx).le (one_le_pow₀ hβ)).trans
    (hd.2.2.2.2.2 x hx).2).trans (hs.trans (min_le_left _ _))
  let U := Y ×ˢ ball (0:E) 2
  have hU : IsOpen U := hY.prod isOpen_ball
  let SC := ({x} : Set E) ×ˢ closedBall (0:E) 1
  have hSC : IsCompact SC := isCompact_singleton.prod (isCompact_closedBall _ _)
  have hSU : SC ⊆ U := fun q hq => ⟨(show q.1=x from hq.1).symm ▸ hx,
    closedBall_subset_ball (by norm_num) hq.2⟩
  have hr := hd.2.2.2.2.1.1
  let j (q : E × E) := ((q.1,r q.1),q.2)
  let Z : FramedRadialParameter dim →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E ℝ).comp (ContinuousLinearMap.fst ℝ (E × ℝ) E)
  let W (y : E) := frameCoordinatesL d.γ y (d.frame y)
  let a (q : FramedRadialParameter dim) :=
    W q.1.1 (actualFramedCenterVelocityRemainder d q (axis i))
  have hZ : ‖Z‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    rw [one_mul]
    exact (norm_fst_le q.1).trans (norm_fst_le q)
  have hData (y : E) (hy : y ∈ Y) (z : E) (hz : z ∈ closedBall (0:E) 2) :=
    hV floor hFloor ε hε (hs.trans (min_le_right _ _)) d hd hFrame
      y hy (r y) (by rw [abs_of_pos (hp y hy)]; linarith [hp y hy]) z hz
  have hA (y : E) (hy : y ∈ Y) (z : E) (hz : z ∈ closedBall (0:E) 2) :
      LocalSmoothJetBudget a ((y,r y),z) N V₀ := by
    let q : FramedRadialParameter dim := ((y,r y),z)
    have hC : LocalSmoothJetBudget W (Z q) N C₁ := hCof hd.1 hFrame y (hSub hy)
    have hC' : LocalSmoothJetBudget (W ∘ Z) q N ((N.factorial:ℝ)*C₁) := by
      simpa only [max_eq_left hZ,one_pow,mul_one] using hC.linear_precomp Z q
    let L₁ := ContinuousLinearMap.apply ℝ E (axis i)
    have hL₁ : ‖L₁‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro T
      rw [one_mul]
      exact (T.le_opNorm _).trans_eq (by rw [norm_axis,mul_one])
    have hR : LocalSmoothJetBudget (fun w => actualFramedCenterVelocityRemainder d w (axis i)) q N C₀ :=
      ((hData y hy z hz).1.linear_postcomp L₁).enlarge
        ((mul_le_mul_of_nonneg_right hL₁ hC₀).trans_eq (one_mul _))
    exact hC'.bilinear hR Ev
  have hj : ContDiffOn ℝ ∞ j U := (contDiff_fst.contDiffOn.prodMk
    (hr.comp contDiff_fst.contDiffOn (fun _ h => h.1))).prodMk contDiff_snd.contDiffOn
  have ha : ContDiffOn ℝ ∞ (a ∘ j) U := by
    intro q hq
    exact (hA q.1 hq.1 q.2 (ball_subset_closedBall hq.2)).smooth.comp_contDiffWithinAt q (hj q hq)
  obtain ⟨p,hpS,_,V,hVop,hSV,hVU,hEq⟩ := exists_contDiff_extension_near_compact hU hSC hSU ha
  obtain ⟨V₀',V₁,hV₀',_,hxV₀',hSV₁,hTube⟩ :=
    generalized_tube_lemma (isCompact_singleton (x:=x)) (isCompact_closedBall (0:E) 1) hVop hSV
  refine ⟨V₀'∩Y,p,hV₀'.inter hY,⟨hxV₀' (mem_singleton _),hx⟩,inter_subset_right,hpS,?_,?_⟩
  · intro y hy hyY z hz
    have hz₀ := sphere_subset_closedBall hz
    have hmem : (y,z) ∈ V := hTube (show (y,z) ∈ V₀' ×ˢ V₁ from ⟨hy.1,hSV₁ hz₀⟩)
    have hpEq := hEq hmem
    have hF := (hData y hyY z (closedBall_subset_closedBall (by norm_num) hz₀)).2
      (axis i) (fderiv ℝ r y (axis i))
    have hF' := ((D y hyY).velocityEq i hz).trans hF
    rw [hpEq,ActualGaussFiberData.centerCorrection]
    change a ((y,r y),z) = ((r y)^2)⁻¹ • (((D y hyY).velocity i).1 z-
      W y (axis i)-fderiv ℝ r y (axis i) • z)
    let b := fderiv ℝ r y (axis i)
    have heq : ((D y hyY).velocity i).1 z = W y (axis i)+b • z+(r y)^2 • a ((y,r y),z) := hF'
    rw [heq]
    have heq' : W y (axis i)+b • z+(r y)^2 • a ((y,r y),z)-W y (axis i)-b • z =
        (r y)^2 • a ((y,r y),z) := by abel
    change a ((y,r y),z) =
      ((r y)^2)⁻¹ • (W y (axis i)+b • z+(r y)^2 • a ((y,r y),z)-W y (axis i)-b • z)
    rw [heq',smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (hp y hyY).ne'),one_smul]
  · intro z hz
    let f (q : E × E) := (x+β⁻¹ • q.1,z+q.2)
    have hf : ContDiff ℝ ∞ f :=
      (contDiff_const.add (contDiff_fst.const_smul _)).prodMk (contDiff_const.add contDiff_snd)
    have hf₀ : f 0 = (x,z) := by simp [f]
    have hLj n (hn : n ≤ N) (hn₀ : 1 ≤ n) :
        ‖iteratedFDeriv ℝ n (fun y => Real.log (r y)) x‖ ≤ L₀*β^n :=
      (hLog d.γ d.g₁ d.g₂ d.frame hd.1 r floor c₀ hFloor hd.2.2.2.2.1 x hx n hn hn₀).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (zero_le_one.trans hβ) _))
    have hB := hComp r hr x hx hp hr₁ β hβ hLj z a V₀
      (hA x hx z (closedBall_subset_closedBall (by norm_num) hz))
    have hEV : p ∘ f =ᶠ[𝓝 0] a ∘ j ∘ f := by
      have hfv : f 0 ∈ V := by rw [hf₀]; exact hSV ⟨mem_singleton _,hz⟩
      filter_upwards [hf.continuous.continuousAt.eventually (hVop.mem_nhds hfv)] with q hq
      exact hEq hq
    exact hB.congr_germ hEV

end CalderonN

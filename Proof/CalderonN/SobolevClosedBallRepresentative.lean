module

public import Proof.CalderonN.SobolevInteriorRepresentative
public import Proof.CalderonN.InwardBallApproximation

import Proof.CalderonN.ClosedBallPointwise
import Proof.CalderonN.TaylorJetCalculus
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 1500000 in
private theorem uniformCauchy_closedBall_of_jet_L2
    {v : ℕ → (X dim) → ℝ} (hv : ∀ n, ContDiff ℝ ∞ (v n)) {f : (X dim) → ℝ}
    (hL : ∀ k : ℕ, Tendsto (fun n =>
      eLpNorm (fun z => iteratedFDeriv ℝ k (v n) z - iteratedFDeriv ℝ k f z)
        2 (volume.restrict (ball (0 : (X dim)) 1))) atTop (𝓝 0)) (k : ℕ) :
    UniformCauchySeqOn (fun n => iteratedFDeriv ℝ k (v n)) atTop (closedBall (0 : (X dim)) 1) := by
  let C := closedBall (0 : (X dim)) 1
  let B := ball (0 : (X dim)) 1
  let μ := (volume : Measure (X dim)).restrict B
  let M : ℝ := 2^(dim+1) / Real.sqrt (volume.real C)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let Nsteps : ℝ := (dim : ℝ) + 2
  let δ := ε / (2*Nsteps*M+1)
  have hNsteps : 0 ≤ Nsteps := by dsimp only [Nsteps]; positivity
  have hden : 0 < 2*Nsteps*M+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hL' (j : ℕ) : ∀ᶠ n in atTop,
      eLpNorm (fun z => iteratedFDeriv ℝ (j+k) (v n) z - iteratedFDeriv ℝ (j+k) f z)
        2 μ ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp (hL (j+k)) _ (ENNReal.ofReal_pos.mpr hδ)
  have hLarge : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (dim+2),
      eLpNorm (fun z => iteratedFDeriv ℝ (j+k) (v n) z - iteratedFDeriv ℝ (j+k) f z)
        2 μ ≤ ENNReal.ofReal δ := (eventually_all_finset (Finset.range (dim+2))).mpr fun j _ => hL' j
  obtain ⟨N,hN⟩ := eventually_atTop.mp hLarge
  refine ⟨N,fun a ha b hb x hx => ?_⟩
  let w (z : (X dim)) := v a z - v b z
  let H := iteratedFDeriv ℝ k w
  have hw : ContDiff ℝ ∞ w := (hv a).sub (hv b)
  have hH : ContDiff ℝ ∞ H := hw.iteratedFDeriv_right (by simp)
  have he (j : ℕ) (hj : j ∈ Finset.range (dim+2)) :
      Real.sqrt (∫ z in C, ‖iteratedFDeriv ℝ j H z‖^2) ≤ 2*δ := by
    let uₐ := iteratedFDeriv ℝ (j+k) (v a)
    let uᵦ := iteratedFDeriv ℝ (j+k) (v b)
    let u := iteratedFDeriv ℝ (j+k) f
    have hSub : eLpNorm (fun z => uₐ z-uᵦ z) 2 μ ≤ ENNReal.ofReal (2*δ) := by
      rw [show (fun z => uₐ z-uᵦ z) = (fun z => uₐ z-u z) - (fun z => uᵦ z-u z) from by
        funext z
        change _ = (uₐ z-u z)-(uᵦ z-u z)
        abel]
      refine (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_
      rw [show 2*δ = δ+δ by ring,ENNReal.ofReal_add hδ.le hδ.le]
      exact add_le_add (hN a ha j hj) (hN b hb j hj)
    have hEq (z : (X dim)) : ‖iteratedFDeriv ℝ j H z‖ = ‖uₐ z-uᵦ z‖ := by
      change ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ k w) z‖ = _
      rw [norm_iteratedFDeriv_iteratedFDeriv]
      congr 1
      exact iteratedFDeriv_sub_apply ((hv a).contDiffAt.of_le (by simp))
        ((hv b).contDiffAt.of_le (by simp))
    have hMeasA : AEStronglyMeasurable (iteratedFDeriv ℝ j H) μ :=
      (hH.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    have hMeasB : AEStronglyMeasurable (fun z => uₐ z-uᵦ z) μ :=
      (((hv a).continuous_iteratedFDeriv (m := j+k) (by simp)).sub
        ((hv b).continuous_iteratedFDeriv (m := j+k) (by simp))).aestronglyMeasurable
    have hLe : eLpNorm (iteratedFDeriv ℝ j H) 2 μ ≤ ENNReal.ofReal (2*δ) :=
      (eLpNorm_congr_norm_ae hMeasA hMeasB (Eventually.of_forall hEq)).trans_le hSub
    have hMem : MemLp (iteratedFDeriv ℝ j H) 2 μ := lt_of_le_of_lt hLe ENNReal.ofReal_lt_top
    change Real.sqrt (∫ z, ‖iteratedFDeriv ℝ j H z‖^2
      ∂(volume.restrict (closedBall (0 : (X dim)) 1))) ≤ _
    rw [volume_restrict_closedUnitBall_eq,sqrt_integral_norm_sq_eq_eLpNorm_toReal hMem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hLe).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hCalc : ‖H x‖ ≤ M*(2*Nsteps*δ) := by
    have hfin : ((dim+1 : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr le_top
    refine (norm_le_unitBall_L2_jets (hH.of_le hfin) hx).trans ?_
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum he).trans_eq ?_) hM
    simp [Nsteps]
    ring
  have hlt : M*(2*Nsteps*δ) < ε := by
    dsimp only [δ]
    rw [show M*(2*Nsteps*(ε/(2*Nsteps*M+1))) = (2*Nsteps*M*ε)/(2*Nsteps*M+1) by ring]
    exact (div_lt_iff₀ hden).2 (by nlinarith only [hε])
  rw [dist_eq_norm]
  have hHx : H x = iteratedFDeriv ℝ k (v a) x - iteratedFDeriv ℝ k (v b) x :=
    iteratedFDeriv_sub_apply ((hv a).contDiffAt.of_le (by simp)) ((hv b).contDiffAt.of_le (by simp))
  rw [← hHx]
  exact hCalc.trans_lt hlt

set_option maxHeartbeats 1500000 in
/-- A smooth interior function whose jets of every order are square
integrable has a single smooth representative on the closed ball.
The boundary jets are the uniform limits of its inward dilations. -/
theorem exists_contDiffOn_closedUnitBall_of_bulk_jets
    {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f (ball (0 : (X dim)) 1))
    (hMem : ∀ k : ℕ, MemLp (iteratedFDeriv ℝ k f) 2 (volume.restrict (ball (0 : (X dim)) 1))) :
    ∃ F : (X dim) → ℝ, ContDiffOn ℝ ∞ F (closedBall (0 : (X dim)) 1) ∧ EqOn F f (ball (0 : (X dim)) 1) := by
  let B := ball (0 : (X dim)) 1
  let C := closedBall (0 : (X dim)) 1
  let r (n : ℕ) := 1-(1/2:ℝ)^(n+1)
  have hr (n : ℕ) : r n ∈ Ioo (0 : ℝ) 1 := by
    have hpow := pow_lt_one₀ (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num : (1/2:ℝ)<1)
      (Nat.succ_ne_zero n)
    exact ⟨sub_pos.mpr hpow,sub_lt_self _ (by positivity)⟩
  have hR : Tendsto r atTop (𝓝 1) := by
    have hP := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ))
      (by norm_num : (1/2:ℝ)<1)).comp (tendsto_add_atTop_nat 1)
    simpa only [r,Function.comp_def,sub_zero] using tendsto_const_nhds.sub hP
  obtain ⟨v,hv,hJet⟩ := exists_smooth_inwardDilations hf r hr
  have hL (k : ℕ) : Tendsto (fun n =>
      eLpNorm (fun z => iteratedFDeriv ℝ k (v n) z - iteratedFDeriv ℝ k f z) 2
        (volume.restrict B)) atTop (𝓝 0) := by
    apply (tendsto_eLpNorm_scaledInward_sub (hMem k) hr hR k).congr
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [hJet n k z (ball_subset_closedBall hz)]
  let G (k : ℕ) (x : (X dim)) := limUnder atTop (fun n => iteratedFDeriv ℝ k (v n) x)
  have hT (k : ℕ) : TendstoUniformlyOn (fun n => iteratedFDeriv ℝ k (v n)) (G k) atTop C := by
    have hc := uniformCauchy_closedBall_of_jet_L2 hv hL k
    exact hc.tendstoUniformlyOn_of_tendsto (fun x hx => (hc.cauchySeq hx).tendsto_limUnder)
  have hG (k : ℕ) : ContinuousOn (G k) C :=
    (hT k).continuousOn (Eventually.of_forall (f := atTop)
      (fun n => ((hv n).continuous_iteratedFDeriv (m := k) (by simp)).continuousOn)).frequently
  have he (k : ℕ) : EqOn (G k) (iteratedFDeriv ℝ k f) B := by
    intro x hx
    have hxC := ball_subset_closedBall hx
    have hCont : ContinuousOn (iteratedFDeriv ℝ k f) B :=
      (contDiffOn_iteratedFDeriv_top hf isOpen_ball k).continuousOn
    have hRX : Tendsto (fun n => r n • x) atTop (𝓝 x) := by
      simpa only [one_smul] using hR.smul (tendsto_const_nhds (x := x))
    have hSeq : Tendsto (fun n => iteratedFDeriv ℝ k (v n) x) atTop (𝓝 (iteratedFDeriv ℝ k f x)) := by
      have hd := (hCont.continuousAt (isOpen_ball.mem_nhds hx)).tendsto.comp hRX
      have hP := (hR.pow k).smul hd
      simpa only [one_pow,one_smul,Function.comp_def,← hJet _ _ _ hxC] using hP
    exact tendsto_nhds_unique ((hT k).tendsto_at hxC) hSeq
  let F := fun x => (G 0 x).curry0
  let J : (X dim) → FormalMultilinearSeries ℝ (X dim) ℝ := fun x k => G k x
  have hclosure : closure B = C := closure_ball _ one_ne_zero
  have hSeries : HasFTaylorSeriesUpToOn (⊤ : ℕ∞) F J C := by
    refine ⟨fun x _ => rfl,fun k _ x hx => ?_,fun k _ => hG k⟩
    have hdiff : DifferentiableOn ℝ (G k) B :=
      ((contDiffOn_iteratedFDeriv_top hf isOpen_ball k).differentiableOn (by simp)).congr
        (he k)
    have hJ (z : (X dim)) (hz : z ∈ B) : fderiv ℝ (G k) z = (G (k+1) z).curryLeft := by
      have hg : G k =ᶠ[𝓝 z] iteratedFDeriv ℝ k f :=
        Filter.mem_of_superset (isOpen_ball.mem_nhds hz) (he k)
      rw [hg.fderiv_eq,fderiv_iteratedFDeriv,Function.comp_apply,he (k+1) hz]
      rfl
    have hCont (z : (X dim)) (hz : z ∈ closure B) : ContinuousWithinAt (G k) B z :=
      ((hG k) z (hclosure ▸ hz)).mono ball_subset_closedBall
    have hCur : ContinuousOn (fun z => (G (k+1) z).curryLeft) C :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => (X dim)) ℝ).continuous.comp_continuousOn (hG (k+1))
    have hNear := (hCur x hx).mono ball_subset_closedBall
    have hLim : Tendsto (fun z => fderiv ℝ (G k) z) (𝓝[B] x) (𝓝 ((G (k+1) x).curryLeft)) :=
      hNear.tendsto.congr' (eventually_mem_nhdsWithin.mono fun z hz => (hJ z hz).symm)
    rw [← hclosure]
    exact hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff (convex_ball _ _) isOpen_ball hCont hLim
  refine ⟨F,hSeries.contDiffOn,fun x hx => ?_⟩
  change (G 0 x).curry0 = f x
  rw [he 0 hx]
  simp [ContinuousMultilinearMap.curry0]

end CalderonN

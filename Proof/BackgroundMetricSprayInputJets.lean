import Proof.UniversalMetricSprayJets
import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

def metricSprayInput (g : MetricField) (p : X × X) : MetricSprayInput :=
  (g p.1,(fderiv ℝ g p.1,p.2))

lemma contDiffAt_metricSprayInput (g : MetricField) (p : X × X)
    (hg : ContDiffAt ℝ ∞ g p.1) : ContDiffAt ℝ ∞ (metricSprayInput g) p :=
  (hg.comp p contDiffAt_fst).prodMk
    (((hg.fderiv_right (m:=∞) (by simp)).comp p contDiffAt_fst).prodMk contDiffAt_snd)

theorem Background.metricSprayInput_jet_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (N : ℕ) (hNm : N+1 ≤ m)
    {p : X × X} (hp : p.1 ∈ Ω) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (metricSprayInput g) p‖ ≤
      ((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)^n := by
  let B := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*B+1
  let pi : (X × X) →L[ℝ] X := ContinuousLinearMap.fst ℝ X X
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hB1 : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hD1 : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*B := by positivity
    dsimp only [D]
    linarith only [hh]
  have hDpow : D ≤ D^n := le_self_pow₀ hD1 (by omega)
  have hg : ContDiffAt ℝ ∞ g p.1 :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp)))
  have hDG := hg.fderiv_right (m:=∞) (by simp)
  have hComp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : X → V) (hf : ContDiffAt ℝ ∞ f p.1)
      (hJets : ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j f p.1‖ ≤ B) :
      ‖iteratedFDeriv ℝ n (fun q : X × X => f q.1) p‖ ≤ D^n := by
    have ht := norm_iteratedFDeriv_comp_at_bound (pi : X × X → X) f p pi.contDiff.contDiffAt hf
      n B 1 hJets (fun j hj _ => by
        simpa only [one_pow] using norm_iteratedFDeriv_clm_le_one pi hpi p j hj)
    change ‖iteratedFDeriv ℝ n (fun q : X × X => f q.1) p‖ ≤ (n.factorial:ℝ)*B*1^n at ht
    simp only [one_pow,mul_one] at ht
    exact ht.trans ((mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hnN) hB0).trans
      ((by dsimp only [D];linarith : (N.factorial:ℝ)*B ≤ D).trans hDpow))
  have hA : ContDiffAt ℝ ∞ (fun q : X × X => g q.1) p := hg.comp p contDiffAt_fst
  have hDA : ContDiffAt ℝ ∞ (fun q : X × X => fderiv ℝ g q.1) p := hDG.comp p contDiffAt_fst
  have hV : ContDiffAt ℝ ∞ (fun q : X × X => q.2) p := contDiffAt_snd
  change ‖iteratedFDeriv ℝ n (fun q : X × X => (g q.1,(fderiv ℝ g q.1,q.2))) p‖ ≤ D^n
  rw [iteratedFDeriv_prodMk hA (hDA.prodMk hV) (i:=n) (by simp),
    ContinuousMultilinearMap.opNorm_prod,iteratedFDeriv_prodMk hDA hV (i:=n) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  refine max_le ?_ (max_le ?_ ?_)
  · apply hComp g hg
    intro j hj
    exact (h.reference_matrix_jet_bound hΩ ⟨j,by omega⟩ hp).trans (abs_metricJet_le_all_budget M _)
  · apply hComp (fderiv ℝ g) hDG
    intro j hj
    rw [norm_iteratedFDeriv_fderiv]
    exact (h.reference_matrix_jet_bound hΩ ⟨j+1,by omega⟩ hp).trans (abs_metricJet_le_all_budget M _)
  · have hL : ‖(ContinuousLinearMap.snd ℝ X X)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro q
      change ‖q.2‖ ≤ 1*‖q‖
      simpa only [one_mul] using norm_snd_le q
    exact (norm_iteratedFDeriv_clm_le_one (ContinuousLinearMap.snd ℝ X X) hL p n hn).trans (one_le_pow₀ hD1)

lemma Elliptic.det_lower_bound_of_density {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    ((metricDensityBudget K)⁻¹)^2 ≤ |(g x).det| := by
  have hLow := (h.density_bounds hK hx).1
  have hB : 0 < metricDensityBudget K := by unfold metricDensityBudget;positivity
  have hSq := pow_le_pow_left₀ (inv_nonneg.mpr hB.le) hLow 2
  rw [show (metricDensity g x)^2 = (g x).det from Real.sq_sqrt (h.posDef hK hx).det_pos.le] at hSq
  exact hSq.trans (le_abs_self _)

lemma Background.metricSprayInput_mem_uniform_set {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} (hK : 0 < K) {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hm : 1 ≤ m) {x v : X} (hx : x ∈ Ω) (hv : ‖v‖ ≤ K) :
    metricSprayInput g (x,v) ∈ universalMetricSpraySet K (backgroundAllMetricJetBudget M) K
      (((metricDensityBudget K)⁻¹)^2) := by
  refine ⟨?_,?_,hv,h.1.det_lower_bound_of_density hK hx⟩
  · exact (Matrix.norm_le_iff hK.le).mpr (fun i j => h.1.entry_abs_bound hK hx i j)
  · change ‖fderiv ℝ g x‖ ≤ _
    rw [← norm_iteratedFDeriv_one]
    exact (h.reference_matrix_jet_bound hΩ ⟨1,by omega⟩ hx).trans (abs_metricJet_le_all_budget M _)

end ShrinkingSpheres

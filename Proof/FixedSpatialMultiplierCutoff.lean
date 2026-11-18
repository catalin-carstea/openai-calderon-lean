import Proof.ClosedCoefficientGlobalHigherJetBounds
import Proof.GeneralLocalCommonSupportFamily
import Proof.ParameterSpatialJetBounds
import Proof.BilinearFamilyJetBounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma norm_iteratedFDeriv_spatial_pullback_le (f : X → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : P) (z : X) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q : P × X => f q.2) (p,z)‖ ≤ ‖iteratedFDeriv ℝ n f z‖ := by
  let L := ContinuousLinearMap.snd ℝ P X
  change ‖iteratedFDeriv ℝ n (f ∘ L) (p,z)‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hf (p,z) (by simp)]
  have hh := (iteratedFDeriv ℝ n f (L (p,z))).norm_compContinuousLinearMap_le (fun _ => L)
  have hProd : (∏ _ : Fin n,‖L‖) ≤ 1 := Finset.prod_le_one₀
    (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_snd_le ℝ P X)
  exact hh.trans (mul_le_of_le_one_right (norm_nonneg _) hProd)

/-- One fixed spatial cutoff gives uniform global coefficient jet budgets
    from genuine local jets on the larger ball. Any parameter cutoff used to
    obtain a smooth representative contributes only germs, never a bound. -/
theorem exists_uniform_commonSupport_closed_multiplier_family (N : ℕ) :
    ∃ C0 : ℝ,1 ≤ C0 ∧ ∀ (f : P × X → ℝ) (U : Set (P × X)) (p0 : P),
      IsOpen U → ContDiffOn ℝ ∞ f U → ({p0} ×ˢ Metric.closedBall (0:X) 4 ⊆ U) →
      ∀ B : ℝ,0 ≤ B →
      (∀ j : ℕ,j ≤ N+3 → ∀ z ∈ Metric.closedBall (0:X) 4,‖iteratedFDeriv ℝ j f (p0,z)‖ ≤ B) →
      ∃ a : P × X → ℝ,∃ ha : ContDiff ℝ ∞ a,∃ S : Set X,∃ hS : IsCompact S,
        ∃ hz : ∀ p z,z ∉ S → a (p,z) = 0,
        ∃ V : Set P,IsOpen V ∧ p0 ∈ V ∧
          (∀ p ∈ V,∀ z ∈ Metric.closedBall (0:X) 2,a =ᶠ[𝓝 (p,z)] f) ∧
          ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (commonSupportClosedCoefficientFamily 3 a ha S hS hz) p0‖ ≤ C0*B := by
  let χ : ContDiffBump (0:X) := ⟨3,4,by norm_num,by norm_num⟩
  obtain ⟨D,hD,hχJets⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff (N+3)
  let C0 : ℝ := 1+2^(N+3)*D
  have hC0 : 1 ≤ C0 := by
    have hh : 0 ≤ (2:ℝ)^(N+3)*D := by positivity
    dsimp only [C0]
    linarith only [hh]
  refine ⟨C0,hC0,?_⟩
  intro f U p0 hU hf hSub B hB hJets
  obtain ⟨A,hA,S,hS,hzA,V,hV,hpV,hSubV,hRep⟩ := exists_local_commonSupport_family_on_open
    isOpen_univ f 4 U hU hf (mem_univ p0) hSub
  let a : P × X → ℝ := fun q => χ q.2*A q
  have ha : ContDiff ℝ ∞ a := (χ.contDiff.comp contDiff_snd).mul hA
  have hz : ∀ p z,z ∉ S → a (p,z) = 0 := by intro p z hz;change χ z*A (p,z)=0;rw [hzA p z hz,mul_zero]
  have hGlobal (z : X) (j : ℕ) (hj : j ≤ N+3) : ‖iteratedFDeriv ℝ j a (p0,z)‖ ≤ (2^(N+3)*D)*B := by
    by_cases hz4 : z ∈ Metric.closedBall (0:X) 4
    · have hAJets (k : ℕ) (hk : k ≤ N+3) : ‖iteratedFDeriv ℝ k A (p0,z)‖ ≤ B := by
        rw [((hRep p0 hpV z hz4).iteratedFDeriv ℝ k).eq_of_nhds]
        exact hJets k hk z hz4
      have hχP (k : ℕ) (hk : k ≤ N+3) : ‖iteratedFDeriv ℝ k (fun q : P × X => χ q.2) (p0,z)‖ ≤ D :=
        (norm_iteratedFDeriv_spatial_pullback_le χ χ.contDiff p0 z k).trans (hχJets k hk z)
      have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ)
        (fun q : P × X => χ q.2) A (p0,z) (χ.contDiff.comp contDiff_snd).contDiffAt hA.contDiffAt
        (N+3) D B hD hB hχP hAJets j hj
      exact hh.trans (by
        calc
          _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖*((2^(N+3)*D)*B) := by ring
          _ ≤ 1*((2^(N+3)*D)*B) := mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (by positivity)
          _ = _ := one_mul _)
    · have hzSupport : z ∉ tsupport χ := by simpa only [χ.tsupport_eq] using hz4
      have hχZero : (fun q : P × X => χ q.2) =ᶠ[𝓝 (p0,z)] (fun _ => 0) :=
        (notMem_tsupport_iff_eventuallyEq.mp hzSupport).comp_tendsto continuousAt_snd.tendsto
      have hZero : a =ᶠ[𝓝 (p0,z)] (fun _ => 0) := by
        filter_upwards [hχZero] with q hq
        change χ q.2*A q=0
        rw [hq,zero_mul]
      rw [(hZero.iteratedFDeriv ℝ j).eq_of_nhds]
      simpa using (mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2:ℝ)^(N+3)) hD) hB)
  refine ⟨a,ha,S,hS,hz,V,hV,hpV,?_,?_⟩
  · intro p hp z hz2
    have hz3 : z ∈ Metric.ball (0:X) χ.rIn := by
      have hh : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz2
      change z ∈ Metric.ball (0:X) 3
      simpa only [Metric.mem_ball,dist_zero_right] using hh.trans_lt (by norm_num : (2:ℝ)<3)
    have hχOne : (fun q : P × X => χ q.2) =ᶠ[𝓝 (p,z)] (fun _ => 1) :=
      (χ.eventuallyEq_one_of_mem_ball hz3).comp_tendsto continuousAt_snd.tendsto
    filter_upwards [hRep p hp z (Metric.closedBall_subset_closedBall (by norm_num) hz2),hχOne] with q hq hχq
    change χ q.2*A q=f q
    rw [hχq,hq,one_mul]
  · intro n hn
    apply norm_iteratedFDeriv_commonSupportClosedCoefficientFamily_global_le 3 a ha S hS hz p0 n (C0*B) (by positivity)
    intro k z
    exact (norm_iteratedFDeriv_parameter_spatial_jet_le a ha p0 z n k.val).trans
      ((hGlobal z (n+k.val) (by omega)).trans
        (mul_le_mul_of_nonneg_right (by dsimp only [C0];linarith) hB))

end ShrinkingSpheres

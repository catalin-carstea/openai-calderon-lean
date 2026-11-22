module

public import Proof.CalderonPatch.GreenPoleScaledJet
public import Proof.CalderonPatch.GreenInversePairing

import Proof.CalderonPatch.ChartDensity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Manifold Topology

namespace CalderonPatch.GreenPole

open CalderonN (X chartTest contMDiff_chartTest tsupport_chartTest_subset)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m+1)) M] [IsManifold (𝓡∂ (m+1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

local notation "J" => 𝓡∂ (m+1)
local notation "R" => 𝓘(ℝ,ℝ)
local notation "Y" => X (m+1)
local notation "Source" => smoothSourceSubmodule (m := m) (M := M)

/-- Quadratic tests shrinking to the pole have value zero there,
nonzero fixed Laplacian there, and globally bounded Laplacians. -/
theorem exists_laplacianTests (D : DirichletData m M) {p : M} (hp : p ∈ (J).interior M) :
    ∃ (v : ℕ → DirichletTest D) (f : ℕ → Source) (B : ℝ), 0 ≤ B ∧
      (∀ n, v n p = 0 ∧ f n p = -(m+1 : ℝ) ∧
        (f n : M → ℝ) = -nativeLaplace D.metric (v n)) ∧
      (∀ n x, |f n x| ≤ B) ∧
      (∀ x ≠ p, ∀ᶠ n : ℕ in atTop, f n x = 0) := by
  obtain ⟨e,hep,_,heI,he,hes⟩ := exists_interiorChart p hp isOpen_univ (mem_univ p)
  let C := nativeInteriorMetricChart D.metric D.volume D.metric_volume e heI he hes
  let c := e p
  let g := C.metric
  have hc : c ∈ e.target := e.map_source hep
  have hG : CalderonN.SmoothMetric e.target g := C.smooth_metric
  obtain ⟨R₀,hR,hT⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hc)
  let ρ := min (R₀/2) 1
  have hρ : 0 < ρ := lt_min (by positivity) zero_lt_one
  have hρR : ρ < R₀ := (min_le_left _ _).trans_lt (by linarith)
  let r (n : ℕ) : ℝ := ρ * (1 / ((n : ℝ)+1))
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrρ (n : ℕ) : r n ≤ ρ := by
    have hN : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact mul_le_of_le_one_right hρ.le ((div_le_one (by positivity)).mpr hN)
  have hr1 (n : ℕ) : r n ≤ 1 := (hrρ n).trans (min_le_right _ _)
  have hrad : Tendsto r atTop (𝓝 0) := by
    simpa [r] using (tendsto_const_nhds (x := ρ)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let K₀ := closedBall c ρ
  have hK₀ : K₀ ⊆ e.target := (closedBall_subset_ball hρR).trans hT
  let K (n : ℕ) : Compacts Y := ⟨closedBall c (r n),isCompact_closedBall _ _⟩
  have hK (n : ℕ) : (K n : Set Y) ⊆ e.target :=
    (closedBall_subset_closedBall (hrρ n)).trans hK₀
  obtain ⟨φ,hφ,hφc,hφS,hφ0,hφLap⟩ := exists_compact_laplace_test (hG.2 c hc)
  obtain ⟨B,hB,hJet⟩ := scaledTest_uniform_jets hφ hφc
  obtain ⟨A,hA,hBound⟩ := exists_laplace_bound_of_uniform_jets e.open_target
    (isCompact_closedBall c ρ) hK₀ hG hB
  let w (n : ℕ) : 𝓓_{K n}(Y, ℝ) := ⟨scaledTest φ c (r n), scaledTest_contDiff hφ c (r n),
    fun x hx => image_eq_zero_of_notMem_tsupport
      (fun h => hx (scaledTest_tsupport hφS c (hr n) h))⟩
  let u (n : ℕ) : M → ℝ := chartTest e (w n)
  have hu (n : ℕ) : ContMDiff J R ∞ (u n) :=
    contMDiff_chartTest e he (w n).contDiff (w n).compact_supp ((w n).tsupport_subset.trans (hK n))
  have huI (n : ℕ) : tsupport (u n) ⊆ (J).interior M := by
    apply (tsupport_chartTest_subset e (w n).compact_supp ((w n).tsupport_subset.trans (hK n))).trans
    rintro _ ⟨x,hx,rfl⟩
    exact heI (e.map_target (hK n ((w n).tsupport_subset hx)))
  let v (n : ℕ) : DirichletTest D := DirichletTest.ofSmooth (u n) (hu n)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun hxS =>
      (show x ∈ ((J).interior M)ᶜ by rw [(J).compl_interior]; exact hx) (huI n hxS)))
  let b (n : ℕ) : 𝓓_{K n}(Y, ℝ) := compactLaplace e.open_target (hK n) hG (w n)
  have hBnative (n : ℕ) : nativeLaplace D.metric (u n) = chartTest e (b n) :=
    nativeLaplace_chartTest_laplace C (hK n) (w n)
  have hSmooth (n : ℕ) : ContMDiff J R ∞ (chartTest e (b n)) :=
    contMDiff_chartTest e he (b n).contDiff (b n).compact_supp ((b n).tsupport_subset.trans (hK n))
  let f (n : ℕ) : Source := ⟨-chartTest e (b n),(hSmooth n).neg⟩
  refine ⟨v,f,A,hA,?_,?_,?_⟩
  · intro n
    have hvp : v n p = 0 := by
      change chartTest e (w n) p = 0
      rw [chartTest,indicator_of_mem hep]
      change scaledTest φ c (r n) c = 0
      simp [scaledTest,hφ0]
    have hfp : f n p = -(m+1 : ℝ) := by
      change -chartTest e (b n) p = _
      rw [chartTest,indicator_of_mem hep]
      change -(CalderonN.laplace g (scaledTest φ c (r n)) c) = _
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg Neg.neg (hφLap (r n) (hr n))
    exact ⟨hvp,hfp,congrArg Neg.neg (hBnative n).symm⟩
  · intro n x
    change |-(chartTest e (b n) x)| ≤ A
    rw [abs_neg]
    by_cases hx : x ∈ e.source ∧ e x ∈ (K n : Set Y)
    · rw [chartTest,indicator_of_mem hx.1]
      exact hBound _ (w n).contDiff (hJet c (r n) (hr n) (hr1 n)) _ (closedBall_subset_closedBall (hrρ n) hx.2)
    · by_cases hxS : x ∈ e.source
      · rw [chartTest,indicator_of_mem hxS]
        have hz := image_eq_zero_of_notMem_tsupport (fun hz : e x ∈ tsupport (b n : Y → ℝ) =>
          hx ⟨hxS,(b n).tsupport_subset hz⟩)
        simpa only [Function.comp_apply,hz,abs_zero] using hA
      · rw [chartTest,indicator_of_notMem hxS,abs_zero]
        exact hA
  · intro x hx
    by_cases hxS : x ∈ e.source
    · have hX : e x ≠ c := fun hee => hx (e.injOn hxS hep hee)
      filter_upwards [hrad.eventually (eventually_lt_nhds (dist_pos.mpr hX))] with n hn
      change -chartTest e (b n) x = 0
      rw [chartTest,indicator_of_mem hxS,Function.comp_apply]
      exact neg_eq_zero.mpr (image_eq_zero_of_notMem_tsupport (fun hz =>
        hn.not_ge (mem_closedBall.mp ((b n).tsupport_subset hz))))
    · exact Eventually.of_forall fun n => by
        change -chartTest e (b n) x = 0
        rw [chartTest,indicator_of_notMem hxS,neg_zero]

end CalderonPatch.GreenPole

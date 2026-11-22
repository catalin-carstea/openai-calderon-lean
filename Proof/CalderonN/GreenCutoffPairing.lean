module

public import Proof.CalderonN.GreenCross
public import Proof.CalderonN.FixedKernelIntegral
public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.GreenWeak
import Proof.CalderonN.WeakHarmonicSpace
import Proof.CalderonN.HarmonicL2Space
import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.DilationHarmonic
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def greenCutoffSource (g : (MetricField dim)) (φ : (X dim) → ℝ) (x : (X dim)) : ℝ :=
  -(chartVolume g x * laplace g φ x)

/-- Pair a fixed cutoff source in the first variable with the mixed Green
kernel. In the known region the Green identity identifies this value
with evaluation of the test function at the pole. -/
@[expose] def greenCutoffPairing (g : (MetricField dim)) (F : (X dim) × (X dim) → ℝ) (φ : (X dim) → ℝ) (y : (X dim)) : ℝ :=
  ∫ x, F (x,y) * greenCutoffSource g φ x

theorem tsupport_greenCutoffSource_subset (g : (MetricField dim)) (φ : (X dim) → ℝ) :
    tsupport (greenCutoffSource g φ) ⊆ tsupport φ := by
  have hs : Function.support (greenCutoffSource g φ) ⊆ Function.support (laplace g φ) := by
    intro x hx h
    exact hx (by simp [greenCutoffSource,show laplace g φ x = 0 from h])
  exact (closure_mono hs).trans (tsupport_laplace_subset g φ)

theorem contDiff_greenCutoffSource {g : (MetricField dim)} (hg : SmoothMetric univ g)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (greenCutoffSource g φ) := by
  obtain ⟨h,_,_⟩ := density_times_laplace_of_compact_test isOpen_univ hg hφ hφc (subset_univ _)
  exact h.neg

theorem greenCutoffPairing_eq_value_of_greenGerm
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : (MetricField dim)} {G F : (X dim) × (X dim) → ℝ}
    (hG : GreenGerm Ω g G) {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) {y : (X dim)} (hy : y ∈ Ω)
    (hEq : EqOn (fun x => F (x,y)) (fun x => G (x,y)) (tsupport (greenCutoffSource g φ))) :
    greenCutoffPairing g F φ y = φ y := by
  have hFzero (x : (X dim)) (hx : x ∉ Ω) : F (x,y) * greenCutoffSource g φ x = 0 :=
    mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport fun h =>
      hx (hφΩ (tsupport_greenCutoffSource_subset g φ h)))
  unfold greenCutoffPairing
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hFzero]
  refine (setIntegral_congr_fun hΩ.measurableSet (fun x _ => ?_)).trans ((hG.2.2 y hy).2 φ hφ hφc hφΩ)
  by_cases hx : x ∈ tsupport (greenCutoffSource g φ)
  · rw [show F (x,y) = G (x,y) from hEq hx]
    unfold greenCutoffSource chartVolume
    ring
  · have hn := image_eq_zero_of_notMem_tsupport hx
    calc
      _ = (G (x,y)) * greenCutoffSource g φ x := by rw [hn,mul_zero,mul_zero]
      _ = _ := by unfold greenCutoffSource chartVolume; ring

theorem greenCutoffPairing_harmonic_of_compact_source
    {g₁ g₂ : (MetricField dim)} (hg₁ : SmoothMetric univ g₁)
    {U V K : Set (X dim)} (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKU : K ⊆ U)
    {F : (X dim) × (X dim) → ℝ} (hF : ProductSolutionOn g₁ g₂ (U ×ˢ V) F)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hsource : tsupport (greenCutoffSource g₁ φ) ⊆ K) :
    Harmonic V g₂ (greenCutoffPairing g₁ F φ) := by
  let H (x y : (X dim)) := F (x,y) * greenCutoffSource g₁ φ x
  let μ := (volume : Measure (X dim)).restrict K
  haveI : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    simpa only [μ,Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)
  have hμ : μ Kᶜ = 0 := by simp [μ,Measure.restrict_apply hK.isClosed.measurableSet.compl]
  have hS := contDiff_greenCutoffSource hg₁ hφ hφc
  have hH : ContDiffOn ℝ ∞ (Function.uncurry H) (U ×ˢ V) :=
    hF.1.mul (hS.comp contDiff_fst).contDiffOn
  have hHlaw (x : (X dim)) (hx : x ∈ K) (y : (X dim)) (hy : y ∈ V) : laplace g₂ (H x) y = 0 := by
    have hf := hF.harmonic_right (hKU hx)
    have he : H x = fun w => greenCutoffSource g₁ φ x * F (x,w) := by
      funext w
      simp only [H,mul_comm]
    rw [he,laplace_const_mul hV hf.1 hy,hf.2 y hy,mul_zero]
  have hJ := harmonic_integral_on_compact hK hKU hU hV hμ hH hHlaw
  have he : (fun y => ∫ x, H x y ∂μ) = greenCutoffPairing g₁ F φ := by
    funext y
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun h => hx (hsource h))))
  exact he ▸ hJ

/-- Two cutoff tests give the same value if their difference is carried
by a region where the first-variable kernel is harmonic. -/
theorem greenCutoffPairing_eq_of_harmonic_difference
    {g : (MetricField dim)} {U : Set (X dim)} (hU : IsOpen U) (hg : SmoothMetric U g)
    {F : (X dim) × (X dim) → ℝ} {y : (X dim)} (hF : Harmonic U g (fun x => F (x,y)))
    {φ₁ φ₂ : (X dim) → ℝ} (hφ₁ : ContDiff ℝ ∞ φ₁) (hφ₂ : ContDiff ℝ ∞ φ₂)
    (hc₁ : HasCompactSupport φ₁) (hc₂ : HasCompactSupport φ₂)
    (hI₁ : Integrable (fun x => F (x,y) * greenCutoffSource g φ₁ x))
    (hI₂ : Integrable (fun x => F (x,y) * greenCutoffSource g φ₂ x))
    (hSub : tsupport (φ₁-φ₂) ⊆ U) :
    greenCutoffPairing g F φ₁ y = greenCutoffPairing g F φ₂ y := by
  let diff : ChartTest U := ⟨φ₁-φ₂,hφ₁.sub hφ₂,hc₁.sub hc₂,hSub⟩
  have hTest := integral_harmonic_test_eq_zero hU hg hF diff
  have hLocal : greenCutoffPairing g F diff.toFun y = 0 := by
    have hz (x : (X dim)) (hx : x ∉ U) : F (x,y) * greenCutoffSource g diff.toFun x = 0 :=
      mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun h =>
        hx (hSub (tsupport_greenCutoffSource_subset g diff.toFun h))))
    unfold greenCutoffPairing
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    have hneg := congrArg Neg.neg hTest
    rw [← integral_neg] at hneg
    refine (integral_congr_ae ?_).trans (show _ = 0 from by simpa only [neg_zero] using hneg)
    filter_upwards with x
    simp only [greenCutoffSource]
    ring
  have hSource (x : (X dim)) :
      greenCutoffSource g diff.toFun x = greenCutoffSource g φ₁ x-greenCutoffSource g φ₂ x := by
    change -(chartVolume g x * laplace g (fun z => φ₁ z-φ₂ z) x) = _
    rw [laplace_sub isOpen_univ g hφ₁.contDiffOn hφ₂.contDiffOn (mem_univ x)]
    unfold greenCutoffSource
    ring
  apply sub_eq_zero.mp
  unfold greenCutoffPairing
  rw [← integral_sub hI₁ hI₂]
  refine (integral_congr_ae ?_).trans hLocal
  filter_upwards with x
  rw [hSource,mul_sub]

/-- The scalar Green pairing is integrable when its fixed source is
supported on a compact set where the kernel slice is continuous. -/
theorem integrable_greenCutoffPairing_of_compact_source
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {K : Set (X dim)} (hK : IsCompact K)
    {F : (X dim) × (X dim) → ℝ} {y : (X dim)} (hF : ContinuousOn (fun x => F (x,y)) K)
    {φ : (X dim) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hsource : tsupport (greenCutoffSource g φ) ⊆ K) :
    Integrable (fun x => F (x,y) * greenCutoffSource g φ x) := by
  have h := (hF.mul (contDiff_greenCutoffSource hg hφ hφc).continuous.continuousOn).integrableOn_compact (μ := volume) hK
  have hzero (x : (X dim)) (hx : x ∉ K) : F (x,y) * greenCutoffSource g φ x = 0 :=
    mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (fun ht => hx (hsource ht)))
  have he : K.indicator (fun x => F (x,y) * greenCutoffSource g φ x) =
      fun x => F (x,y) * greenCutoffSource g φ x := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hzero x hx]
  rw [← he]
  exact h.integrable_indicator hK.isClosed.measurableSet

end CalderonN

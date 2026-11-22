module

public import Proof.CalderonPatch.GreenOffPole
public import Proof.CalderonN.FixedKernelIntegral

import Proof.CalderonPatch.HomogeneousTests
import Proof.CalderonN.ChartSchwarzWords
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic.Ring

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis coordDeriv laplace chartVolume Harmonic parameterSecondOrder)

variable {n : ℕ} [NeZero n]

theorem parameterSecondOrder_const_mul (a : I n → I n → ℝ) (b : I n → ℝ) (c d : ℝ)
    {f : X n → ℝ} {V : Set (X n)} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {x : X n} (hx : x ∈ V) :
    parameterSecondOrder a b c (fun z => d * f z) x = d * parameterSecondOrder a b c f x := by
  have h₁ (j : I n) :
      (fun z => fderiv ℝ (fun w => d * f w) z (axis j)) =ᶠ[𝓝 x]
        fun z => d * fderiv ℝ f z (axis j) := by
    filter_upwards [hV.mem_nhds hx] with z hz
    have h := (((hf.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.const_mul d).fderiv
    exact DFunLike.congr_fun h (axis j)
  have h₂ (i j : I n) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => d * f w) z (axis j)) x (axis i) =
      d * fderiv ℝ (fun z => fderiv ℝ f z (axis j)) x (axis i) := by
    have hd := (hf.fderiv_of_isOpen hV (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := axis j))
    have h := (((hd.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.const_mul d).fderiv
    rw [(h₁ j).fderiv_eq]
    exact DFunLike.congr_fun h (axis i)
  simp only [parameterSecondOrder,h₂, (h₁ _).eq_of_nhds, Finset.mul_sum, mul_add]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    · exact Finset.sum_congr rfl fun _ _ => by ring
  · ring

private theorem parameterSecondOrder_eq_zero_of_zero_germ
    (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ)
    {f : X n → ℝ} {z : X n} (h : f =ᶠ[𝓝 z] 0) :
    parameterSecondOrder a b c f z = 0 := by
  have h₁ (i : I n) : fderiv ℝ f z (axis i) = 0 := by
    rw [h.fderiv_eq]
    simp [Pi.zero_def]
  have h₂ (i j : I n) : fderiv ℝ (fun y => fderiv ℝ f y (axis j)) z (axis i) = 0 := by
    have he := (chartDerivativeWord_congr_germ [i,j] h).eq_of_nhds
    simp only [CalderonN.chartDerivativeWord,List.foldr_cons,List.foldr_nil,coordDeriv] at he
    change fderiv ℝ (coordDeriv j f) z (axis i) = 0
    rw [he]
    have hZ : coordDeriv j (0 : X n → ℝ) = 0 := by
      funext y
      simp [coordDeriv, Pi.zero_def]
    rw [hZ]
    simp [Pi.zero_def]
  simp only [parameterSecondOrder,h₁,h₂,h.eq_of_nhds,Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero]

/-- A smooth parameter derivative of a jointly smooth family of
harmonic functions is harmonic. Testing against the metric density
allows the proof to use compact domination in the other variable. -/
theorem harmonic_parameterSecondOrder {U V : Set (X n)} (hU : IsOpen U) (hV : IsOpen V)
    {g : MetricField n} (hg : CalderonN.SmoothMetric U g)
    {G : X n → X n → ℝ} (hG : ContDiffOn ℝ ∞ (Function.uncurry G) (U ×ˢ V))
    (hH : ∀ z ∈ V, Harmonic U g (fun x => G x z)) {z : X n} (hz : z ∈ V)
    (a : I n → I n → ℝ) (b : I n → ℝ) (c : ℝ) :
    Harmonic U g (fun y => parameterSecondOrder a b c (G y) z) := by
  let w : X n → ℝ := fun y => parameterSecondOrder a b c (G y) z
  have hP i : ContDiffOn ℝ ∞ (Function.uncurry (fun y s => fderiv ℝ (G y) s (axis i))) (U ×ˢ V) :=
    (CalderonN.contDiffOn_partial hG (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞) hU hV).clm_apply contDiffOn_const
  have hPP j : ContDiffOn ℝ ∞ (Function.uncurry
      (fun y s => fderiv ℝ (fun q => fderiv ℝ (G y) q (axis j)) s)) (U ×ˢ V) :=
    CalderonN.contDiffOn_partial (hP j) (by simp) hU hV
  have hMap : MapsTo (fun y : X n => (y,z)) U (U ×ˢ V) := fun _ hy => ⟨hy,hz⟩
  have hC : ContDiffOn ℝ ∞ (fun y : X n => (y,z)) U := contDiffOn_id.prodMk contDiffOn_const
  have hw : ContDiffOn ℝ ∞ w U := by
    unfold w parameterSecondOrder
    apply ContDiffOn.add
    · apply ContDiffOn.add
      · exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
          contDiffOn_const.mul ((hPP j).comp hC hMap |>.clm_apply contDiffOn_const)
      · exact ContDiffOn.sum fun i _ => contDiffOn_const.mul ((hP i).comp hC hMap)
    · exact contDiffOn_const.mul (hG.comp hC hMap)
  apply harmonic_of_zero_laplace_tests hU hg hw
  intro φ hφ hc hs
  let L : X n → ℝ := fun y => chartVolume g y * laplace g φ y
  let T := tsupport φ
  let μ := (volume : Measure (X n)).restrict T
  have : IsFiniteMeasure μ := ⟨by simpa only [μ,Measure.restrict_apply_univ] using hc.measure_lt_top⟩
  have hm : MeasurableSet Tᶜ := (isClosed_tsupport φ : IsClosed T).measurableSet.compl
  have hT : μ Tᶜ = 0 := by simp [μ,Measure.restrict_apply hm, Set.compl_inter_self]
  have hL := CalderonN.density_times_laplace_of_compact_test hU hg hφ hc hs
  have hLzero (y : X n) (hy : y ∉ T) : L y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hL.2.2 h))
  let F (y s : X n) := L y * G y s
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (U ×ˢ V) :=
    ((hL.1.comp contDiff_fst).contDiffOn).mul hG
  have hZero : (fun s => ∫ y, F y s ∂μ) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hV.mem_nhds hz] with s hs'
    change (∫ y in T, F y s) = 0
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => mul_eq_zero_of_left (hLzero y hy) _)]
    have hHarm := hH s hs'
    have hComp := CalderonN.integral_laplace_symmetric_of_compact_test hU hg hHarm.1 hφ hc hs
    have hzero : (fun y => φ y * (chartVolume g y * laplace g (fun q => G q s) y)) = 0 := by
      funext y
      by_cases hy : y ∈ U
      · rw [hHarm.2 y hy, mul_zero, mul_zero,Pi.zero_apply]
      · rw [image_eq_zero_of_notMem_tsupport (fun ht => hy (hs ht)), zero_mul,Pi.zero_apply]
    rw [hzero] at hComp
    change (∫ y, G y s * laplace g φ y * chartVolume g y) = (∫ _ : X n, (0 : ℝ)) at hComp
    rw [integral_zero] at hComp
    refine Eq.trans ?_ hComp
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by change L y * G y s = _; unfold L; ring
  have hJet := CalderonN.integral_parameterSecondOrder hc hs hU hV hT
    (hF.of_le (by simp : (2 : WithTop ℕ∞) ≤ ∞)) a b c hz
  rw [parameterSecondOrder_eq_zero_of_zero_germ a b c hZero] at hJet
  have hW : (∫ y, L y * w y ∂μ) = 0 := by
    apply Eq.trans _ hJet.symm
    apply integral_congr_ae
    filter_upwards [CalderonN.ae_mem_of_measure_compl hT] with y hy
    have hS : ContDiffOn ℝ ∞ (G y) V :=
      hG.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => ⟨hs hy,hz⟩)
    exact (parameterSecondOrder_const_mul a b c (L y) hV hS hz).symm
  change (∫ y in T, L y * w y) = 0 at hW
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => mul_eq_zero_of_left (hLzero y hy) _)] at hW
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    have hz : laplace g φ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hh => hy (hs (CalderonN.tsupport_laplace_subset g φ hh)))
    simp [hz])]
  have hEq : (fun y => w y * (-laplace g φ y) * chartVolume g y) = fun y => -(L y * w y) := by
    funext y
    unfold L
    ring
  rw [hEq,integral_neg,hW,neg_zero]

end CalderonPatch

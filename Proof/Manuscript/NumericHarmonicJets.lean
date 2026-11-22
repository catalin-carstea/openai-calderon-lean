module

public import Proof.Manuscript.NumericInteriorEnergy
public import Proof.CalderonN.MetricDivergence

import all Proof.CalderonN.ClassicalInteriorJets
import Proof.CalderonN.ProductDerivativeWords
import Proof.CalderonN.CrossTensor
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {d : ℕ} [NeZero d]

open Elliptic
open LocalMetricExtension (integral_sq_eq_norm_sq)

/-- Only finitely many derivatives of the divergence coefficient are needed
for a uniform harmonic jet estimate. The local cutoff and coordinate-word
conversion follow the release's `exists_uniform_harmonic_interior_jet_bound`. -/
theorem exists_numeric_harmonic_interior_jet_bound
    {U : Set (X d)} (hU : IsOpen U)
    {K : Set (X d)} (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ)
    {lam Ma : ℝ} (hlam : 0 < lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField d), SmoothMetric U g →
      HasEllipticityFloor (fun i j x => divergenceCoeff g x i j) U lam →
      HasWordBudget (fun i j x => divergenceCoeff g x i j) U Ma ((fullCoordinateWord d).length + k) →
      ∀ (u : Lp ℝ 2 ((volume : Measure (X d)).restrict U)) (f : X d → ℝ), Harmonic U g f →
        (u : X d → ℝ) =ᵐ[(volume : Measure (X d)).restrict U] f →
        ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖u‖ := by
  obtain ⟨V,hV,hKV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨ζ,hζ,_,hζU,hζV⟩ := exists_plateau_cutoff hU hVc hVU
  have hLen (q : Fin k → I d) : (fullCoordinateWord d ++ List.ofFn q).length ≤
      (fullCoordinateWord d).length + k := by
    simp
  choose A hAc hbound using (fun q : Fin k → I d =>
    exists_interior_word_point_bound_numeric hV hK hKV (Ma := Ma) hlam (List.ofFn q))
  refine ⟨∑ q, A q,Finset.sum_nonneg fun q _ => hAc q,fun g hg hFloor hBudget u f hf hrep x hx => ?_⟩
  let b (i j : I d) (y : X d) := divergenceCoeff g y i j
  let a (i j : I d) (y : X d) := ζ y * b i j y
  have hb (i j : I d) : ContDiffOn ℝ ∞ (b i j) U := by
    exact contDiffOn_divergenceCoeff hg i j
  have ha (i j : I d) : ContDiff ℝ ∞ (a i j) :=
    contDiff_mul_of_tsupport_subset hU hζ hζU (hb i j)
  have hζOne (y : X d) (hy : y ∈ V) : ζ =ᶠ[𝓝 y] fun _ => 1 := hζV y (subset_closure hy)
  let F (y : (X d)) := ζ y*f y
  have hF : ContDiff ℝ ∞ F := contDiff_mul_of_tsupport_subset hU hζ hζU hf.1
  have hFeq (y : (X d)) (hy : y ∈ V) : F =ᶠ[𝓝 y] f :=
    (hζOne y hy).mono fun z hz => by simp [F,hz]
  have hAeq (y : (X d)) (hy : y ∈ V) (i j : (I d)) : a i j =ᶠ[𝓝 y] b i j :=
    (hζOne y hy).mono fun z hz => by simp [a,hz]
  have hEll : HasEllipticityFloor a V lam := by
    intro y hy p
    have he (i j : I d) := (hAeq y hy i j).eq_of_nhds
    simp only [he]
    exact hFloor y (hVU (subset_closure hy)) p
  have hWord (q : Fin k → I d) :
      HasWordBudget a V Ma (fullCoordinateWord d ++ List.ofFn q).length := by
    intro y hy i j w hw
    rw [(wordDeriv_congr_germ w (hAeq y hy i j)).eq_of_nhds]
    exact hBudget y (hVU (subset_closure hy)) i j w (hw.trans (hLen q))
  have hPDE (y : (X d)) (hy : y ∈ V) : Lop (a) F y = 0 := by
    have hyU := hVU (subset_closure hy)
    have hCoeff := lop_coeff_congr_germ (hAeq y hy) F
    rw [hCoeff]
    have hD (j : I d) : coordDeriv j F =ᶠ[𝓝 y] coordDeriv j f := by
      filter_upwards [(hFeq y hy).fderiv (𝕜 := ℝ)] with z hz
      exact congrFun (congrArg DFunLike.coe hz) (axis j)
    have hLop : Lop (b) F y = Lop (b) f y := by
      unfold Lop
      refine Finset.sum_congr rfl fun i _ => pd_congr_of_eventuallyEq ?_ i
      filter_upwards [Filter.eventually_all.mpr hD] with z hz
      simp only [Elliptic.pd, coordDeriv] at hz ⊢
      simp only [hz]
    rw [hLop]
    change (∑ i, coordDeriv i (fun z => divergenceFlux g f z i) y) = 0
    rw [← chartVolume_mul_laplace_eq_divergence hU hg hf.1 hyU, hf.2 y hyU, mul_zero]
  have hIntU : IntegrableOn (fun y => f y^2) U :=
    (Lp.memLp u).integrable_sq.congr (hrep.mono fun _ hy => congrArg (fun a : ℝ => a^2) hy)
  have hIntV : IntegrableOn (fun y => F y^2) V :=
    (hIntU.mono_set (subset_closure.trans hVU)).congr_fun
      (fun y hy => by rw [(hFeq y hy).eq_of_nhds]) hV.measurableSet
  have hInt : (∫ y in V, F y^2) ≤ ‖u‖^2 := by
    calc
      _ = ∫ y in V, f y^2 := setIntegral_congr_fun hV.measurableSet (fun y hy => by rw [(hFeq y hy).eq_of_nhds])
      _ ≤ ∫ y in U, f y^2 := setIntegral_mono_set hIntU (ae_of_all _ fun _ => sq_nonneg _)
        (subset_closure.trans hVU).eventuallyLE
      _ = ∫ y in U, (u y)^2 := integral_congr_ae (hrep.symm.mono fun _ hy => congrArg (fun a : ℝ => a^2) hy)
      _ = ‖u‖^2 := integral_sq_eq_norm_sq u
  have hFjet := (hFeq x (hKV hx)).iteratedFDeriv (𝕜 := ℝ) k
  rw [← hFjet.eq_of_nhds, Finset.sum_mul]
  apply norm_multilinear_le_sum_coordinate _ (fun q => A q * ‖u‖) (fun q => mul_nonneg (hAc q) (norm_nonneg _))
  intro q
  rw [← directionalWord_ofFn_eq_iteratedFDeriv hF]
  change |directionalWord (List.ofFn (axis ∘ q)) F x| ≤ _
  rw [← List.map_ofFn, directionalWord_map_axis]
  have he := Real.sqrt_le_sqrt hInt
  rw [Real.sqrt_sq (norm_nonneg _)] at he
  exact (hbound q a ha hEll (hWord q) F hF hPDE hIntV x hx).trans (mul_le_mul_of_nonneg_left he (hAc q))

end CalderonN

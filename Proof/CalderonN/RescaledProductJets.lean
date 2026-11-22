module

public import Proof.CalderonN.ProductAffineChart
public import Proof.CalderonN.UniformProductInteriorJets

import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

public section

set_option maxHeartbeats 1800000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {d : ℕ} [NeZero d]

/-- The constants for small translated product rectangles can be chosen
on a compact set that includes zero scales. Only the kernels on the
positive-scale rectangles enter the derivative estimate. -/
theorem exists_uniform_rescaled_product_jets
    {g₁ g₂ : (MetricField d)} (hg₁ : SmoothMetric univ g₁) (hg₂ : SmoothMetric univ g₂)
    (B S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ lam ∈ Icc (-1 : ℝ) 1, ∀ x₀ ∈ closedBall (0 : (X d)) B,
      ∀ y₀ ∈ closedBall (0 : (X d)) B, ∀ s ∈ Icc 0 S,
      ∀ a : ℝ, ∀ {O : Set ((X d) × (X d))}, IsOpen O →
      MapsTo (separateAffineChart x₀ y₀ s) (ball (0 : (X d)) 2 ×ˢ ball (0 : (X d)) 2) O →
      ∀ {F : (X d) × (X d) → ℝ}, ProductSolutionOn (dilatedMetric g₁ lam) (dilatedMetric g₂ lam) O F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ q ∈ ball (0 : (X d)) 2 ×ˢ ball (0 : (X d)) 2, |a * F (separateAffineChart x₀ y₀ s q)| ≤ M) →
      ∃ H : (X d) × (X d) → ℝ, ContDiff ℝ ∞ H ∧
        H =ᶠ[𝓝 0] (fun q => a * F (separateAffineChart x₀ y₀ s q)) ∧
        ∀ k ≤ n, ‖iteratedFDeriv ℝ k H 0‖ ≤ C*M := by
  let P := ℝ × ((X d) × ((X d) × ℝ))
  let J : Set P := Icc (-1 : ℝ) 1 ×ˢ
    (closedBall (0 : (X d)) B ×ˢ (closedBall (0 : (X d)) B ×ˢ Icc 0 S))
  have hJ : IsCompact J := isCompact_Icc.prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod isCompact_Icc))
  let U := ball (0 : (X d)) 1
  let V := ball (0 : (X d)) 2
  let K : Set (X d) := {0}
  have hU : IsOpen U := isOpen_ball
  have hV : IsOpen V := isOpen_ball
  have hUc : IsCompact (closure U) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hKU : K ⊆ U := singleton_subset_iff.mpr (mem_ball_self zero_lt_one)
  have hUV : closedBall (0 : (X d)) 1 ⊆ V := closedBall_subset_ball (by norm_num)
  let gA (p : P) := affineChartMetric (dilatedMetric g₁ p.1) (p.2.1,p.2.2.2)
  let gB (p : P) := affineChartMetric (dilatedMetric g₂ p.1) (p.2.2.1,p.2.2.2)
  have hdilated (g : MetricField d) (hg : SmoothMetric univ g) (lam : ℝ) :
      SmoothMetric univ (dilatedMetric g lam) := by
    simpa only [mem_univ, Set.ofPred_true] using smoothMetric_dilated hg lam
  have hSmooth (g : (MetricField d)) (hg : SmoothMetric univ g) (p : P) (c : (X d)) :
      SmoothMetric U (affineChartMetric (dilatedMetric g p.1) (c,p.2.2.2)) :=
    let h := smoothMetric_affineChartMetric (hdilated g hg p.1) (c,p.2.2.2)
    ⟨fun i j => (h.1 i j).mono (subset_univ _), fun x _ => h.2 x (mem_univ _)⟩
  have hMap (c : P → (X d)) (hc : ContDiff ℝ ∞ c) :
      ContDiff ℝ ∞ (fun q : P × (X d) => ((q.1.1 • c q.1,q.1.1*q.1.2.2.2),q.2)) :=
    ((contDiff_fst.fst.smul (hc.comp contDiff_fst)).prodMk
      (contDiff_fst.fst.mul contDiff_fst.snd.snd.snd)).prodMk contDiff_snd
  have hA (i j : (I d)) : ContDiffOn ℝ ∞
      (fun q : P × (X d) => divergenceCoeff (gA q.1) q.2 i j) (univ ×ˢ U) := by
    simp only [gA,affineChartMetric_dilatedMetric]
    exact ((contDiff_affineChartMetric_divergenceCoeff hg₁ i j).comp (hMap _ contDiff_snd.fst)).contDiffOn
  have hB (i j : (I d)) : ContDiffOn ℝ ∞
      (fun q : P × (X d) => divergenceCoeff (gB q.1) q.2 i j) (univ ×ˢ U) := by
    simp only [gB,affineChartMetric_dilatedMetric]
    exact ((contDiff_affineChartMetric_divergenceCoeff hg₂ i j).comp (hMap _ contDiff_snd.snd.fst)).contDiffOn
  obtain ⟨C,hC,hJet⟩ := exists_uniform_product_interior_jet_bound_of_sup hJ hU hU hUc hUc
    isCompact_singleton isCompact_singleton hKU hKU (fun p _ => hSmooth g₁ hg₁ p p.2.1)
    (fun p _ => hSmooth g₂ hg₂ p p.2.2.1) hA hB n
  refine ⟨C,hC,?_⟩
  intro lam hl x₀ hx y₀ hy s hs a O hO hMap F hF M hM hBound
  let p : P := (lam,(x₀,(y₀,s)))
  let f (q : (X d) × (X d)) := a * F (separateAffineChart x₀ y₀ s q)
  have hf : ProductSolutionOn (gA p) (gB p) (V ×ˢ V) f :=
    ((hF.separateAffineChart_pullback hO (hdilated g₁ hg₁ lam)
      (hdilated g₂ hg₂ lam) x₀ y₀ s).mono hMap).const_mul (hV.prod hV) a
  obtain ⟨H,hH,_,W,hW,hCW,_,he⟩ := exists_contDiff_extension_near_compact
    (hV.prod hV) ((isCompact_closedBall (0 : (X d)) 1).prod (isCompact_closedBall (0 : (X d)) 1))
    (Set.prod_mono hUV hUV) hf.1
  have hUW : U ×ˢ U ⊆ W := (Set.prod_mono ball_subset_closedBall ball_subset_closedBall).trans hCW
  have hUV' : U ×ˢ U ⊆ V ×ˢ V :=
    Set.prod_mono (ball_subset_closedBall.trans hUV) (ball_subset_closedBall.trans hUV)
  have hHF := (hf.mono hUV').congr (hU.prod hU) (he.mono hUW)
  have h₀ : (0 : (X d) × (X d)) ∈ K ×ˢ K := ⟨mem_singleton _,mem_singleton _⟩
  refine ⟨H,hH,?_ ,fun k hk => hJet p ⟨hl,hx,hy,hs⟩ H hH hHF M hM ?_ k hk 0 h₀⟩
  · filter_upwards [hW.mem_nhds (hUW (Set.prod_mono hKU hKU h₀))] with q hq
    exact he hq
  · intro q hq
    rw [he (hUW hq)]
    exact hBound q (hUV' hq)

end CalderonN

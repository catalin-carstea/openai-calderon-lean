module

public import Proof.CalderonN.SphereFrame
public import Proof.CalderonN.Chart

import Proof.CalderonN.ParallelTransportODE
import Proof.CalderonN.ParallelFrameCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! Adapted from `HorizontalBundleDerivative` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A horizontal direction is realized by a locally defined curve in
the actual metric sphere bundle, using parallel transport. -/
theorem exists_horizontal_curve
    {Y : Set (X dim)} (hY : IsOpen Y) {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ Y)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    (w : ↥(standardSphere dim)) (a : (X dim)) :
    ∃ c : ℝ → (X dim) × (X dim), c 0 = (y,frameVector e y w) ∧
      HasDerivAt c (a,-connection γ y a (frameVector e y w)) 0 ∧
      ∀ᶠ t in 𝓝 (0:ℝ), c t ∈ bundle Y γ := by
  let q (t : ℝ) := y+t • a
  have hq : ContDiff ℝ ∞ q := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hq₀ : q 0 = y := by simp [q]
  have hdq : HasDerivAt q a 0 := by
    simpa only [q,id_eq,ContinuousLinearMap.toSpanSingleton_apply,one_smul] using
      ((((hasDerivAt_id (0:ℝ)).smul_const a).hasFDerivAt.const_add y : HasFDerivAt _ _ (0:ℝ)).hasDerivAt)
  obtain ⟨F,_,hF₀,hPar⟩ := exists_parallelFrame hγ hq (e y)
  -- The vector uses the transported frame at time t and unchanged angular coordinates.
  let W (t : ℝ) := ∑ i, (w : (X dim)) i • F t i
  let c (t : ℝ) := (q t,W t)
  have hW₀ : W 0 = frameVector e y w := by simp [W,frameVector,hF₀]
  have hP := hPar 0 (left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hW : HasDerivAt W (-connection γ y a (frameVector e y w)) 0 := by
    have hF' i : HasDerivAt (fun s => F s i) (-connection γ y a (F 0 i)) 0 := by
      simpa only [hq₀,hdq.deriv] using hP.self_of_nhds.1 i
    have h := hasDerivAt_parallelFrame_sum γ y a F (fun _ => (w:(X dim)))
      (hasDerivAt_const (0 : ℝ) (w:(X dim))) hF'
    simpa only [W,hW₀,PiLp.zero_apply,zero_smul,Finset.sum_const_zero,zero_sub] using h
  refine ⟨c,Prod.ext hq₀ hW₀,?_,?_⟩
  · convert (hdq.hasFDerivAt.prodMk hW.hasFDerivAt).hasDerivAt using 1
    simp
  have hYq : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ Y :=
    hq.continuous.continuousAt.preimage_mem_nhds (by simpa only [hq₀] using hY.mem_nhds hy)
  filter_upwards [hP,hYq] with t ht hty
  have hor (i j : (I dim)) : metricPair γ (q t) (F t i) (F t j) = if i=j then 1 else 0 :=
    (ht.2 i j).trans (by rw [hq₀,he])
  let e' : (Frame dim) := fun _ => F t
  exact ⟨hty,frameVector_mem_sphere γ e' (q t) hor w⟩

/-- Equality on the sphere bundle determines every horizontal derivative
of smooth ambient representatives along that bundle. -/
theorem horizontal_eq_of_eqOn_bundle
    {V : Set (X dim)} (hV : IsOpen V) {γ : (MetricField dim)} (hγ : SmoothMetric univ γ)
    {e : (Frame dim)} {y : (X dim)} (hy : y ∈ V)
    (he : ∀ i j, metricPair γ y (e y i) (e y j) = if i=j then 1 else 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : (X dim) × (X dim) → F} (h : EqOn u v (bundle V γ)) (w : ↥(standardSphere dim))
    (hu : DifferentiableAt ℝ u (y,frameVector e y w))
    (hv : DifferentiableAt ℝ v (y,frameVector e y w)) (a : (X dim)) :
    horizontal γ u y (frameVector e y w) a = horizontal γ v y (frameVector e y w) a := by
  obtain ⟨c,hc,hc',hcB⟩ := exists_horizontal_curve hV hγ hy he w a
  have hu' : DifferentiableAt ℝ u (c 0) := hc.symm ▸ hu
  have hv' : DifferentiableAt ℝ v (c 0) := hc.symm ▸ hv
  have heq : (u ∘ c) =ᶠ[𝓝 (0:ℝ)] (v ∘ c) := hcB.mono (fun _ ht => h ht)
  have hdu := hu'.hasFDerivAt.comp_hasDerivAt 0 hc'
  have hdv := hv'.hasFDerivAt.comp_hasDerivAt 0 hc'
  have h := (hdu.congr_of_eventuallyEq heq.symm).unique hdv
  simpa only [horizontal,hc] using h

end CalderonN

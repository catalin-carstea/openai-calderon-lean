/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

 


















public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

 


theorem ContDiffOn.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hfs : ContDiffOn ℝ n f s) (hs : s ∈ nhds x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs
  let b : ContDiffBump x :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let g : E → F := fun y ↦ b y • f y
  have hball : ContDiffOn ℝ n f (Metric.ball x ε) :=
    hfs.mono hεs
  have hg : ContDiff ℝ n g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport b
    · have hyClosed : y ∈ Metric.closedBall x (ε / 2) := by
        simpa only [b, ContDiffBump.tsupport_eq] using hy
      have hyBall : y ∈ Metric.ball x ε := by
        rw [Metric.mem_ball]
        exact hyClosed.trans_lt (by linarith)
      exact b.contDiffAt.smul
        ((hball y hyBall).contDiffAt (Metric.isOpen_ball.mem_nhds hyBall))
    · have hbzero : (b : E → ℝ) =ᶠ[nhds y] fun _ ↦ 0 :=
        notMem_tsupport_iff_eventuallyEq.mp hy
      have hgeq : g =ᶠ[nhds y] fun _ ↦ (0 : F) := by
        filter_upwards [hbzero] with z hz
        simp only [g, hz, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq hgeq
  refine ⟨g, hg, b.hasCompactSupport.smul_right, ?_⟩
  filter_upwards [b.eventuallyEq_one] with y hy
  have hone : (fun _ : E ↦ (1 : ℝ)) y = 1 := by
    rfl
  have hy' : b y = 1 := hy.trans hone
  simp only [g, hy', one_smul]

 

theorem ContDiffAt.exists_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] (n : ℕ) {f : E → F} {x : E}
    (hf : ContDiffAt ℝ n f x) :
    ∃ g : E → F, ContDiff ℝ n g ∧ HasCompactSupport g ∧ g =ᶠ[nhds x] f :=
  let ⟨s, hs, hfs⟩ := hf.contDiffOn le_rfl (by simp)
  hfs.exists_contDiff_eventuallyEq_of_finiteDimensional hs

 



theorem ContDiffOn.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional
    [FiniteDimensional ℝ E] {n : ℕ∞} {f : E → F} {x : E} {s : Set E}
    (hf : ContDiffOn ℝ (n + 1) f s) (hs : s ∈ nhds x) :
    ∃ (g : E → F) (K : NNReal), ContDiff ℝ (n + 1) g ∧ LipschitzWith K g ∧ g =ᶠ[nhds x] f := by
  obtain ⟨g, hg, hgsupp, hgf⟩ := hf.exists_contDiff_eventuallyEq_of_finiteDimensional hs
  obtain ⟨C, hC⟩ := hg.lipschitzWith_of_hasCompactSupport hgsupp (by simp)
  exact ⟨g, C, hg, hC, hgf⟩

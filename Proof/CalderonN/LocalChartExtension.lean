module

public import Proof.CalderonN.Chart

import Proof.CalderonN.EllipticCalculus
import Proof.CalderonN.GreenWeak
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ}

/-- Extend a smooth chart metric to a globally smooth positive metric
while retaining it near a prescribed compact subset. -/
theorem exists_global_chart_metric
    {U K : Set (X dim)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) :
    ∃ G : (MetricField dim), SmoothMetric univ G ∧ ∀ x ∈ K, G =ᶠ[𝓝 x] g := by
  obtain ⟨f,hf,_,hfU,hfK⟩ := Elliptic.exists_plateau_cutoff hU hK hKU
  let χ (x : (X dim)) := Real.smoothTransition (f x)
  let G (x : (X dim)) : (Mat dim) := χ x • g x + (1-χ x) • (1 : (Mat dim))
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf
  have hz (x : (X dim)) (hx : x ∉ U) : χ =ᶠ[𝓝 x] fun _ => 0 := by
    have h : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hfU h))
    exact h.mono (fun y hy => by
      change f y = 0 at hy
      change χ y = 0
      exact Real.smoothTransition.zero_of_nonpos hy.le)
  have hGone (x : (X dim)) (hx : x ∉ U) : G =ᶠ[𝓝 x] fun _ => (1 : (Mat dim)) := by
    filter_upwards [hz x hx] with y hy
    change χ y = 0 at hy
    simp [G,hy]
  refine ⟨G,⟨fun i j => contDiffOn_univ.mpr ?_,fun x _ => ?_⟩,?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · have h := (hχ.contDiffAt.mul ((hg.1 i j).contDiffAt (hU.mem_nhds hx))).add
        (((contDiffAt_const (c := (1 : ℝ))).sub hχ.contDiffAt).mul (contDiffAt_const (c := (1 : (Mat dim)) i j)))
      simpa only [G,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] using h
    · apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hGone x hx] with y hy
      exact congrArg (fun M : (Mat dim) => M i j) hy
  · by_cases hx : x ∈ U
    · have hχ0 : 0 ≤ χ x := Real.smoothTransition.nonneg _
      have hχ1 : χ x ≤ 1 := Real.smoothTransition.le_one _
      rcases eq_or_lt_of_le hχ0 with he | he
      · simpa only [G,← he,zero_smul,sub_zero,one_smul,zero_add] using
          (Matrix.PosDef.one : Matrix.PosDef (1 : (Mat dim)))
      rcases eq_or_lt_of_le hχ1 with h₁ | h₁
      · simpa only [G,h₁,one_smul,sub_self,zero_smul,add_zero] using hg.2 x hx
      exact ((hg.2 x hx).smul he).add (Matrix.PosDef.one.smul (sub_pos.mpr h₁))
    · rw [(hGone x hx).eq_of_nhds]
      exact Matrix.PosDef.one
  · intro x hx
    filter_upwards [hfK x hx] with y hy
    change f y = 1 at hy
    have h : χ y = 1 := Real.smoothTransition.one_of_one_le (by rw [hy])
    simp [G,h]

/-- Restrict the exact chart Green identities to an open subchart and
change the metric by an equality on that subchart. -/
theorem GreenGerm.restrict_congr_metric
    {U V : Set (X dim)} (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    {g G : (MetricField dim)} (hg : SmoothMetric U g) (hEq : EqOn g G V)
    {K : (X dim) × (X dim) → ℝ} (hK : GreenGerm U g K) : GreenGerm V G K := by
  have hOff : OffDiagonal V ⊆ OffDiagonal U :=
    fun _ hp => ⟨hVU hp.1,hVU hp.2.1,hp.2.2⟩
  refine ⟨hK.1.mono hOff,fun p hp => hK.2.1 p (hOff hp),fun y hy => ?_⟩
  obtain ⟨hLoc,hDist⟩ := hK.2.2 y (hVU hy)
  refine ⟨hLoc.mono_set hVU,fun φ hφ hφc hφV => ?_⟩
  let F (x : (X dim)) := K (x,y) * (-laplace g φ x) * Real.sqrt (g x).det
  have hF (x : (X dim)) (hx : x ∉ V) : F x = 0 := by
    have hs := (density_times_laplace_of_compact_test hU hg hφ hφc (hφV.trans hVU)).2.2
    have hzero : chartVolume g x * laplace g φ x = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun z => chartVolume g z * laplace g φ z) (fun hs' => hx (hφV (hs hs')) :
        x ∉ tsupport (fun z => chartVolume g z * laplace g φ z))
    have hF' : F x = -(K (x,y) * (chartVolume g x * laplace g φ x)) := by
      simp only [F,chartVolume]
      ring
    rw [hF',hzero,mul_zero,neg_zero]
  calc
    _ = ∫ x in V, F x := by
      apply setIntegral_congr_fun hV.measurableSet
      intro x hx
      have hl := laplace_congrOn hV hEq (fun _ _ => rfl) hx (f := φ)
      simp only [F,hEq hx,hl]
    _ = ∫ x, F x := setIntegral_eq_integral_of_forall_compl_eq_zero hF
    _ = ∫ x in U, F x := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hF x (fun hxV => hx (hVU hxV)))).symm
    _ = φ y := hDist φ hφ hφc (hφV.trans hVU)

end CalderonN

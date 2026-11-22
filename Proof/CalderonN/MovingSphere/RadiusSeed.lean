module

public import Proof.CalderonN.FixedTube.GreenInitialization

import Proof.CalderonN.ProductGluing
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN.MovingSphere

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {normal : I dim}

open FixedTube

@[expose] def lowerNormalSeed (normal : I dim) (N : Set ((X dim) × (X dim))) : Set ((X dim) × (X dim)) :=
  N ∩ {q | q.2 normal < -(1/4 : ℝ)} ∩ {q | q.1 ≠ q.2}

@[expose] def separatedNormalSeed (N : Set ((X dim) × (X dim))) (γ : (MetricField dim)) (V : (X dim) × (X dim) → (X dim))
    (r₀ : ℝ) : Set ((X dim) × (X dim)) :=
  N ∩ {q | r₀^2 < metricPair γ q.2 (V q) (V q)}

theorem isOpen_lowerNormalSeed {N : Set ((X dim) × (X dim))} (hN : IsOpen N) :
    IsOpen (lowerNormalSeed normal N) :=
  (hN.inter (isOpen_lt ((EuclideanSpace.proj (𝕜 := ℝ) normal).continuous.comp continuous_snd)
    continuous_const)).inter (isOpen_ne_fun continuous_fst continuous_snd)

theorem isOpen_separatedNormalSeed {N : Set ((X dim) × (X dim))} (hN : IsOpen N)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N)
    (r₀ : ℝ) : IsOpen (separatedNormalSeed N γ V r₀) := by
  have h (i j : (I dim)) : ContinuousOn (fun q : (X dim) × (X dim) => γ q.2 i j) N :=
    ((contDiffOn_univ.mp (hγ.1 i j)).continuous.comp continuous_snd).continuousOn
  have hv (i : (I dim)) : ContinuousOn (fun q : (X dim) × (X dim) => V q i) N :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hV
  have hc : ContinuousOn (fun q : (X dim) × (X dim) => metricPair γ q.2 (V q) (V q)) N := by
    unfold metricPair
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact ((h i j).mul (hv i)).mul (hv j)
  exact hc.isOpen_inter_preimage hN isOpen_Ioi

set_option maxHeartbeats 500000 in
/-- The open seed is the union of a fixed positive normal separation
and the lower punctured tube. Its germs are the initialized Green
continuation and the actual lower-cross values, respectively. -/
theorem exists_normalRadius_seed
    {N : Set ((X dim) × (X dim))} (hN : IsOpen N) {B d r₀ : ℝ}
    (hNB : N ⊆ ball (0 : (X dim)) B ×ˢ ball (0 : (X dim)) B)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {V : (X dim) × (X dim) → (X dim)} (hV : ContinuousOn V N)
    (hSep : ∀ q ∈ N, r₀^2 ≤ metricPair γ q.2 (V q) (V q) → d ≤ ‖q.1-q.2‖)
    {g₁ g₂ : (MetricField dim)} {O : Set ((X dim) × (X dim))} (hO : fixedSeparationSet B d ⊆ O)
    {F G : (X dim) × (X dim) → ℝ} (hG : ProductSolutionOn g₁ g₂ O G)
    (hF : ProductSolutionOn g₁ g₂ (lowerCross normal B (1/4)) F)
    (hGF : EqOn G F (fixedSeparationSet B d ∩ lowerSidePairs normal (1/4))) :
    ∃ H, ProductSolutionOn g₁ g₂
      (separatedNormalSeed N γ V r₀ ∪ lowerNormalSeed normal N) H ∧
      EqOn H G (separatedNormalSeed N γ V r₀) ∧ EqOn H F (lowerNormalSeed normal N) := by
  let S := separatedNormalSeed N γ V r₀
  let T := lowerNormalSeed normal N
  have hS : IsOpen S := isOpen_separatedNormalSeed hN hγ hV _
  have hT : IsOpen T := isOpen_lowerNormalSeed hN
  have hSfixed : S ⊆ fixedSeparationSet B d := fun q hq =>
    ⟨(mem_ball_zero_iff.mp (hNB hq.1).1).le,(mem_ball_zero_iff.mp (hNB hq.1).2).le,
      hSep q hq.1 (show r₀^2 < metricPair γ q.2 (V q) (V q) from hq.2).le⟩
  have hTlow (q : (X dim) × (X dim)) (hq : q ∈ T) : q ∈ lowerSidePairs normal (1/4) :=
    show min (q.1 normal) (q.2 normal) < -(1/4 : ℝ) from min_lt_iff.mpr (Or.inr hq.1.2)
  have hTcross : T ⊆ lowerCross normal B (1/4) := fun q hq => lowerCross_mem_of_norm
    (mem_ball_zero_iff.mp (hNB hq.1.1).1) (mem_ball_zero_iff.mp (hNB hq.1.1).2) hq.2 (hTlow q hq)
  let U (b : Bool) := if b then T else S
  let K (b : Bool) := if b then F else G
  have hU (b : Bool) : IsOpen (U b) := by
    cases b
    · exact hS
    · exact hT
  have hK (b : Bool) : ProductSolutionOn g₁ g₂ (U b) (K b) := by
    cases b
    · exact hG.mono (hSfixed.trans hO)
    · exact hF.mono hTcross
  have hEq (a b : Bool) : EqOn (K a) (K b) (U a ∩ U b) := by
    cases a <;> cases b
    · exact fun _ _ => rfl
    · exact fun q hq => hGF ⟨hSfixed hq.1,hTlow q hq.2⟩
    · exact fun q hq => (hGF ⟨hSfixed hq.2,hTlow q hq.1⟩).symm
    · exact fun _ _ => rfl
  obtain ⟨H,hH,hAgree⟩ := exists_productSolution_iUnion U hU K hK hEq
  have hST : S ∪ T ⊆ ⋃ b, U b := fun q hq => hq.elim
    (fun h => mem_iUnion.mpr ⟨false,h⟩) (fun h => mem_iUnion.mpr ⟨true,h⟩)
  exact ⟨H,hH.mono hST,hAgree false,hAgree true⟩

end CalderonN.MovingSphere

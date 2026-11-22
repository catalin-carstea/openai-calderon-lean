module

public import Proof.Manuscript.RadiusTaylorJets

import Proof.CalderonN.LocalFlowVariation
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open CalderonN Filter MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The radius derivative of a smooth ambient function is the derivative of
its actual fixed-parameter radius slice. -/
theorem hasDerivAt_radialFirstDerivative {a : P × ℝ → V} {q : P × ℝ}
    (ha : ContDiffAt ℝ ∞ a q) :
    HasDerivAt (fun s => a (q.1,s)) (radialFirstDerivative a q) q.2 :=
  hasDerivAt_time_slice a q.1 q.2 (ha.differentiableAt (by simp))

variable {ι : Type}

@[expose] def radiusSubsum (S : Finset ι) (c : ℝ) (d : ι → ℝ)
    (a : P × ℝ → V) (b : ι → P × ℝ → V) (q : P × ℝ) : V :=
  c • a q - ∑ k ∈ S, d k • b k q

theorem contDiffOn_radiusSubsum {O : Set (P × ℝ)} {a : P × ℝ → V}
    {b : ι → P × ℝ → V} {S : Finset ι}
    (ha : ContDiffOn ℝ ∞ a O) (hb : ∀ k ∈ S, ContDiffOn ℝ ∞ (b k) O)
    (c : ℝ) (d : ι → ℝ) : ContDiffOn ℝ ∞ (radiusSubsum S c d a b) O :=
  (ha.const_smul c).sub (ContDiffOn.sum fun k hk => (hb k hk).const_smul (d k))

theorem radialFirstDerivative_radiusSubsum {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} {b : ι → P × ℝ → V} {S : Finset ι}
    (ha : ContDiffOn ℝ ∞ a O) (hb : ∀ k ∈ S, ContDiffOn ℝ ∞ (b k) O)
    (c : ℝ) (d : ι → ℝ) :
    EqOn (radialFirstDerivative (radiusSubsum S c d a b))
      (radiusSubsum S c d (radialFirstDerivative a) (fun k => radialFirstDerivative (b k))) O := by
  intro q hq
  have hn := hO.mem_nhds hq
  have hA := HasDerivAt.const_smul c (hasDerivAt_radialFirstDerivative (ha.contDiffAt hn))
  have hB := HasDerivAt.sum (u := S)
    (fun k hk => HasDerivAt.const_smul (d k) (hasDerivAt_radialFirstDerivative ((hb k hk).contDiffAt hn)))
  have hF := hasDerivAt_radialFirstDerivative ((contDiffOn_radiusSubsum ha hb c d).contDiffAt hn)
  apply hF.unique
  convert hA.sub hB using 1
  · funext s
    simp only [radiusSubsum,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply]
  · rfl

theorem radiusSecondDerivative_radiusSubsum {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} {b : ι → P × ℝ → V} {S : Finset ι}
    (ha : ContDiffOn ℝ ∞ a O) (hb : ∀ k ∈ S, ContDiffOn ℝ ∞ (b k) O)
    (c : ℝ) (d : ι → ℝ) :
    EqOn (radiusSecondDerivative (radiusSubsum S c d a b))
      (radiusSubsum S c d (radiusSecondDerivative a) (fun k => radiusSecondDerivative (b k))) O := by
  intro q hq
  have hf : radialFirstDerivative (radiusSubsum S c d a b) =ᶠ[𝓝 q]
      radiusSubsum S c d (radialFirstDerivative a) (fun k => radialFirstDerivative (b k)) :=
    Filter.mem_of_superset (hO.mem_nhds hq) (radialFirstDerivative_radiusSubsum hO ha hb c d)
  have hC : radialFirstDerivative (radialFirstDerivative (radiusSubsum S c d a b)) q =
      radialFirstDerivative
        (radiusSubsum S c d (radialFirstDerivative a) (fun k => radialFirstDerivative (b k))) q :=
    congrArg (fun L : (P × ℝ) →L[ℝ] V => L (0,1)) hf.fderiv_eq
  exact hC.trans (radialFirstDerivative_radiusSubsum hO (contDiffOn_radialFirstDerivative hO ha)
    (fun k hk => contDiffOn_radialFirstDerivative hO (hb k hk)) c d hq)

/-- The literal Taylor tail respects the finite combination in each
normalized symbol truncation, including at zero radius. -/
theorem radiusTaylorRemainder_radiusSubsum [CompleteSpace V] {O : Set (P × ℝ)} (hO : IsOpen O)
    {a : P × ℝ → V} {b : ι → P × ℝ → V} {S : Finset ι}
    (ha : ContDiffOn ℝ ∞ a O) (hb : ∀ k ∈ S, ContDiffOn ℝ ∞ (b k) O)
    (c : ℝ) (d : ι → ℝ) :
    EqOn (radiusTaylorRemainder (radiusSubsum S c d a b))
      (radiusSubsum S c d (radiusTaylorRemainder a) (fun k => radiusTaylorRemainder (b k)))
      (radiusSegment O) := by
  intro q hq
  let g (f : P × ℝ → V) (t : ℝ) :=
    (1-t) • radiusSecondDerivative f (q.1,t*q.2)
  have hg (f : P × ℝ → V) (hf : ContDiffOn ℝ ∞ f O) :
      IntervalIntegrable (g f) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    have hmap : Continuous (fun t : ℝ => (q.1,t*q.2)) :=
      continuous_const.prodMk (continuous_id.mul continuous_const)
    exact (continuous_const.sub continuous_id).continuousOn.smul
      ((contDiffOn_radiusSecondDerivative hO hf).continuousOn.comp hmap.continuousOn hq)
  have heq : EqOn (g (radiusSubsum S c d a b))
      (fun t => c • g a t - ∑ k ∈ S, d k • g (b k) t) (uIcc (0:ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    change (1-t) • radiusSecondDerivative (radiusSubsum S c d a b) (q.1,t*q.2) = _
    rw [radiusSecondDerivative_radiusSubsum hO ha hb c d (hq t ht)]
    simp only [radiusSubsum,g,smul_sub,Finset.smul_sum,smul_smul]
    simp only [mul_comm c, mul_comm (d _)]
  change (∫ t in (0:ℝ)..1, g (radiusSubsum S c d a b) t) =
    c • (∫ t in (0:ℝ)..1, g a t) - ∑ k ∈ S, d k • (∫ t in (0:ℝ)..1, g (b k) t)
  rw [intervalIntegral.integral_congr heq]
  have hInt := intervalIntegral.integral_sub ((hg a ha).smul c)
    (IntervalIntegrable.sum S fun k hk => (hg (b k) (hb k hk)).smul (d k))
  simp only [Finset.sum_apply,Pi.smul_apply] at hInt
  rw [intervalIntegral.integral_finsetSum (f := fun k t => d k • g (b k) t)
    (fun k hk => (hg (b k) (hb k hk)).smul (d k))] at hInt
  simpa only [intervalIntegral.integral_smul] using hInt

end CalderonPaper

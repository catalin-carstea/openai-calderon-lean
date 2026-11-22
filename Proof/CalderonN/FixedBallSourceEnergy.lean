module

public import Proof.CalderonN.SourceSobolev
public import Proof.ReleasedAnalysis.TauCeti.Analysis.PDE.DirichletProblem
public import Proof.PriorAnalysis.TauCeti.Analysis.Sobolev.Embedding
public import Mathlib.Analysis.Matrix.Normed

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

public section

/- Zero-boundary source energy from FixedBallSourceEnergy in the 3D Theorem
   3.1 release, using the released generic TauCeti variational definitions. -/
noncomputable section
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Matrix.Norms.Elementwise

namespace CalderonN

variable {n : ℕ}

@[expose] def fixedBallOpens (n : ℕ) : Opens (X n) := ⟨ball 0 1, isOpen_ball⟩

abbrev FixedBallH1 (n : ℕ) := TauCeti.W1p (volume : Measure (X n)) (fixedBallOpens n) 2

abbrev FixedBallH1Zero (n : ℕ) := TauCeti.W1p0 (volume : Measure (X n)) (fixedBallOpens n) 2

local instance : TopologicalSpace.PseudoMetrizableSpace (Mat n) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (I n → I n → ℝ))

set_option maxHeartbeats 1800000 in
theorem fixedBall_zeroTrace_critical_bound (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : FixedBallH1Zero n,
      MemLp (TauCeti.W1p.value (u : FixedBallH1 n) : X n → ℝ) (criticalSobolevExponent n)
        ((volume : Measure (X n)).restrict (fixedBallOpens n)) ∧
      (eLpNorm (TauCeti.W1p.value (u : FixedBallH1 n) : X n → ℝ) (criticalSobolevExponent n)
        ((volume : Measure (X n)).restrict (fixedBallOpens n))).toReal ≤
          C * ‖TauCeti.W1p.gradient (u : FixedBallH1 n)‖ := by
  let q := criticalSobolevExponent n
  let μ := (volume : Measure (X n)).restrict (fixedBallOpens n)
  let C := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (X n)) ((2 : ℝ≥0∞).toReal)
  have hq : q ≠ ⊤ := criticalSobolevExponent_ne_top
  have hnq : q⁻¹ + (Module.finrank ℝ (X n) : ℝ≥0∞)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
    simpa only [X, I, finrank_euclideanSpace, Fintype.card_fin] using criticalSobolevExponent_inv_add hn
  let : Fact (1 ≤ q) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_criticalSobolevExponent hn)⟩
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun u => ?_⟩
  let U : Lp ℝ q μ := TauCeti.W1p0.sobolevEmbeddingL hq hnq u
  have hU : (U : X n → ℝ) =ᵐ[μ] TauCeti.W1p.value (u : FixedBallH1 n) :=
    TauCeti.W1p0.coeFn_sobolevEmbeddingL hq hnq u
  refine ⟨(Lp.memLp U).ae_eq hU, ?_⟩
  rw [← eLpNorm_congr_ae hU, ← Lp.norm_def]
  exact (TauCeti.W1p0.norm_sobolevEmbeddingL_le hq hnq u).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (norm_nonneg _))

private theorem integral_mul_le_twoNorms {f g : (X n) → ℝ} {μ : Measure (X n)}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hp : ENNReal.ofReal (2:ℝ) = 2 := by norm_num
  have hf' : MemLp f (ENNReal.ofReal (2:ℝ)) μ := by simpa only [hp] using hf
  have hg' : MemLp g (ENNReal.ofReal (2:ℝ)) μ := by simpa only [hp] using hg
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' hg' 
  have hBound : (∫ x, ‖f x‖ * ‖g x‖ ∂μ) ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow,sqrt_integral_norm_sq_eq_eLpNorm_toReal hf,
      sqrt_integral_norm_sq_eq_eLpNorm_toReal hg] using h
  refine (integral_mono (hf.integrable_mul hg) (hf.norm.integrable_mul hg.norm) fun x => ?_).trans hBound
  change f x * g x ≤ ‖f x‖ * ‖g x‖
  rw [← norm_mul,Real.norm_eq_abs]
  exact le_abs_self _

set_option maxHeartbeats 1600000 in
/-- A source supported on a small set controls the first-order energy by
the 1/n power of that set's volume. Neither the location nor the
shape of the small set enters the constant. -/
theorem exists_fixedBall_source_gradient_bound
    (hn : 3 ≤ n) {a : (X n) → (Mat n)} (ha : Continuous a) {lo hi : ℝ}
    (hEll : TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens n) : Set (X n)) a lo hi) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Lp ℝ 2 ((volume : Measure (X n)).restrict (fixedBallOpens n)))
        (u : FixedBallH1Zero n) (h : TauCeti.PDE.IsWeakSolutionDirichlet a 0 0 F u)
        (A : Set (X n)) (hA : MeasurableSet A),
        (∀ᵐ x ∂((volume : Measure (X n)).restrict (fixedBallOpens n)), x ∉ A → F x = 0) →
        ‖TauCeti.W1p.gradient (u : (FixedBallH1 n))‖ ≤
          C * (((volume : Measure (X n)).restrict (fixedBallOpens n)).real A)^(1 / (n : ℝ)) * ‖F‖ := by
  let μ := (volume : Measure (X n)).restrict (fixedBallOpens n)
  have hμ : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using
      ((measure_mono (show ((fixedBallOpens n) : Set (X n)) ⊆ closedBall (0 : (X n)) 1 from ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : (X n)) 1).measure_lt_top)⟩
  obtain ⟨S,hS,hQ⟩ := fixedBall_zeroTrace_critical_bound hn
  have hlo : 0 < lo := hEll.1
  refine ⟨S/lo,div_pos hS hlo,fun F u h A hA hSupp => ?_⟩
  let U := TauCeti.W1p.value (u : (FixedBallH1 n))
  let G := ‖TauCeti.W1p.gradient (u : (FixedBallH1 n))‖
  let ν := μ.restrict A
  have hν : IsFiniteMeasure ν := by dsimp only [ν]; infer_instance
  have hνμ : ν ≤ μ := Measure.restrict_le_self
  have hF : MemLp (F : (X n) → ℝ) 2 μ := Lp.memLp F
  have hU : MemLp (U : (X n) → ℝ) 2 μ := Lp.memLp U
  have hDom₁ : (eLpNorm (F : (X n) → ℝ) 2 ν).toReal ≤ ‖F‖ := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_mono hF.ne (eLpNorm_mono_measure _ hνμ)
  have hDom₂ : (eLpNorm (U : (X n) → ℝ) 2 ν).toReal ≤ (μ.real A)^(1 / (n : ℝ))*(S*G) := by
    have he : ν.real univ = μ.real A := by simp [ν,measureReal_def]
    refine (eLpNorm_two_toReal_le_volume_one_div_eLpNorm_critical hn hνμ (hQ u).1).trans ?_
    rw [he]
    exact mul_le_mul_of_nonneg_left (hQ u).2 (Real.rpow_nonneg (by positivity) _)
  have hR : (∫ x, F x * U x ∂μ) = ∫ x, F x * U x ∂ν := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [hSupp] with x hx
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA]
    · rw [indicator_of_notMem hxA,hx hxA,zero_mul]
  have hE := hEll.mul_norm_gradient_sq_le_energyFormH1_self_of_zero_drift
    (b := (0 : (X n) → (X n))) (c := (0 : (X n) → ℝ)) (gamma := 0)
    ha.aestronglyMeasurable aestronglyMeasurable_const (by simp) (by simp) (by simp) (u : (FixedBallH1 n))
  have hEq := (TauCeti.PDE.isWeakSolutionDirichlet_iff F u).mp h u
  change _ = ∫ x, F x * U x ∂μ at hEq
  rw [hEq,hR] at hE
  have hEB : lo * G^2 ≤ (‖F‖ * (μ.real A)^(1 / (n : ℝ)) * S) * G := by
    refine hE.trans ((integral_mul_le_twoNorms (hF.mono_measure hνμ) (hU.mono_measure hνμ)).trans ?_)
    calc
      _ ≤ ‖F‖ * ((μ.real A)^(1 / (n : ℝ))*(S*G)) :=
        mul_le_mul hDom₁ hDom₂ ENNReal.toReal_nonneg (norm_nonneg _)
      _ = _ := by ring
  change G ≤ _
  by_cases hG : G = 0
  · rw [hG]
    positivity
  · have hG' : 0 < G := (norm_nonneg _).lt_of_ne' hG
    have hC : lo*G ≤ ‖F‖ * (μ.real A)^(1 / (n : ℝ)) * S := by
      by_contra! hgt
      have hLt := mul_lt_mul_of_pos_right hgt hG'
      nlinarith only [hLt,hEB]
    calc
      G ≤ (‖F‖*(μ.real A)^(1 / (n : ℝ))*S)/lo :=
        (le_div_iff₀ hlo).mpr (by simpa only [mul_comm G lo] using hC)
      _ = _ := by ring

end CalderonN

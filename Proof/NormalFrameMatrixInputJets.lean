import Proof.FiniteJetCompositionBound
import Proof.MatrixFieldHigherJetNorms
import Proof.UniversalMatrixFrameNormalizer
import Proof.FourthBilinearVelocityBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres

lemma norm_iteratedFDeriv_clm_le_one {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] (L : P →L[ℝ] Q) (hL : ‖L‖ ≤ 1)
    (p : P) (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℝ n (L : P → Q) p‖ ≤ 1 := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => rw [norm_iteratedFDeriv_one,L.hasFDerivAt.fderiv];exact hL
    | succ k => rw [norm_iteratedFDeriv_linear_higher L p k];exact zero_le_one

def normalFrameLinearProjection : NormalFrameParameter →L[ℝ] (X →L[ℝ] X) :=
  (ContinuousLinearMap.snd ℝ ℝ (X →L[ℝ] X)).comp
    (ContinuousLinearMap.snd ℝ X (ℝ × (X →L[ℝ] X)))

lemma normalFrameLinearProjection_apply (p : NormalFrameParameter) : normalFrameLinearProjection p = p.2.2 := rfl

lemma norm_normalFrameLinearProjection_le_one : ‖normalFrameLinearProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  simpa only [one_mul,normalFrameLinearProjection_apply] using (norm_snd_le p.2).trans (norm_snd_le p)

def normalFrameMatrixInput (g : MetricField) (p : NormalFrameParameter) : MatrixFrameInput := (g p.1,p.2.2)

def backgroundAllMetricJetBudget {m : ℕ} (M : Fin (m+1) → ℝ) : ℝ := 1+∑ j,|M j|

lemma backgroundAllMetricJetBudget_ge_one {m : ℕ} (M : Fin (m+1) → ℝ) : 1 ≤ backgroundAllMetricJetBudget M := by
  have hs : 0 ≤ ∑ j,|M j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  dsimp only [backgroundAllMetricJetBudget]
  linarith

lemma abs_metricJet_le_all_budget {m : ℕ} (M : Fin (m+1) → ℝ) (j : Fin (m+1)) :
    |M j| ≤ backgroundAllMetricJetBudget M := by
  have ht : |M j| ≤ ∑ k,|M k| := Finset.single_le_sum (f:=fun k : Fin (m+1) => |M k|) (fun k _ => abs_nonneg (M k)) (Finset.mem_univ j)
  dsimp only [backgroundAllMetricJetBudget]
  linarith

lemma contDiffAt_normalFrameMatrixInput (g : MetricField) (p : NormalFrameParameter)
    (hg : ContDiffAt ℝ ∞ g p.1) : ContDiffAt ℝ ∞ (normalFrameMatrixInput g) p :=
  (hg.comp p contDiffAt_fst).prodMk contDiffAt_snd.snd

/-- The independent matrix input has all its finite jets controlled by
background metric budgets. The frame variable is a linear projection;
no derivative of the admitted frame field enters this bound. -/
theorem Background.normalFrameMatrixInput_jet_bound {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (N : ℕ) (hNm : N ≤ m)
    {p : NormalFrameParameter} (hp : p.1 ∈ Ω) (n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖iteratedFDeriv ℝ n (normalFrameMatrixInput g) p‖ ≤
      ((N.factorial:ℝ)*backgroundAllMetricJetBudget M+1)^n := by
  let B := backgroundAllMetricJetBudget M
  let D := (N.factorial:ℝ)*B+1
  let π : NormalFrameParameter →L[ℝ] X := ContinuousLinearMap.fst ℝ X (ℝ × (X →L[ℝ] X))
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using norm_fst_le q
  have hB1 : 1 ≤ B := backgroundAllMetricJetBudget_ge_one M
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hDB : 0 ≤ (N.factorial:ℝ)*B := by positivity
  have hD1 : 1 ≤ D := by dsimp only [D];linarith
  have hDPow : D ≤ D^n := le_self_pow₀ hD1 (by omega)
  have hg : ContDiffAt ℝ ∞ g p.1 :=
    contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => (h.1.1 i j).contDiffAt (hΩ.mem_nhds hp)))
  have hΓ : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => g q.1) p := hg.comp p contDiffAt_fst
  have hΓBound : ‖iteratedFDeriv ℝ n (fun q : NormalFrameParameter => g q.1) p‖ ≤ (n.factorial:ℝ)*B := by
    have ht := norm_iteratedFDeriv_comp_at_bound (π : NormalFrameParameter → X) g p π.contDiff.contDiffAt hg n B 1
      (fun i hi => (h.reference_matrix_jet_bound hΩ ⟨i,by omega⟩ hp).trans (abs_metricJet_le_all_budget M _))
      (fun i hi _ => by
        simpa only [one_pow] using norm_iteratedFDeriv_clm_le_one π hπ p i hi)
    change ‖iteratedFDeriv ℝ n (fun q : NormalFrameParameter => g q.1) p‖ ≤ (n.factorial:ℝ)*B*1^n at ht
    simpa only [one_pow,mul_one] using ht
  have hL : ContDiffAt ℝ ∞ (fun q : NormalFrameParameter => q.2.2) p := contDiffAt_snd.snd
  change ‖iteratedFDeriv ℝ n (fun q : NormalFrameParameter => (g q.1,q.2.2)) p‖ ≤ D^n
  rw [iteratedFDeriv_prodMk hΓ hL (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · calc
      _ ≤ (n.factorial:ℝ)*B := hΓBound
      _ ≤ (N.factorial:ℝ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hnN) hB0
      _ ≤ D := by dsimp only [D];linarith
      _ ≤ D^n := hDPow
  · have ht := norm_iteratedFDeriv_clm_le_one normalFrameLinearProjection norm_normalFrameLinearProjection_le_one p n hn
    exact ht.trans (one_le_pow₀ hD1)

end ShrinkingSpheres

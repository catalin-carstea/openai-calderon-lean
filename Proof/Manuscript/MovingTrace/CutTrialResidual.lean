module

public import Proof.Manuscript.MovingTrace.PhysicalCollarTrialEquation
public import Proof.Manuscript.MovingTrace.ResidualLiftJetBounds
public import Proof.CalderonN.ParametricBallStrongSolution
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000

open CalderonN Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n+1)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem joint_complexNegativeBallDivergence_contDiff [FiniteDimensional ℝ P]
    {a : P × Z → Mat (n+1)} (ha : ContDiff ℝ ∞ a)
    {u : P × Z → ℂ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun q : P × Z => complexNegativeBallDivergence (fun z => a (q.1,z))
      (fun z => u (q.1,z)) q.2) := by
  have hRe := contDiff_negativeBallDivergence_family ha (Complex.reCLM.contDiff.comp hu)
  have hIm := contDiff_negativeBallDivergence_family ha (Complex.imCLM.contDiff.comp hu)
  have hC := (Complex.ofRealCLM.contDiff.comp hRe).add
    (contDiff_const (c := Complex.I) |>.mul (Complex.ofRealCLM.contDiff.comp hIm))
  convert hC using 1
  funext q
  apply Complex.ext <;> simp [complexNegativeBallDivergence,Function.comp_def]

theorem complexNegativeBallDivergence_zero_of_germ (a : MetricField (n+1))
    {u : Z → ℂ} {z : Z} (hu : u =ᶠ[𝓝 z] fun _ => (0:ℂ)) :
    complexNegativeBallDivergence a u z = 0 := by
  have hZero : negativeBallDivergence a (fun _ => (0:ℝ)) z = 0 := by
    simp [negativeBallDivergence,Elliptic.Lop,Elliptic.pd,coordDeriv]
  have hR : Complex.reCLM ∘ u =ᶠ[𝓝 z] fun _ => (0:ℝ) :=
    hu.mono fun _ hu => by simp [hu]
  have hI : Complex.imCLM ∘ u =ᶠ[𝓝 z] fun _ => (0:ℝ) :=
    hu.mono fun _ hu => by simp [hu]
  apply Complex.ext
  · exact (negativeBallDivergence_congr_germ EventuallyEq.rfl hR).trans hZero
  · exact (negativeBallDivergence_congr_germ EventuallyEq.rfl hI).trans hZero

/-- Force only inside the ball and a band of width h outside it. -/
def cutTrialResidual (a : P × Z → Mat (n+1)) (u : P × Z → ℂ) (h : ℝ) (q : P × Z) : ℂ :=
  residualCutIn ((1-‖q.2‖)/h) *
    complexNegativeBallDivergence (fun z => a (q.1,z)) (fun z => u (q.1,z)) q.2

theorem cutTrialResidual_eq_on_closedBall (a : P × Z → Mat (n+1)) (u : P × Z → ℂ)
    {h : ℝ} (hh : 0 < h) (p : P) {z : Z} (hz : z ∈ closedBall (0:Z) 1) :
    cutTrialResidual a u h (p,z) =
      complexNegativeBallDivergence (fun x => a (p,x)) (fun x => u (p,x)) z := by
  have hZ : ‖z‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hz
  simp [cutTrialResidual,residualCutIn_one (div_nonneg (sub_nonneg.mpr hZ) hh.le)]

theorem cutTrialResidual_contDiff [FiniteDimensional ℝ P] {a : P × Z → Mat (n+1)} (ha : ContDiff ℝ ∞ a)
    {u : P × Z → ℂ} (hu : ContDiff ℝ ∞ u) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (cutTrialResidual a u h) := by
  have hD := joint_complexNegativeBallDivergence_contDiff ha hu
  apply ContDiff.mul ?_ hD
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hz : q.2 = 0
  · have hOpen : IsOpen {p : P × Z | ‖p.2‖ < 1} := isOpen_lt continuous_snd.norm continuous_const
    have hq : q ∈ {p : P × Z | ‖p.2‖ < 1} := by simp [hz]
    apply (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hOpen.mem_nhds hq] with p hp
    exact residualCutIn_one (div_nonneg (sub_nonneg.mpr hp.le) hh.le)
  · apply residualCutIn_contDiff.contDiffAt.comp q
    exact (contDiffAt_const.sub ((contDiffAt_norm ℝ hz).comp q contDiffAt_snd)).div_const h

theorem cutTrialResidual_zero_off_support
    {a : P × Z → Mat (n+1)} {u : P × Z → ℂ}
    {K : Set Z} (hK : IsClosed K) (hU : ∀ p z, z ∉ K → u (p,z) = 0)
    (h : ℝ) (p : P) {z : Z} (hz : z ∉ K) :
    cutTrialResidual a u h (p,z) = 0 := by
  have hu : (fun x => u (p,x)) =ᶠ[𝓝 z] fun _ => (0:ℂ) :=
    Filter.mem_of_superset (hK.isOpen_compl.mem_nhds hz) (hU p)
  change _ * complexNegativeBallDivergence (fun x => a (p,x)) (fun x => u (p,x)) z = 0
  rw [complexNegativeBallDivergence_zero_of_germ _ hu,mul_zero]

end CalderonPaper

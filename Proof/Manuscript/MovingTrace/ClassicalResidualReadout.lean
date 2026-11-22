module

public import Proof.CalderonN.ParametricClassicalBallRepresentative
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open CalderonN CalderonN.BallDirichlet MeasureTheory Metric Set
open scoped ContDiff

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Reading all finite mixed jets of a classical zero-Dirichlet correction
on the closed ball requires only its finite-order strong Sobolev solution.
The estimate holds also where the radial derivative is evaluated on the sphere. -/
theorem parametric_classicalBallRepresentative_parameter_jets
    {V : Set P} (hV : IsOpen V)
    {U : (s : ℕ) → P → StrongDirichletSpace dim s}
    (hU : ∀ s, ContDiffOn ℝ ∞ (U s) V)
    (hAgree : ∀ p ∈ V, ∀ s,
      strongDirichletProjectionL dim s (U s p) = strongDirichletProjectionL dim 0 (U 0 p)) :
    ∃ b : P → X dim → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
      (∀ p ∈ V, TauCeti.W1p.value (strongDirichletProjectionL dim 0 (U 0 p) : FixedBallH1 dim)
        =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] b p) ∧
      (∀ k : ℕ, ContDiffOn ℝ ∞ (fun q : P × X dim => iteratedFDeriv ℝ k (b q.1) q.2)
        (V ×ˢ closedBall (0 : X dim) 1)) ∧
      ∀ k j : ℕ, ∀ p ∈ V, ∀ z ∈ closedBall (0 : X dim) 1,
        ‖iteratedFDeriv ℝ j (fun q => iteratedFDeriv ℝ k (b q) z) p‖ ≤
          ballJetEmbeddingConstant dim * ‖iteratedFDeriv ℝ j (U (k + dim + 1)) p‖ := by
  obtain ⟨b, hb, hbVal, hbJet⟩ := exists_parametric_classicalBallRepresentative hV hU hAgree
  refine ⟨b, hb, hbVal, hbJet, ?_⟩
  intro k j p hp z hz
  let s := k + dim + 1
  let m := s + 2
  have hm : k + dim + 1 ≤ m := by dsimp [m,s]; omega
  let w (q : P) : ClosedBallSobolev dim m :=
    denseSmoothBallSobolev dim m ⟨b q, hb q⟩
  let incA : ClosedBallSobolev dim m →ₗᵢ[ℝ] BallSobolev dim m :=
    ((closedBallSobolev dim) m).toSubmodule.subtypeₗᵢ
  let incS : StrongDirichletSpace dim s →ₗᵢ[ℝ] BallSobolev dim m :=
    ((strongDirichletSubmodule dim) s).toSubmodule.subtypeₗᵢ
  have hSame : EqOn (incA ∘ w) (incS ∘ U s) V := by
    intro q hq
    change smoothBallSobolev m ⟨b q, hb q⟩ = (U s q : BallSobolev dim m)
    apply TauCeti.Wkp.ext m
    apply Lp.ext
    refine (value_smoothBallSobolev_ae m ⟨b q, hb q⟩).trans ?_
    have hv := congrArg (fun u : FixedBallH1Zero dim =>
      TauCeti.W1p.value (u : FixedBallH1 dim)) (hAgree q hq s)
    change TauCeti.W1p.value (strongDirichletProjectionL dim s (U s q) : FixedBallH1 dim) = _ at hv
    rw [strongDirichletProjectionL_apply, TauCeti.Wkp.value_firstOrder] at hv
    change b q =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      ⇑(TauCeti.Wkp.value m (U s q : BallSobolev dim m))
    rw [hv]
    exact (hbVal q hq).symm
  have hInc : ContDiffOn ℝ ∞ (incA ∘ w) V :=
    (incS.toContinuousLinearMap.contDiff.comp_contDiffOn (hU s)).congr hSame
  let : CompleteSpace (ClosedBallSobolev dim m) := completeSpace_closedBallSobolev dim m
  have hw : ContDiffOn ℝ ∞ w V := contDiffOn_top_of_closedRangeLinearIsometry hV incA w hInc
  have heqDeriv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : P → E}
      (hEq : EqOn f g V) : iteratedFDeriv ℝ j f p = iteratedFDeriv ℝ j g p := by
    simpa only [iteratedFDerivWithin_of_isOpen j hV hp] using iteratedFDerivWithin_congr hEq hp j
  have hNorm : ‖iteratedFDeriv ℝ j w p‖ = ‖iteratedFDeriv ℝ j (U s) p‖ := by
    calc
      _ = ‖iteratedFDeriv ℝ j (incA ∘ w) p‖ :=
        (incA.norm_iteratedFDeriv_comp_left (hw.contDiffAt (hV.mem_nhds hp))
          (by simp : (j : ℕ∞ω) ≤ ∞)).symm
      _ = ‖iteratedFDeriv ℝ j (incS ∘ U s) p‖ := by rw [heqDeriv hSame]
      _ = _ := incS.norm_iteratedFDeriv_comp_left ((hU s).contDiffAt (hV.mem_nhds hp))
        (by simp : (j : ℕ∞ω) ≤ ∞)
  let z₀ : UnitClosedBall dim := ⟨z, hz⟩
  let ev : ClosedBallSobolev dim m →L[ℝ] BallJet dim k :=
    (ContinuousMap.evalCLM ℝ z₀).comp (closedBallJetL dim k m)
  have hEv : EqOn (ev ∘ w) (fun q => iteratedFDeriv ℝ k (b q) z) V := by
    intro q hq
    simp only [Function.comp_apply, ev, ContinuousLinearMap.comp_apply, w,
      closedBallJetL_on_smooth k m hm]
    rfl
  have hEvNorm : ‖ev‖ ≤ ballJetEmbeddingConstant dim :=
    ContinuousLinearMap.opNorm_le_bound ev (ballJetEmbeddingConstant_nonneg dim)
      (fun g => norm_closedBallJetL_apply_le k m hm g z₀)
  rw [← heqDeriv hEv]
  exact (ev.norm_iteratedFDeriv_comp_left (hw.contDiffAt (hV.mem_nhds hp))
    (by simp : (j : ℕ∞ω) ≤ ∞)).trans
    (hNorm ▸ mul_le_mul_of_nonneg_right hEvNorm (norm_nonneg _))

end CalderonPaper

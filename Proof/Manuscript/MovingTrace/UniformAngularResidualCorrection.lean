module

public import Proof.Manuscript.MovingTrace.ClassicalBoundaryJetReadout
public import Proof.Manuscript.MovingTrace.UniformResidualOperator
public import Proof.Manuscript.MovingTrace.ResidualForcingJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3400000

open CalderonN CalderonN.BallDirichlet MeasureTheory Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {P Q E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A single strong-order solve controls the joint geometry, frequency,
and angular readout jets of the classical residual correction. -/
theorem uniform_classical_zeroDirichlet_residual_angular_jets
    {V J : Set P} (hV : IsOpen V) (hJ : IsCompact J) (hJV : J ⊆ V)
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSuppA : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p))
    (w : E → X dim) (hw : ContDiff ℝ ∞ w) (hwB : ∀ x, w x ∈ closedBall (0:X dim) 1)
    {K : Set E} (hK : IsCompact K) (k N : ℕ) :
    let s := k+N+dim+1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : (P × Q) × X dim → ℝ) (hf : ContDiff ℝ ∞ f)
      (Kf : Set (X dim)) (hKf : IsCompact Kf) (hSuppF : ∀ p z, z ∉ Kf → f (p,z) = 0),
      ∃ b : (P × Q) → X dim → ℝ,
        (∀ p, ContDiff ℝ ∞ (b p)) ∧
        (∀ p : P × Q, p.1 ∈ V → EqOn (b p) 0 (standardSphere dim) ∧
          EqOn (negativeBallDivergence (fun z => a (p.1,z)) (b p))
            (fun z => f (p,z)) (ball (0 : X dim) 1)) ∧
        (∀ l : ℕ, ContDiffOn ℝ ∞ (fun q : (P × Q) × X dim => iteratedFDeriv ℝ l (b q.1) q.2)
          ((V ×ˢ univ) ×ˢ closedBall (0 : X dim) 1)) ∧
        ∀ p : P × Q, p.1 ∈ J → ∀ x ∈ K, ∀ M : ℝ, 0 ≤ M →
          (∀ j ≤ N, ∀ l ≤ s+1, ∀ z,
            ‖iteratedFDeriv ℝ j (fun q => iteratedFDeriv ℝ l (fun y => f (q,y)) z) p‖ ≤ M) →
          ∀ j ≤ N, ‖iteratedFDeriv ℝ j
            (fun q : (P × Q) × E => iteratedFDeriv ℝ k (b q.1) (w q.2)) (p,x)‖ ≤ C*M := by
  dsimp only
  let s := k+N+dim+1
  let V' : Set (P × Q) := V ×ˢ univ
  have hV' : IsOpen V' := hV.prod isOpen_univ
  let a' : (P × Q) × X dim → Mat dim := fun q => a (q.1.1,q.2)
  have ha' : ContDiff ℝ ∞ a' := ha.comp ((contDiff_fst.fst).prodMk contDiff_snd)
  have hSuppA' (p : P × Q) (z : X dim) (hz : z ∉ Ka) : a' (p,z) = 0 := hSuppA p.1 z hz
  have hEll' (p : P × Q) (hp : p ∈ V') :
      TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
        (fun z => a' (p,z)) (lo p.1) (hi p.1) := hEll p.1 hp.1
  obtain ⟨C₁,hC₁,hInverse⟩ := uniform_ball_dirichlet_inverse_residual_jets (Q := Q)
    hV hJ hJV a ha Ka hKa hSuppA lo hi hEll s N
  obtain ⟨C₂,hC₂,hForcing⟩ := ballForcingFamily_all_parameter_jets (P := P × Q) (dim := dim) s
  obtain ⟨C₃,hC₃,hRead⟩ := parametric_classicalBallRepresentative_angular_jets
    hV' w hw hwB hK k N
  refine ⟨C₃*C₁*C₂,by positivity,?_⟩
  intro f hf Kf hKf hSuppF
  obtain ⟨U,hU,hEquation⟩ := exists_parametric_ballStrongSolution V'
    a' ha' Ka hKa hSuppA' f hf Kf hKf hSuppF (lo ∘ Prod.fst) (hi ∘ Prod.fst) hEll'
  obtain ⟨b,hb,hValue,hJet,hReadout⟩ := hRead U hU (fun p hp t => (hEquation p hp t).1)
  refine ⟨b,hb,?_,hJet,?_⟩
  · intro p hp
    have hp' : p ∈ V' := ⟨hp,mem_univ _⟩
    let sol := strongDirichletProjectionL dim 0 (U 0 p)
    have hA : ContDiff ℝ ∞ (fun z => a (p.1,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
    have hF : ContDiff ℝ ∞ (fun z => f (p,z)) := hf.comp (contDiff_const.prodMk contDiff_id)
    exact ⟨eqOn_zero_sphere_of_ballH1Zero (hb p) sol (hValue p hp'),
      negativeBallDivergence_eq_of_ballWeakSolution hA hF (hb p) sol (hValue p hp') _
        (ballForcingFamily_value 0 f hf Kf hKf hSuppF p) (hEquation p hp' 0).2.1⟩
  · intro p hp x hx M hM hResidual j hj
    let F := ballForcingFamily s f hf Kf hKf hSuppF
    let T (q : P) := (strongDirichletOperator fixedSobolevCalculus s
      (commonSupportMatrixFamily (s+2) a ha Ka hKa hSuppA q)).inverse
    have hFJet : ∀ l ≤ N, ‖iteratedFDeriv ℝ l F p‖ ≤ C₂*M :=
      hForcing f hf Kf hKf hSuppF p N M hM hResidual
    have hEq : EqOn (U s) (fun q : P × Q => T q.1 (F q)) V' := by
      intro q hq
      rw [(hEquation q hq s).2.2]
      rfl
    have hp' : p ∈ V' := ⟨hJV hp,mem_univ _⟩
    have hUJet (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (U s) p‖ ≤ C₁*(C₂*M) := by
      have hUEq : iteratedFDeriv ℝ l (U s) p =
          iteratedFDeriv ℝ l (fun q : P × Q => T q.1 (F q)) p := by
        simpa only [iteratedFDerivWithin_of_isOpen l hV' hp'] using
          iteratedFDerivWithin_congr hEq hp' l
      rw [hUEq]
      exact hInverse F p hp (contDiff_ballForcingFamily s f hf Kf hKf hSuppF).contDiffAt
        (C₂*M) (mul_nonneg hC₂ hM) hFJet l hl
    exact (hReadout p hp' x hx (C₁*(C₂*M)) (by positivity) hUJet j hj).trans_eq (by ring)

end CalderonPaper

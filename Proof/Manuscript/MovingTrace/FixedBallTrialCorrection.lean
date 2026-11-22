module

public import Proof.Manuscript.MovingTrace.UniformClassicalResidualCorrection
public import Proof.CalderonN.ParametricBallConormal
public import Proof.CalderonN.SmoothStrongBallEstimates
public import Proof.CalderonN.MixedSliceJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 3200000

open CalderonN CalderonN.BallDirichlet Set Metric
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]

/-- Every jet of a globally smooth representative on the closed ball
is independent of its extension across the sphere. -/
theorem eqOn_iteratedFDeriv_closedUnitBall {b c : X dim → ℝ}
    (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (he : EqOn b c (closedBall (0 : X dim) 1)) (k : ℕ) :
    EqOn (iteratedFDeriv ℝ k b) (iteratedFDeriv ℝ k c) (closedBall (0 : X dim) 1) := by
  intro z hz
  have hU : UniqueDiffOn ℝ (closedBall (0 : X dim) 1) :=
    uniqueDiffOn_convex (convex_closedBall _ _) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0,by simp⟩)
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hU (hb.contDiffAt.of_le (by simp)) hz,
    ← iteratedFDerivWithin_eq_iteratedFDeriv hU (hc.contDiffAt.of_le (by simp)) hz]
  exact iteratedFDerivWithin_congr he hz k

/-- Any finite trial having the exact Dirichlet datum can be compared
to the canonical Poisson solution with the uniform inverse bound for its
residual. The forcing extension only has to agree on the open ball. -/
theorem uniform_fixedBallPoisson_trial_correction
    {V J : Set P} (hV : IsOpen V) (hJ : IsCompact J) (hJV : J ⊆ V)
    {U : Set (P × X dim)} (hU : IsOpen U)
    (hCU : V ×ˢ closedBall (0 : X dim) 1 ⊆ U)
    (g : P × X dim → Mat dim)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef)
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSuppA : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (hA : ∀ q ∈ U, ∀ i j, a q i j = divergenceCoeff (fun z => g (q.1,z)) q.2 i j)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p))
    (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u d f : (P × Q) × X dim → ℝ) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ f)
        (Kf : Set (X dim)) (hKf : IsCompact Kf) (hSuppF : ∀ p z, z ∉ Kf → f (p,z) = 0)
        (hDatum : ∀ p : P × Q, p.1 ∈ V → EqOn (fun z => u (p,z)) (fun z => d (p,z)) (standardSphere dim))
        (hEq : ∀ p : P × Q, p.1 ∈ V → EqOn
          (negativeBallDivergence (fun z => a (p.1,z)) (fun z => u (p,z)))
          (fun z => f (p,z)) (ball (0 : X dim) 1)),
        let b (p : P × Q) := fixedBallPoisson (fun z => g (p.1,z)) (fun z => d (p,z))
        (∀ l : ℕ, ContDiffOn ℝ ∞ (fun q : (P × Q) × X dim => iteratedFDeriv ℝ l (b q.1) q.2)
          ((V ×ˢ univ) ×ˢ closedBall (0 : X dim) 1)) ∧
        ∀ p : P × Q, p.1 ∈ J → ∀ M : ℝ, 0 ≤ M →
          (∀ j ≤ N, ∀ l ≤ k + dim + 2, ∀ z,
            ‖iteratedFDeriv ℝ j (fun q => iteratedFDeriv ℝ l (fun x => f (q,x)) z) p‖ ≤ M) →
          ∀ j ≤ N, ∀ z ∈ closedBall (0 : X dim) 1,
            ‖iteratedFDeriv ℝ j (fun q => iteratedFDeriv ℝ k (fun x => b q x - u (q,x)) z) p‖ ≤ C*M := by
  obtain ⟨C,hC,hCorr⟩ := uniform_classical_zeroDirichlet_residual_jets (Q := Q)
    hV hJ hJV a ha Ka hKa hSuppA lo hi hEll k N
  refine ⟨C,hC,?_⟩
  intro u d f hu hf Kf hKf hSuppF hDatum hEq
  dsimp only
  let L := V ×ˢ (univ : Set Q)
  have hL : IsOpen L := hV.prod isOpen_univ
  obtain ⟨b,hb,hB,hJet,hBound⟩ := hCorr f hf Kf hKf hSuppF
  let sol (p : P × Q) (z : X dim) := u (p,z)-b p z
  have hSolD (p : P × Q) : ContDiff ℝ ∞ (sol p) :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).sub (hb p)
  let c (p : P × Q) := fixedBallPoisson (fun z => g (p.1,z)) (fun z => d (p,z))
  have hCompare (p : P × Q) (hp : p ∈ L) :
      ContDiff ℝ ∞ (c p) ∧ EqOn (c p) (sol p) (closedBall (0 : X dim) 1) := by
    let S : Set (X dim) := (Prod.mk p.1) ⁻¹' U
    have hS : IsOpen S := hU.preimage (continuous_const.prodMk continuous_id)
    have hCS : closedBall (0 : X dim) 1 ⊆ S := fun z hz => hCU ⟨hp.1,hz⟩
    have hM : SmoothMetric S (fun z => g (p.1,z)) := by
      refine ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ hx => hx), fun z hz => hPos _ hz⟩
    have hLap (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
        laplace (fun x => g (p.1,x)) (sol p) z = 0 := by
      have hzS := hCS (ball_subset_closedBall hz)
      have hD := negativeBallDivergence_eq_neg_laplace hS hM
        (fun x hx => hA (p.1,x) hx) (hSolD p).contDiffOn hzS
      have haS : ContDiff ℝ ∞ (fun z => a (p.1,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
      have huS : ContDiff ℝ ∞ (fun z => u (p,z)) := hu.comp (contDiff_const.prodMk contDiff_id)
      have hD₀ := negativeBallDivergence_sub_solution haS
        ⟨fun z => u (p,z),huS⟩ ⟨b p,hb p⟩ z
      change negativeBallDivergence (fun x => a (p.1,x)) (sol p) z =
        negativeBallDivergence (fun x => a (p.1,x)) (fun z => u (p,z)) z -
          negativeBallDivergence (fun x => a (p.1,x)) (b p) z at hD₀
      rw [hEq p hp.1 hz,(hB p hp.1).2 hz,sub_self] at hD₀
      rw [hD₀] at hD
      exact (mul_eq_zero.mp (neg_eq_zero.mp hD.symm)).resolve_left
        (Real.sqrt_pos.mpr (hM.2 z hzS).det_pos).ne'
    have hSol : FixedBallSolution (fun z => g (p.1,z)) (fun z => d (p,z)) (sol p) := by
      refine ⟨hSolD p,fun z hz => ?_,hLap⟩
      change u (p,z) - b p z = d (p,z)
      rw [show b p z = 0 from (hB p hp.1).1 hz,sub_zero]
      exact hDatum p hp.1 hz
    have hExist : ∃ w, FixedBallSolution (fun z => g (p.1,z)) (fun z => d (p,z)) w := ⟨sol p,hSol⟩
    have hCan : FixedBallSolution (fun z => g (p.1,z)) (fun z => d (p,z)) (c p) := by
      dsimp only [c,fixedBallPoisson]
      rw [dite_eq_left hExist]
      exact Classical.choose_spec hExist
    exact ⟨hCan.1,eqOn_fixedBallSolution hS hCS hM hCan hSol (fun _ _ => rfl)⟩
  have hVal (p : P × Q) (hp : p ∈ L) (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) (l : ℕ) :
      iteratedFDeriv ℝ l (c p) z =
        iteratedFDeriv ℝ l (fun x => u (p,x)) z - iteratedFDeriv ℝ l (b p) z := by
    have hC := hCompare p hp
    rw [eqOn_iteratedFDeriv_closedUnitBall hC.1 (hSolD p) hC.2 l hz]
    exact fun_iteratedFDeriv_sub_apply ((hu.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
      ((hb p).contDiffAt.of_le (by simp))
  constructor
  · intro l
    apply ((contDiff_iteratedFDeriv_slice_right hu l).contDiffOn.sub (hJet l)).congr
    rintro ⟨p,z⟩ ⟨hp,hz⟩
    exact hVal p hp z hz l
  · intro p hp M hM hF j hj z hz
    have hpL : p ∈ L := ⟨hJV hp,mem_univ _⟩
    have hEqL : EqOn
        (fun q : P × Q => iteratedFDeriv ℝ k (fun x => c q x-u (q,x)) z)
        (fun q : P × Q => -iteratedFDeriv ℝ k (b q) z) L := by
      intro q hq
      have hC := hCompare q hq
      have hUq : ContDiff ℝ ∞ (fun x => u (q,x)) := hu.comp (contDiff_const.prodMk contDiff_id)
      change iteratedFDeriv ℝ k (fun x => c q x-u (q,x)) z = _
      rw [fun_iteratedFDeriv_sub_apply (hC.1.contDiffAt.of_le (by simp)) (hUq.contDiffAt.of_le (by simp)),
        hVal q hq z hz k]
      abel
    rw [← iteratedFDerivWithin_of_isOpen j hL hpL,iteratedFDerivWithin_congr hEqL hpL j,
      iteratedFDerivWithin_of_isOpen j hL hpL]
    change ‖iteratedFDeriv ℝ j (-(fun q : P × Q => iteratedFDeriv ℝ k (b q) z)) p‖ ≤ C*M
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hBound p hp M hM hF j hj z hz

end CalderonPaper

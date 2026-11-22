module

public import Proof.CalderonN.BilinearFamilyJetBounds
public import Proof.CalderonN.CompactLocalJetBounds
public import Proof.CalderonN.ParametricBallStrongSolution
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 1300000

open CalderonN Filter Set
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonPaper

variable {P Q H W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Applying a parameter-dependent operator with uniformly bounded jets on a
compact set preserves a common estimate on the entire forcing jet. The
second parameter, such as the frequency of a plane wave, need not stay
in any bounded set. -/
theorem uniform_finite_jets_of_operator_on_residual
    {U J : Set P} (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    (T : P → H →L[ℝ] W) (hT : ContDiffOn ℝ ∞ T U) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : P × Q → H) (q : P × Q), q.1 ∈ J →
      ContDiffAt ℝ ∞ F q → ∀ M : ℝ, 0 ≤ M →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j F q‖ ≤ M) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun p : P × Q => T p.1 (F p)) q‖ ≤ C * M := by
  obtain ⟨B, hB, hJets⟩ := exists_uniform_local_finite_jet_bound hJ
    (fun p hp => hT.contDiffAt (hU.mem_nhds (hJU hp))) N
  let ev : (H →L[ℝ] W) →L[ℝ] (H →L[ℝ] W) := ContinuousLinearMap.id ℝ _
  let fst : P × Q →L[ℝ] P := ContinuousLinearMap.fst ℝ P Q
  refine ⟨‖ev‖ * 2 ^ N * B, by positivity, ?_⟩
  intro F q hq hF M hM hResidual j hj
  have hqU : fst q ∈ U := hJU hq
  have hU' : IsOpen (fst ⁻¹' U) := hU.preimage fst.continuous
  have hT' := hT.comp_continuousLinearMap fst
  have hAt : ContDiffAt ℝ ∞ (T ∘ fst) q := hT'.contDiffAt (hU'.mem_nhds hqU)
  have hProductJets (k : ℕ) (hk : k ≤ N) : ‖iteratedFDeriv ℝ k (T ∘ fst) q‖ ≤ B := by
    have he := fst.iteratedFDerivWithin_comp_right hT hU.uniqueDiffOn hU'.uniqueDiffOn hqU
      (by simp : (k : ℕ∞ω) ≤ ∞)
    rw [iteratedFDerivWithin_of_isOpen k hU' hqU,
      iteratedFDerivWithin_of_isOpen k hU hqU] at he
    rw [he]
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    simp only [Finset.prod_const, Finset.card_fin]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ P Q))
      (norm_nonneg _)).trans (by rw [mul_one]; exact hJets q.1 hq k hk)
  exact ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound ev (T ∘ fst) F q
    hAt hF N B M (zero_le_one.trans hB) hM hProductJets hResidual j hj

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [FiniteDimensional ℝ P]

/-- The actual fixed-ball zero-Dirichlet inverse has uniform bounds for
every finite joint parameter jet of a residual in the strong solution
norm, including derivatives in an unbounded frequency parameter. -/
theorem uniform_ball_dirichlet_inverse_residual_jets
    {U J : Set P} (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hSupport : ∀ p z, z ∉ K → a (p,z) = 0)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ U, TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) (s N : ℕ) :
    let T := fun p : P =>
      (strongDirichletOperator fixedSobolevCalculus s
        (commonSupportMatrixFamily (s+2) a ha K hK hSupport p)).inverse
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : P × Q → BallSobolev dim s) (q : P × Q), q.1 ∈ J →
      ContDiffAt ℝ ∞ F q → ∀ M : ℝ, 0 ≤ M →
      (∀ j ≤ N, ‖iteratedFDeriv ℝ j F q‖ ≤ M) →
      ∀ j ≤ N, ‖iteratedFDeriv ℝ j (fun p : P × Q => T p.1 (F p)) q‖ ≤ C * M := by
  exact uniform_finite_jets_of_operator_on_residual (Q := Q) hU hJ hJU _
    (contDiffOn_commonSupport_actual_strongDirichletInverse fixedSobolevCalculus
      fixedDirichletRegularity s a ha K hK hSupport U lo hi hEll) N

end CalderonPaper

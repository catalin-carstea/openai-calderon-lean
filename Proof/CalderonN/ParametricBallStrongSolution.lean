module

public import Proof.CalderonN.Coercivity
public import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator
public import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev
public import Proof.CalderonN.BallRegularity.Multiplier

import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonN

variable {dim : ℕ} [NeZero dim]



open CalderonN.BallDirichlet

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A common-support smooth right-hand side, as a member of the fixed-ball
Sobolev space. Multiplication of the constant function provides the
canonical lift. -/
@[expose] def ballForcingFamily (k : ℕ) (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → f (p,z) = 0)
    (p : P) : (BallSobolev dim) k :=
  coefficientMultiplier fixedSobolevCalculus k (commonSupportCoefficientFamily (k+1) f hf K hK hSupp p)
    (smoothBallSobolev k ⟨1,contDiff_const⟩)

theorem contDiff_ballForcingFamily (k : ℕ) (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → f (p,z) = 0) :
    ContDiff ℝ ∞ (ballForcingFamily k f hf K hK hSupp) :=
  (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus k f hf K hK hSupp).clm_apply
    contDiff_const

theorem ballForcingFamily_value (k : ℕ) (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (K : Set (X dim)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → f (p,z) = 0) (p : P) :
    TauCeti.Wkp.value k (ballForcingFamily k f hf K hK hSupp p)
      =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] fun z => f (p,z) := by
  refine (coefficientMultiplier_value_ae fixedSobolevCalculus k
    (commonSupportCoefficientFamily (k+1) f hf K hK hSupp p) _).trans ?_
  have h1 := value_smoothBallSobolev_ae k (⟨1,contDiff_const⟩ : SmoothData dim)
  filter_upwards [h1] with z hz
  rw [show coefficientValue (k+1) (commonSupportCoefficientFamily (k+1) f hf K hK hSupp p) z =
    f (p,z) from coefficientValue_commonSupportCoefficientFamily (k+1) f hf K hK hSupp p z,hz]
  simp

set_option maxHeartbeats 1600000 in
/-- The strong inverses at all orders describe the same weak solution.
Every order depends smoothly on the coefficients and forcing. -/
theorem exists_parametric_ballStrongSolution
    (V : Set P)
    (a : P × (X dim) → (Mat dim)) (ha : ContDiff ℝ ∞ a)
    (Ka : Set (X dim)) (hKa : IsCompact Ka) (hSa : ∀ p z, z ∉ Ka → a (p,z) = 0)
    (f : P × (X dim) → ℝ) (hf : ContDiff ℝ ∞ f)
    (Kf : Set (X dim)) (hKf : IsCompact Kf) (hSf : ∀ p z, z ∉ Kf → f (p,z) = 0)
    (lo hi : P → ℝ)
    (hEll : ∀ p ∈ V, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lo p) (hi p)) :
    ∃ U : (s : ℕ) → P → (StrongDirichletSpace dim) s,
      (∀ s, ContDiffOn ℝ ∞ (U s) V) ∧
      ∀ p ∈ V, ∀ s,
        (strongDirichletProjectionL dim) s (U s p) = (strongDirichletProjectionL dim) 0 (U 0 p) ∧
        TauCeti.PDE.IsWeakSolutionDirichlet (fun z => a (p,z)) 0 0
          (TauCeti.Wkp.value 0 (ballForcingFamily 0 f hf Kf hKf hSf p))
          ((strongDirichletProjectionL dim) s (U s p)) ∧
        U s p =
          (strongDirichletOperator fixedSobolevCalculus s
            (commonSupportMatrixFamily (s+2) a ha Ka hKa hSa p)).inverse
            (ballForcingFamily s f hf Kf hKf hSf p) := by
  let A (s : ℕ) (p : P) := commonSupportMatrixFamily (s+2) a ha Ka hKa hSa p
  let F (s : ℕ) := ballForcingFamily s f hf Kf hKf hSf
  let U (s : ℕ) (p : P) : (StrongDirichletSpace dim) s :=
    (strongDirichletOperator fixedSobolevCalculus s (A s p)).inverse (F s p)
  have hC (s : ℕ) (p : P) : coefficientMatrixField (s+2) (A s p) = fun z => a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily _ a ha Ka hKa hSa p
  have hU (s : ℕ) : ContDiffOn ℝ ∞ (U s) V :=
    (contDiffOn_commonSupport_actual_strongDirichletInverse fixedSobolevCalculus
      fixedDirichletRegularity s a ha Ka hKa hSa V lo hi hEll).clm_apply
      (contDiff_ballForcingFamily s f hf Kf hKf hSf).contDiffOn
  refine ⟨U,hU,fun p hp s => ?_⟩
  have hEllA (s : ℕ) : TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (coefficientMatrixField (s+2) (A s p)) (lo p) (hi p) := hC s p ▸ hEll p hp
  have hInvertible (s : ℕ) : (strongDirichletOperator fixedSobolevCalculus s (A s p)).IsInvertible :=
    strongDirichletOperator_isInvertible_of_elliptic fixedSobolevCalculus fixedDirichletRegularity
      s (A s p) (hEllA s)
  have hForce (s : ℕ) : TauCeti.Wkp.value s (F s p) = TauCeti.Wkp.value 0 (F 0 p) :=
    Lp.ext ((ballForcingFamily_value s f hf Kf hKf hSf p).trans (ballForcingFamily_value 0 f hf Kf hKf hSf p).symm)
  have hSolve (s : ℕ) :
      TauCeti.PDE.IsWeakSolutionDirichlet (fun z => a (p,z)) 0 0
        (TauCeti.Wkp.value 0 (F 0 p)) ((strongDirichletProjectionL dim) s (U s p)) := by
    intro v
    have hEnergy := strongCoefficientOperator_energy fixedSobolevCalculus s (A s p) (U s p) v
    have hApply : strongDirichletOperator fixedSobolevCalculus s (A s p) (U s p) = F s p :=
      (hInvertible s).self_apply_inverse _
    rw [hApply,hForce s,hC s p] at hEnergy
    exact hEnergy.symm
  obtain ⟨w,hw,huniq⟩ := existsUnique_fixedBall_weakSolution
    (ha.comp (contDiff_const.prodMk contDiff_id)).continuous (hEll p hp)
    (TauCeti.Wkp.value 0 (F 0 p))
  exact ⟨(huniq _ (hSolve s)).trans (huniq _ (hSolve 0)).symm,hSolve s,rfl⟩

end CalderonN

module

public import Proof.CalderonN.BallPoissonOperator
public import Proof.CalderonN.SmoothZeroTraceMembership

import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator
import Mathlib.Tactic

public section

noncomputable section

open Set MeasureTheory Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

/-- Expose the strong inverse as an operator into the ordinary Sobolev
space with two extra derivatives. Its smooth values come from the same
classical zero-trace solution at every order. -/
@[expose] def fullStrongBallInverseL (s : ℕ) (A : SmoothCoefficientMatrix n (s+2)) :
    BallSobolev n s →L[ℝ] BallSobolev n (s+2) :=
  ((strongDirichletSubmodule n) s).toSubmodule.subtypeL.comp
    (strongDirichletOperator fixedSobolevCalculus s A).inverse

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 1700000 in
theorem fullStrongBallInverseL_of_classical
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (p : P) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi)
    (f w : SmoothData n) (hw : EqOn w.1 0 (standardSphere n))
    (hEq : EqOn (negativeBallDivergence (fun z => a (p,z)) w.1) f.1 (ball (0 : X n) 1)) (s : ℕ) :
    fullStrongBallInverseL s (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)
      (smoothBallSobolev s f) = smoothBallSobolev (s+2) w := by
  let A (s : ℕ) := commonSupportMatrixFamily (s+2) a ha K hK hSupp p
  have hEllA (s : ℕ) : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
      (coefficientMatrixField (s+2) (A s)) lo hi := by
    rw [coefficientMatrixField_commonSupportMatrixFamily]
    exact hEll
  have hMem := smoothSobolev_mem_zero_of_eqOn_sphere (A 0) (hEllA 0) w hw
  let v : StrongDirichletSpace n s :=
    ⟨smoothBallSobolev (s+2) w, (mem_strongDirichletSubmodule s _).mpr (by
      rw [firstOrder_smoothBallSobolev]
      exact hMem)⟩
  have hV : strongDirichletOperator fixedSobolevCalculus s (A s) v = smoothBallSobolev s f := by
    have hFull : strongDirichletOperator fixedSobolevCalculus s (A s) v =
        fullBallDivergenceL s (A s) (smoothBallSobolev (s+2) w) := by
      rw [strongDirichletOperator_apply fixedSobolevCalculus s (A s) v]
      simp only [fullBallDivergenceL,coefficientDivergenceL_apply_apply,
        coefficientMatrixMultiplierL_apply,strongCoordinateDerivativeL,ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply,v]
    rw [hFull,fullBallDivergence_family_smooth s a ha K hK hSupp p w]
    exact smoothBallSobolev_eq_of_eqOn_ball s _ _ hEq
  have hInv := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity s (A s) (hEllA s)
  change ((strongDirichletOperator fixedSobolevCalculus s (A s)).inverse
    (smoothBallSobolev s f) : StrongDirichletSpace n s).1 = _
  rw [← hV,hInv.inverse_apply_self]

set_option maxHeartbeats 2400000 in
theorem exists_classical_fullStrongBallInverseL_family
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (p : P) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi)
    (f : SmoothData n) :
    ∃ w : SmoothData n, EqOn w.1 0 (standardSphere n) ∧
      EqOn (negativeBallDivergence (fun z => a (p,z)) w.1) f.1 (ball (0 : X n) 1) ∧
      ∀ s, fullStrongBallInverseL s (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)
        (smoothBallSobolev s f) = smoothBallSobolev (s+2) w := by
  let A (s : ℕ) := commonSupportMatrixFamily (s+2) a ha K hK hSupp p
  have hA (s : ℕ) : coefficientMatrixField (s+2) (A s) = fun z => a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily _ a ha K hK hSupp p
  have hEllA (s : ℕ) : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
      (coefficientMatrixField (s+2) (A s)) lo hi := by
    rw [hA s]
    exact hEll
  obtain ⟨w,hw,hEq,_⟩ := exists_native_classical_zeroDirichlet (A 0) (hEllA 0) f
  rw [hA 0] at hEq
  exact ⟨w,hw,hEq,fullStrongBallInverseL_of_classical a ha K hK hSupp p hEll f w hw hEq⟩

end CalderonPaper.LowerGreen

end

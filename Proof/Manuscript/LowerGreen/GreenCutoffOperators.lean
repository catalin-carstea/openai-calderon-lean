module

public import Proof.Manuscript.LowerGreen.FirstOrderBallFamily
public import Proof.CalderonN.GreenSourceCutoff

import Proof.CalderonN.ParametricBallStrongSolution
import Mathlib.Tactic

public section

noncomputable section

open Set MeasureTheory Filter CalderonN CalderonN.BallDirichlet TauCeti
open scoped Topology ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

set_option maxHeartbeats 1500000

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

@[expose] def greenCutoffFirstCoefficient (a : P × X n → Mat n) (χ : X n → ℝ) (j : I n)
    (q : P × X n) : ℝ :=
  -2 * ∑ i, a q i j * coordDeriv i χ q.2

@[expose] def greenCutoffZeroCoefficient (a : P × X n → Mat n) (χ : X n → ℝ) (q : P × X n) : ℝ :=
  negativeBallDivergence (fun x => a (q.1,x)) χ q.2

theorem contDiff_greenCutoffFirstCoefficient
    {a : P × X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : I n) :
    ContDiff ℝ ∞ (greenCutoffFirstCoefficient a χ j) := by
  have hd (i : I n) : ContDiff ℝ ∞ (coordDeriv i χ) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  apply contDiff_const.mul
  exact ContDiff.sum (fun i _ =>
    ((((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp ha)).mul
      ((hd i).comp contDiff_snd))

theorem contDiff_greenCutoffZeroCoefficient
    {a : P × X n → Mat n} (ha : ContDiff ℝ ∞ a)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (greenCutoffZeroCoefficient a χ) := by
  change ContDiff ℝ ∞ (fun q : P × X n => negativeBallDivergence
    (fun x => a (q.1,x)) (fun x => χ x) q.2)
  exact contDiff_negativeBallDivergence_family (a := a) (u := fun q : P × X n => χ q.2)
    ha (hχ.comp contDiff_snd)

theorem greenCutoffFirstCoefficient_vanishes
    (a : P × X n → Mat n) (χ : X n → ℝ) (j : I n) (p : P) (z : X n)
    (hz : z ∉ tsupport χ) : greenCutoffFirstCoefficient a χ j (p,z) = 0 := by
  have hc := (notMem_tsupport_iff_eventuallyEq.mp hz).fderiv_eq (𝕜 := ℝ)
  have hz' : fderiv ℝ (0 : X n → ℝ) z = 0 := by
    change fderiv ℝ (fun _ : X n => (0 : ℝ)) z = 0
    simp
  have hzero : fderiv ℝ χ z = 0 := hc.trans hz' 
  simp only [greenCutoffFirstCoefficient,coordDeriv,hzero,zero_apply,mul_zero,Finset.sum_const_zero]

theorem greenCutoffZeroCoefficient_vanishes
    (a : P × X n → Mat n) (χ : X n → ℝ) (p : P) (z : X n)
    (hz : z ∉ tsupport χ) : greenCutoffZeroCoefficient a χ (p,z) = 0 := by
  unfold greenCutoffZeroCoefficient
  rw [negativeBallDivergence_congr_germ EventuallyEq.rfl (notMem_tsupport_iff_eventuallyEq.mp hz)]
  change negativeBallDivergence (fun x => a (p,x)) (fun _ => 0) z = 0
  simp [negativeBallDivergence,Elliptic.Lop,Elliptic.pd_const]

theorem greenSourceCutoffError_firstOrder
    (a : P × X n → Mat n) (χ u : X n → ℝ) (p : P) (z : X n) :
    greenSourceCutoffError (fun x => a (p,x)) χ u z =
      (∑ j, greenCutoffFirstCoefficient a χ j (p,z) * coordDeriv j u z) +
      greenCutoffZeroCoefficient a χ (p,z) * u z := by
  unfold greenSourceCutoffError greenCutoffFirstCoefficient greenCutoffZeroCoefficient
  dsimp only
  have hs : (-2 : ℝ) * (∑ i, ∑ j, a (p,z) i j * coordDeriv i χ z * coordDeriv j u z) =
      ∑ j, ((-2 : ℝ) * ∑ i, a (p,z) i j * coordDeriv i χ z) * coordDeriv j u z := by
    rw [Finset.sum_comm,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, Finset.sum_mul]
  have hs' : (2 : ℝ) * (∑ i, ∑ j, a (p,z) i j * coordDeriv i χ z * coordDeriv j u z) =
      -(∑ j, ((-2 : ℝ) * ∑ i, a (p,z) i j * coordDeriv i χ z) * coordDeriv j u z) := by
    rw [← hs]
    ring
  rw [hs']
  ring


@[expose] def greenCutoffOperatorFamily (s : ℕ) (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    BallSobolev n (s+1) →L[ℝ] BallSobolev n s :=
  firstOrderBallL s
    (fun j => commonSupportCoefficientFamily (s+1) (greenCutoffFirstCoefficient a χ.1 j)
      (contDiff_greenCutoffFirstCoefficient ha χ.2 j) (tsupport χ.1) hχ.isCompact
      (greenCutoffFirstCoefficient_vanishes a χ.1 j) p)
    (commonSupportCoefficientFamily (s+1) (greenCutoffZeroCoefficient a χ.1)
      (contDiff_greenCutoffZeroCoefficient ha χ.2) (tsupport χ.1) hχ.isCompact
      (greenCutoffZeroCoefficient_vanishes a χ.1) p)

theorem contDiff_greenCutoffOperatorFamily (s : ℕ)
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiff ℝ ∞ (greenCutoffOperatorFamily s a ha χ hχ) :=
  contDiff_firstOrderBallL_family s _ _ (contDiff_greenCutoffFirstCoefficient ha χ.2)
    (contDiff_greenCutoffZeroCoefficient ha χ.2) _ hχ.isCompact _ _

theorem greenCutoffOperatorFamily_smooth (s : ℕ)
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ : SmoothData n) (hχ : HasCompactSupport χ.1)
    (p : P) (u : SmoothData n) :
    greenCutoffOperatorFamily s a ha χ hχ p (smoothBallSobolev (s+1) u) =
      smoothBallSobolev s ⟨greenSourceCutoffError (fun x => a (p,x)) χ.1 u.1,
        contDiff_greenSourceCutoffError (ha.comp (contDiff_const.prodMk contDiff_id)) χ.2 u.2⟩ := by
  apply Wkp.ext s
  apply Lp.ext
  unfold greenCutoffOperatorFamily
  refine (firstOrderBallL_smooth_value s _ _ u).trans ?_
  refine (Filter.EventuallyEq.of_eq <| funext fun z => ?_).trans (value_smoothBallSobolev_ae _ _).symm
  have hCut := greenSourceCutoffError_firstOrder a χ.1 u.1 p z
  refine Eq.trans ?_ hCut.symm
  congr 1

end CalderonPaper.LowerGreen

end

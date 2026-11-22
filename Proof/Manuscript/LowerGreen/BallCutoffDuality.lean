module

public import Proof.Manuscript.LowerGreen.BallCutoffChains
public import Proof.Manuscript.LowerGreen.BallCutoffAdjoint
public import Proof.Manuscript.LowerGreen.BallCenterEvaluation

import Proof.Manuscript.LowerGreen.StrongBallInverseAdjoint
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 1900000

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n) {p : P} (hp : p ∈ F.V)
variable (χ : SmoothData n) (hχ : HasCompactSupport χ.1)

@[expose] def commutatorData (u : SmoothData n) (p : P) : SmoothData n :=
  ⟨greenSourceCutoffError (fun z => F.a (p,z)) χ.1 u.1,
    contDiff_greenSourceCutoffError (F.smooth.comp (contDiff_const.prodMk contDiff_id)) χ.2 u.2⟩

theorem commutatorL_on_smooth (u : SmoothData n) (s : ℕ) :
    F.commutatorL s χ hχ p (smoothBallSobolev (s+1) u) =
      smoothBallSobolev s (F.commutatorData χ u p) :=
  greenCutoffOperatorFamily_smooth s F.a F.smooth χ hχ p u

include hp in
theorem inverseL_smooth_representative (f : SmoothData n) :
    ∃ w : SmoothData n, EqOn w.1 0 (standardSphere n) ∧
      EqOn (negativeBallDivergence (fun z => F.a (p,z)) w.1) f.1 (ball (0 : X n) 1) ∧
      ∀ s, F.inverseL s p (smoothBallSobolev s f) = smoothBallSobolev (s+2) w :=
  exists_classical_fullStrongBallInverseL_family F.a F.smooth F.K F.compact F.support p
    (F.elliptic p hp) f

private theorem smoothBallSobolev_neg (s : ℕ) (f : SmoothData n) :
    smoothBallSobolev s ⟨fun z => -f.1 z,f.2.neg⟩ = -smoothBallSobolev s f := by
  let u : smoothBallDataSubmodule n := ⟨f.1,f.2⟩
  exact (smoothBallSobolevLinear n s).map_neg u

include hp in
theorem backwardL_smooth_representative (u : SmoothData n) :
    ∃ w : SmoothData n, ∀ s, F.backwardL s χ hχ p (smoothBallSobolev s u) =
      smoothBallSobolev (s+1) w := by
  obtain ⟨v,_,_,hv⟩ := F.inverseL_smooth_representative hp u
  let f := F.commutatorData χ v p
  refine ⟨⟨fun z => -f.1 z,f.2.neg⟩,fun s => ?_⟩
  rw [backwardL,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,hv,
    F.commutatorL_on_smooth χ hχ v (s+1),smoothBallSobolev_neg]

theorem inner_smoothBallSobolev (s t : ℕ) (u v : SmoothData n) :
    ⟪Wkp.value s (smoothBallSobolev s u),Wkp.value t (smoothBallSobolev t v)⟫_ℝ =
      ∫ z in ball (0 : X n) 1, u.1 z * v.1 z := by
  rw [L2.inner_def]
  change (∫ z, ⟪Wkp.value s (smoothBallSobolev s u) z,Wkp.value t (smoothBallSobolev t v) z⟫_ℝ
    ∂volume.restrict (fixedBallOpens n)) = _
  apply integral_congr_ae
  filter_upwards [value_smoothBallSobolev_ae s u,value_smoothBallSobolev_ae t v] with z hu hv
  simp [hu,hv,Real.inner_apply,mul_comm]

include hp in
/-- The equality of the forward and transposed pairings is independent
of the Sobolev orders used to represent the smooth arguments. -/
theorem inner_forwardL_backwardL_on_smooth
    (hSupp : tsupport χ.1 ⊆ ball (0 : X n) (1/2)) (s t : ℕ) (v u : SmoothData n) :
    ⟪Wkp.value t (smoothBallSobolev t v),
      Wkp.value (s+2) (F.forwardL s χ hχ p (smoothBallSobolev (s+1) u))⟫_ℝ =
    ⟪Wkp.value (t+1) (F.backwardL t χ hχ p (smoothBallSobolev t v)),
      Wkp.value (s+1) (smoothBallSobolev (s+1) u)⟫_ℝ := by
  obtain ⟨U,_,_,hU⟩ := F.inverseL_smooth_representative hp (F.commutatorData χ u p)
  obtain ⟨V,_,_,hV⟩ := F.inverseL_smooth_representative hp v
  have hF (s : ℕ) : F.forwardL s χ hχ p (smoothBallSobolev (s+1) u) =
      smoothBallSobolev (s+2) U := by
    rw [forwardL,ContinuousLinearMap.comp_apply,F.commutatorL_on_smooth χ hχ u s,hU]
  let Q := F.commutatorData χ V p
  have hB : F.backwardL t χ hχ p (smoothBallSobolev t v) = -smoothBallSobolev (t+1) Q := by
    rw [backwardL,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,hV,
      F.commutatorL_on_smooth χ hχ V (t+1)]
  have hAway := integral_greenCutoffError_skew
    (F.smooth.comp (contDiff_const.prodMk contDiff_id))
    (fun z hz i j => (F.symmetry p hp z hz).apply j i) χ u V hSupp
  let A := commonSupportMatrixFamily 2 F.a F.smooth F.K F.compact F.support p
  have hA : coefficientMatrixField 2 A = fun z => F.a (p,z) :=
    coefficientMatrixField_commonSupportMatrixFamily _ F.a F.smooth F.K F.compact F.support p
  have hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n))
      (coefficientMatrixField 2 A) (F.lo p) (F.hi p) := by rw [hA]; exact F.elliptic p hp
  have hSym z (hz : z ∈ (fixedBallOpens n : Set (X n))) :
      (coefficientMatrixField 2 A z).IsSymm := by rw [hA]; exact F.symmetry p hp z hz
  have hSymInv := fullStrongBallInverseL_zero_inner A hEll hSym
    (smoothBallSobolev 0 v) (smoothBallSobolev 0 (F.commutatorData χ u p))
  change ⟪Wkp.value 2 (F.inverseL 0 p (smoothBallSobolev 0 v)),_⟫_ℝ =
    ⟪_,Wkp.value 2 (F.inverseL 0 p (smoothBallSobolev 0 (F.commutatorData χ u p)))⟫_ℝ at hSymInv
  rw [hV,hU,← Wkp.value_zero (smoothBallSobolev 0 v),
    ← Wkp.value_zero (smoothBallSobolev 0 (F.commutatorData χ u p)),
    inner_smoothBallSobolev,inner_smoothBallSobolev] at hSymInv
  have hnQ : Wkp.value (t+1) (-smoothBallSobolev (t+1) Q) =
      -Wkp.value (t+1) (smoothBallSobolev (t+1) Q) :=
    (Wkp.valueL (t+1)).map_neg _
  rw [hF,hB,hnQ,inner_neg_left,inner_smoothBallSobolev,inner_smoothBallSobolev,← hSymInv]
  exact hAway.trans (congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall
    (fun z => mul_comm (u.1 z) (Q.1 z)))))

end SupportedBallFamily

end CalderonPaper.LowerGreen

end

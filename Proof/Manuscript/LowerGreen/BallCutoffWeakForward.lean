module

public import Proof.Manuscript.LowerGreen.BallCutoffForward
public import Proof.Manuscript.LowerGreen.WeakBallClassicalProjection
public import Proof.Manuscript.LowerGreen.WeakBallCutoffForcing

import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency true

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n) {p : P} (hp : p ∈ F.V)

@[expose] def weakForwardL (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    FixedBallL2 n →L[ℝ] FixedBallH1 n :=
  (fixedBallWeakInverseL F.a F.smooth p).comp (weakGreenCutoffFamily F.a F.smooth χ hχ p)

theorem contDiffOn_weakForwardL (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiffOn ℝ ∞ (F.weakForwardL χ hχ) F.V :=
  (contDiffOn_fixedBallWeakInverseL F.a F.smooth F.K F.compact F.support F.elliptic).clm_comp
    (contDiff_weakGreenCutoffFamily F.a F.smooth χ hχ).contDiffOn

include hp in
theorem weakForwardL_apply_localized
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (hSupp : tsupport χ.1 ⊆ ball (0 : X n) (1/2))
    (u v : SmoothData n)
    (hu : EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1))
    (hv : ∀ z ∈ tsupport χ.1, v.1 =ᶠ[𝓝 z] u.1) :
    F.weakForwardL χ hχ p (smoothBallSobolev 0 v) =
      smoothBallSobolev 1 (cutoffData χ u) := by
  let a := F.a
  have haP : ContDiff ℝ ∞ (fun z => a (p,z)) := F.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hSym (z : X n) (hz : z ∈ ball (0 : X n) 1) (i j : I n) :
      a (p,z) i j = a (p,z) j i := (F.symmetry p hp z hz).apply j i
  let f : SmoothData n := ⟨greenSourceCutoffError (fun z => a (p,z)) χ.1 v.1,
    contDiff_greenSourceCutoffError haP χ.2 v.2⟩
  let w := cutoffData χ u
  have hw : EqOn w.1 0 (standardSphere n) := by
    intro z hz
    have hn : ¬ z ∈ tsupport χ.1 := by
      intro ht
      have hb := mem_ball_zero_iff.mp (hSupp ht)
      rw [mem_sphere_zero_iff_norm.mp hz] at hb
      norm_num at hb
    change χ.1 z * u.1 z = 0
    have hz₀ : χ.1 z = 0 := (notMem_tsupport_iff_eventuallyEq.mp hn).eq_of_nhds
    rw [hz₀,zero_mul]
  have hEq : EqOn (negativeBallDivergence (fun z => a (p,z)) w.1) f.1 (ball (0 : X n) 1) := by
    intro z hz
    change negativeBallDivergence (fun x => a (p,x)) (fun x => χ.1 x * u.1 x) z =
      greenSourceCutoffError (fun x => a (p,x)) χ.1 v.1 z
    have hu₀ : negativeBallDivergence (fun x => a (p,x)) u.1 z = 0 := hu hz
    rw [negativeBallDivergence_mul_eq_at_symm haP χ.2 u.2 z (hSym z hz),hu₀,mul_zero,zero_add,
      greenSourceCutoffError_congr_germ_input _ _ _ _ hv]
  change fixedBallWeakInverseL F.a F.smooth p
    (weakGreenCutoffFamily F.a F.smooth χ hχ p (smoothBallSobolev 0 v)) = _
  rw [← Wkp.value_zero (smoothBallSobolev 0 v), weakGreenCutoffFamily_apply_smooth F.a F.smooth χ hχ p hSym v]
  exact fixedBallWeakInverseL_of_classical F.a F.smooth F.K F.compact F.support p (F.elliptic p hp)
    f w hw hEq

end SupportedBallFamily

end CalderonPaper.LowerGreen

end

module

public import Proof.Manuscript.LowerGreen.ClosedBallConormal
public import Proof.Manuscript.LowerGreen.ClosedBallOperatorLift
public import Proof.Manuscript.LowerGreen.BallCutoffDuality

import Proof.CalderonN.NormalFluxDensity
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

namespace SupportedBallFamily

variable (F : SupportedBallFamily P n) {p : P}

theorem inverseL_mem_closed (hp : p ∈ F.V) {s : ℕ} (v : ClosedBallSobolev n s) :
    F.inverseL s p v.1 ∈ closedBallSobolev n (s+2) :=
  maps_closedBallSobolev_of_smooth _ (fun f => by
    obtain ⟨g,_,_,hg⟩ := F.inverseL_smooth_representative hp f
    exact ⟨g,hg s⟩) v

@[expose] def inverseOnClosedL (hp : p ∈ F.V) (s : ℕ) :
    ClosedBallSobolev n s →L[ℝ] ClosedBallSobolev n (s+2) :=
  ((F.inverseL s p).comp (closedBallSobolev n s).toSubmodule.subtypeL).codRestrict
    (closedBallSobolev n (s+2)).toSubmodule (F.inverseL_mem_closed hp)

set_option maxHeartbeats 2300000 in
theorem inverseOnClosedL_boundaryPairing (hp : p ∈ F.V) (s : ℕ) (hs : 1+n+1 ≤ s+2)
    (v : ClosedBallSobolev n s) (u : SmoothData n)
    (hu : EqOn (negativeBallDivergence (fun z => F.a (p,z)) u.1) 0 (ball (0 : X n) 1)) :
    -(∫ w : ↥(standardSphere n), closedBallConormal (fun z => F.a (p,z)) (s+2)
      (F.inverseOnClosedL hp s v) w * u.1 w ∂(chartSurfaceMeasure n)) =
      ⟪Wkp.value s v.1,smoothBallSobolev 0 u⟫_ℝ := by
  let a := fun z => F.a (p,z)
  let A := F.inverseOnClosedL hp s
  have ha : ContDiff ℝ ∞ a := F.smooth.comp (contDiff_const.prodMk contDiff_id)
  refine (denseRange_denseSmoothBallSobolev n s).induction_on v ?_ ?_
  · apply isClosed_eq
    · exact ((continuous_integral_closedBallConormal a ha.continuous (s+2) u).comp A.continuous).neg
    · exact ((Wkp.valueL s).continuous.comp continuous_subtype_val).inner continuous_const
  · intro f
    obtain ⟨w,hw,hEq,hwRep⟩ := F.inverseL_smooth_representative hp ⟨f.1,f.2⟩
    let w' : smoothBallDataSubmodule n := ⟨w.1,w.2⟩
    have hW : F.inverseOnClosedL hp s (denseSmoothBallSobolev n s f) =
        denseSmoothBallSobolev n (s+2) w' := Subtype.ext (hwRep s)
    rw [hW]
    have hCon : closedBallConormal (fun z => F.a (p,z)) (s+2)
        (denseSmoothBallSobolev n (s+2) w') =
        fun z : ↥(standardSphere n) => smoothBallConormal a w.1 z :=
      funext (closedBallConormal_smooth a (s+2) hs w')
    rw [hCon]
    have hVal : Wkp.value s (denseSmoothBallSobolev n s f).1 =
        Wkp.value s (smoothBallSobolev s ⟨f.1,f.2⟩) := rfl
    rw [hVal,← Wkp.value_zero (smoothBallSobolev 0 u),inner_smoothBallSobolev]
    have hG := integral_sub_ballGreenFlux ha (fun z hz i j => (F.symmetry p hp z hz).apply j i) w u
    have hLeft :
        (∫ z in ball (0 : X n) 1, u.1 z * negativeBallDivergence a w.1 z -
          w.1 z * negativeBallDivergence a u.1 z) =
        ∫ z in ball (0 : X n) 1, f.1 z * u.1 z := by
      apply setIntegral_congr_fun isOpen_ball.measurableSet
      intro z hz
      have hu₀ : negativeBallDivergence a u.1 z = 0 := hu hz
      change u.1 z * negativeBallDivergence a w.1 z -
        w.1 z * negativeBallDivergence a u.1 z = f.1 z * u.1 z
      have he : negativeBallDivergence a w.1 z = f.1 z := hEq hz
      rw [he,hu₀,mul_zero,sub_zero,mul_comm]
    have hRight : unitSphereFlux (fun z => w.1 z • smoothBallFlux a u.1 z -
        u.1 z • smoothBallFlux a w.1 z) =
      -(∫ z : ↥(standardSphere n), smoothBallConormal a w.1 z * u.1 z ∂(chartSurfaceMeasure n)) := by
      unfold unitSphereFlux
      rw [show -(∫ z : ↥(standardSphere n), smoothBallConormal a w.1 z * u.1 z
          ∂(chartSurfaceMeasure n)) =
          ∫ z : ↥(sphere (0 : X n) 1), -(smoothBallConormal a w.1 z * u.1 z)
          ∂(chartSurfaceMeasure n) from (integral_neg _).symm]
      apply integral_congr_ae
      filter_upwards with z
      have hTrace : w.1 z = 0 := hw z.property
      simp [hTrace,smoothBallConormal,inner_smul_right,mul_comm]
    rw [hLeft,hRight] at hG
    exact hG.symm

end SupportedBallFamily

end CalderonPaper.LowerGreen

end

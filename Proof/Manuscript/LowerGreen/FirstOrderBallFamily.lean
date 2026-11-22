module

public import Proof.CalderonN.BallPoissonOperator
public import Proof.CalderonN.BallRegularity.SmoothCommonSupportStrongOperator

import Mathlib.Tactic

public section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology
open CalderonN CalderonN.BallDirichlet TauCeti

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

noncomputable section

/-- A family of first-order operators with a shared compact coefficient
support. The construction loses exactly one fixed-ball Sobolev order. -/
def firstOrderBallL (s : ℕ)
    (b : (i : I n) → SmoothCoefficientJets n (s+1))
    (c : SmoothCoefficientJets n (s+1)) :
    BallSobolev n (s+1) →L[ℝ] BallSobolev n s :=
  (∑ i, (coefficientMultiplier fixedSobolevCalculus s (b i)).comp
    (unitBallCoordinateDerivativeL fixedSobolevCalculus s i)) +
    (coefficientMultiplier fixedSobolevCalculus s c).comp (Wkp.lowerOrderL s)

omit [Nontrivial (Fin n)] in
theorem contDiff_firstOrderBallL_family (s : ℕ)
    (b : I n → P × X n → ℝ) (c : P × X n → ℝ)
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hc : ContDiff ℝ ∞ c)
    (K : Set (X n)) (hK : IsCompact K)
    (hbK : ∀ i p z, z ∉ K → b i (p,z) = 0)
    (hcK : ∀ p z, z ∉ K → c (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => firstOrderBallL s
      (fun i => commonSupportCoefficientFamily (s+1) (b i) (hb i) K hK (hbK i) p)
      (commonSupportCoefficientFamily (s+1) c hc K hK hcK p)) := by
  unfold firstOrderBallL
  refine (ContDiff.sum (fun i _ => ?_)).add ?_
  · exact (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus s
      (b i) (hb i) K hK (hbK i)).clm_comp contDiff_const
  · exact (contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus s
      c hc K hK hcK).clm_comp contDiff_const

omit [Nontrivial (Fin n)] in
private theorem coefficientMultiplier_on_smooth (s : ℕ) (d : SmoothCoefficientJets n (s+1))
    (f : SmoothData n) :
    (Wkp.value s (coefficientMultiplier fixedSobolevCalculus s d (smoothBallSobolev s f)))
      =ᵐ[volume.restrict (fixedBallOpens n)] fun x => coefficientValue (s+1) d x * f.1 x := by
  exact (coefficientMultiplier_value_ae fixedSobolevCalculus s d (smoothBallSobolev s f)).trans
    ((EventuallyEq.rfl (f := coefficientValue (s+1) d)).mul (value_smoothBallSobolev_ae s f))

theorem firstOrderBallL_smooth_value (s : ℕ)
    (b : I n → SmoothCoefficientJets n (s+1)) (c : SmoothCoefficientJets n (s+1)) (u : SmoothData n) :
    (Wkp.value s (firstOrderBallL s b c (smoothBallSobolev (s+1) u)))
      =ᵐ[volume.restrict (fixedBallOpens n)] fun x =>
        (∑ i, coefficientValue (s+1) (b i) x * coordDeriv i u.1 x) +
          coefficientValue (s+1) c x * u.1 x := by
  let w := smoothBallSobolev (s+1) u
  let v (i : I n) := coefficientMultiplier fixedSobolevCalculus s (b i)
    (unitBallCoordinateDerivativeL fixedSobolevCalculus s i w)
  let q := coefficientMultiplier fixedSobolevCalculus s c (Wkp.lowerOrderL s w)
  have hv (i : I n) : (Wkp.value s (v i)) =ᵐ[volume.restrict (fixedBallOpens n)]
      fun x => coefficientValue (s+1) (b i) x * coordDeriv i u.1 x := by
    change (Wkp.value s (coefficientMultiplier fixedSobolevCalculus s (b i)
      (unitBallCoordinateDerivativeL fixedSobolevCalculus s i (smoothBallSobolev (s+1) u))))
      =ᵐ[volume.restrict (fixedBallOpens n)] _
    rw [unitBallCoordinateDerivativeL_smooth]
    exact coefficientMultiplier_on_smooth s (b i) _
  have hq : (Wkp.value s q) =ᵐ[volume.restrict (fixedBallOpens n)]
      fun x => coefficientValue (s+1) c x * u.1 x := by
    change (Wkp.value s (coefficientMultiplier fixedSobolevCalculus s c
      (Wkp.lowerOrder s (smoothBallSobolev (s+1) u)))) =ᵐ[volume.restrict (fixedBallOpens n)] _
    rw [lowerOrder_smoothBallSobolev]
    exact coefficientMultiplier_on_smooth s c u
  have hAction : firstOrderBallL s b c w = (∑ i, v i) + q := by
    simp only [firstOrderBallL,add_apply,sum_apply,
      ContinuousLinearMap.comp_apply,v,q]
  rw [hAction]
  change (Wkp.valueL (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n) (p := 2) s
    ((∑ i, v i) + q)) =ᵐ[volume.restrict (fixedBallOpens n)] _
  rw [map_add,map_sum]
  refine (Lp.coeFn_add _ _).trans (((Lp.coeFn_finsetSum _ _).trans ?_).add hq)
  filter_upwards [Filter.eventually_all.2 hv] with x hx
  simp only [Finset.sum_apply,Wkp.valueL_apply]
  exact Finset.sum_congr rfl (fun i _ => hx i)

end

end CalderonPaper.LowerGreen

module

public import Proof.CalderonN.BallRegularity.CoefficientJetSpace
public import Proof.CalderonN.BallRegularity.FixedCalculus

/-! From Proof/Archive/CoefficientMultiplier.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section

set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Function
open scoped ENNReal ContDiff
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


 
def sobolevMultiplierBound (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) : ℝ :=
  Classical.choose (hcalc.1 k)

theorem sobolevMultiplierBound_nonneg (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) :
    0 ≤ sobolevMultiplierBound hcalc k :=
  (Classical.choose_spec (hcalc.1 k)).1

theorem exists_coefficientMultiplier (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k + 1)) :
    ∃ T : (BallSobolev dim) k →L[ℝ] (BallSobolev dim) k,
      (∀ f : (BallSobolev dim) k,
        TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k (T f)
          =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
          fun x => coefficientValue (k + 1) F x * TauCeti.Wkp.value
            (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k f x) ∧
      ‖T‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ := by
  exact (Classical.choose_spec (hcalc.1 k)).2
    (coefficientValue (k + 1) F) (contDiff_coefficientValue _ F)
    (hasCompactSupport_coefficientValue _ F) ‖F‖ (norm_nonneg F)
    (fun j hj x => norm_iteratedFDeriv_coefficientValue_le _ F j hj x)

 
def coefficientMultiplier (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k + 1)) :=
  Classical.choose (exists_coefficientMultiplier hcalc k F)

theorem coefficientMultiplier_value_ae (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k + 1)) (f : (BallSobolev dim) k) :
    TauCeti.Wkp.value (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k
      (coefficientMultiplier hcalc k F f)
      =ᵐ[((volume : Measure (X dim)).restrict (fixedBallOpens dim))]
      fun x => coefficientValue (k + 1) F x * TauCeti.Wkp.value
        (mu := (volume : Measure (X dim))) (Omega := (fixedBallOpens dim)) (p := 2) k f x :=
  (Classical.choose_spec (exists_coefficientMultiplier hcalc k F)).1 f

theorem norm_coefficientMultiplier_le (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k + 1)) :
    ‖coefficientMultiplier hcalc k F‖ ≤ sobolevMultiplierBound hcalc k * ‖F‖ :=
  (Classical.choose_spec (exists_coefficientMultiplier hcalc k F)).2

theorem coefficientMultiplier_add (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F G : (SmoothCoefficientJets dim) (k + 1)) :
    coefficientMultiplier hcalc k (F + G) =
      coefficientMultiplier hcalc k F + coefficientMultiplier hcalc k G := by
  apply ContinuousLinearMap.ext
  intro f
  apply TauCeti.Wkp.ext k
  rw [add_apply, TauCeti.Wkp.value_add]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k (F + G) f,
    coefficientMultiplier_value_ae hcalc k F f,
    coefficientMultiplier_value_ae hcalc k G f,
    Lp.coeFn_add (TauCeti.Wkp.value k (coefficientMultiplier hcalc k F f))
      (TauCeti.Wkp.value k (coefficientMultiplier hcalc k G f))] with x hFG hF hG hadd
  rw [hFG, hadd]
  simp only [Pi.add_apply]
  rw [hF, hG]
  rw [coefficientValue_add]
  simp only [Pi.add_apply, add_mul]

theorem coefficientMultiplier_smul (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (c : ℝ) (F : (SmoothCoefficientJets dim) (k + 1)) :
    coefficientMultiplier hcalc k (c • F) = c • coefficientMultiplier hcalc k F := by
  apply ContinuousLinearMap.ext
  intro f
  apply TauCeti.Wkp.ext k
  rw [smul_apply, TauCeti.Wkp.value_smul]
  apply Lp.ext
  filter_upwards [coefficientMultiplier_value_ae hcalc k (c • F) f,
    coefficientMultiplier_value_ae hcalc k F f,
    Lp.coeFn_smul c (TauCeti.Wkp.value k (coefficientMultiplier hcalc k F f))]
      with x hcF hF hsmul
  rw [hcF, hsmul]
  simp only [Pi.smul_apply]
  rw [hF, coefficientValue_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

 
def coefficientMultiplierLinearMap (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) :
    (SmoothCoefficientJets dim) (k + 1) →ₗ[ℝ] (BallSobolev dim) k →L[ℝ] (BallSobolev dim) k where
  toFun := coefficientMultiplier hcalc k
  map_add' := coefficientMultiplier_add hcalc k
  map_smul' := coefficientMultiplier_smul hcalc k

 
def coefficientMultiplierL (hcalc : (FixedSobolevCalculus dim)) (k : ℕ) :=
  (coefficientMultiplierLinearMap hcalc k).mkContinuous (sobolevMultiplierBound hcalc k)
    (norm_coefficientMultiplier_le hcalc k)

theorem coefficientMultiplierL_apply (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : (SmoothCoefficientJets dim) (k + 1)) :
    coefficientMultiplierL hcalc k F = coefficientMultiplier hcalc k F := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffOn_coefficientMultiplier {n : WithTop ℕ∞}
    (hcalc : (FixedSobolevCalculus dim)) (k : ℕ)
    (F : E → (SmoothCoefficientJets dim) (k + 1)) (s : Set E)
    (hF : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun x => coefficientMultiplierL hcalc k (F x)) s :=
  (coefficientMultiplierL hcalc k).contDiff.comp_contDiffOn hF

end CalderonN.BallDirichlet

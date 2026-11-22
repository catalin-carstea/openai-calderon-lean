module

public import Proof.CalderonN.ActualRelativeCoefficientGerms
public import Proof.CalderonN.FixedBallSmoothEnergy
public import Proof.CalderonN.CommonSupportZeroMultiplierHigherJets

import Proof.CalderonN.BallRegularity.CoordinateFluxEnergy
import Proof.CalderonN.ParameterSpatialJetBounds
import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Tactic

/-! The smooth physical weak energy depends on the zeroth coefficient
jet alone. Its mixed parameter bounds therefore retain both radius
factors in the actual relative coefficient remainder. -/

public section

noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet ShrinkingSpheres
variable {dim : ℕ} [NeZero dim]

abbrev FixedBallL2 (dim : ℕ) := Lp ℝ 2 ((volume : Measure (X dim)).restrict (fixedBallOpens dim))

@[expose] def fixedBallWeakEnergyTermL (i j : I dim) :
    (FixedBallL2 dim →L[ℝ] FixedBallL2 dim) →L[ℝ]
      (FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ) :=
  let R := ((ContinuousLinearMap.compL ℝ (FixedBallH1 dim) (FixedBallL2 dim) ℝ).flip
    (unitBallCoordinateGradientL i)).comp (innerSL ℝ)
  (ContinuousLinearMap.compL ℝ (FixedBallH1 dim) (FixedBallL2 dim) (FixedBallH1 dim →L[ℝ] ℝ) R).comp
    ((ContinuousLinearMap.compL ℝ (FixedBallH1 dim) (FixedBallL2 dim) (FixedBallL2 dim)).flip
      (unitBallCoordinateGradientL j))

@[expose] def fixedBallWeakEnergyJetBudget (dim : ℕ) [NeZero dim] : ℝ :=
  ∑ i : I dim,∑ j : I dim, ‖fixedBallWeakEnergyTermL i j‖

private theorem fixedBallWeakEnergyTermL_apply (i j : I dim)
    (M : FixedBallL2 dim →L[ℝ] FixedBallL2 dim) (u v : FixedBallH1 dim) :
    fixedBallWeakEnergyTermL i j M u v =
      ⟪M (unitBallCoordinateGradientL j u),unitBallCoordinateGradientL i v⟫_ℝ := by
  simp only [fixedBallWeakEnergyTermL,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,innerSL_apply_apply]

theorem commonSupport_fixedBallSmoothEnergy_formula
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (J : Set (X dim)) (hJ : IsCompact J) (hSupp : ∀ p z,z ∉ J → a (p,z) = 0) (p : P) :
    let G := commonSupportMatrixFamily 1 a ha J hJ hSupp p
    fixedBallSmoothEnergyL (ha.continuous.comp (continuous_const.prodMk continuous_id) :
      Continuous (fun z => a (p,z))) =
      ∑ i : I dim,∑ j : I dim,fixedBallWeakEnergyTermL i j (coefficientMultiplier fixedSobolevCalculus 0 (G i j)) := by
  dsimp only
  let G := commonSupportMatrixFamily 1 a ha J hJ hSupp p
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  simp only [fixedBallSmoothEnergyL_apply,ContinuousLinearMap.sum_apply,fixedBallWeakEnergyTermL_apply]
  let q (i j : I dim) : FixedBallL2 dim :=
    coefficientMultiplier fixedSobolevCalculus 0 (G i j) (unitBallCoordinateGradientL j u)
  have hq (i j : I dim) : q i j =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      fun x => a (p,x) i j*(TauCeti.W1p.gradient u x) j := by
    have hM := coefficientMultiplier_value_ae fixedSobolevCalculus 0 (G i j) (unitBallCoordinateGradientL j u)
    simp only [TauCeti.Wkp.value_zero] at hM
    have hE : ∀ z, coefficientValue 1 (G i j) z = a (p,z) i j := by
      intro z
      have h := congrFun (coefficientMatrixField_commonSupportMatrixFamily 1 a ha J hJ hSupp p) z
      exact congrArg (fun M : Mat dim => M i j) h
    filter_upwards [hM,unitBallCoordinateGradientL_ae j u] with z h₁ h₂
    change q i j z = _
    rw [h₁,hE,h₂]
  exact energyFormH1_eq_sum_coordinateFlux_inner (fun z => a (p,z)) u v q hq

theorem local_fixedBallWeakEnergy_jet_budget
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (a : P × X dim → Mat dim) (ha : ContDiff ℝ ∞ a)
    (J : Set (X dim)) (hJ : IsCompact J) (hSupp : ∀ p z,z ∉ J → a (p,z) = 0)
    (p : P) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ z ∈ closedBall (0:X dim) 1, LocalSmoothJetBudget a (p,z) N C) :
    LocalSmoothJetBudget (fun t => fixedBallSmoothEnergyL
      (ha.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun z => a (t,z))))
      p N (fixedBallWeakEnergyJetBudget dim*C) := by
  let G := commonSupportMatrixFamily 1 a ha J hJ hSupp
  let L (i j : I dim) := matrixEntryL i j
  let U (i j : I dim) (t : P) := coefficientMultiplier fixedSobolevCalculus 0 (G t i j)
  have hL (i j : I dim) : ‖L i j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    rw [one_mul,matrixEntryL_apply]
    exact Matrix.norm_entry_le_entrywise_sup_norm A (i:=i) (j:=j)
  have hEntry (i j : I dim) : ContDiff ℝ ∞ (fun q => a q i j) := (L i j).contDiff.comp ha
  have hU (i j : I dim) : LocalSmoothJetBudget (U i j) p N C := by
    have hF := contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0
      (fun q => a q i j) (hEntry i j) J hJ (fun p z hz => by rw [hSupp p z hz];rfl)
    refine ⟨hF.contDiffAt,fun n hn => ?_⟩
    apply norm_iteratedFDeriv_commonSupport_coefficientMultiplier_zero_le fixedSobolevCalculus
      (fun q => a q i j) (hEntry i j) J hJ (fun p z hz => by rw [hSupp p z hz];rfl) p n C hC
    intro z hz
    have hLoc := ((h z (ball_subset_closedBall hz)).linear_postcomp (L i j)).enlarge
      (mul_le_of_le_one_left hC (hL i j))
    have hMix := norm_iteratedFDeriv_parameter_spatial_jet_le (L i j ∘ a) (hEntry i j) p z n 0
    exact hMix.trans (hLoc.bound _ (by omega))
  have hData (i j : I dim) :=
    (hU i j).linear_postcomp (fixedBallWeakEnergyTermL i j)
  have hSum := LocalSmoothJetBudget.finite_sum Finset.univ
    (fun (i : I dim) t => ∑ j : I dim, (fixedBallWeakEnergyTermL i j) (U i j t))
    (fun i => ∑ j : I dim,‖fixedBallWeakEnergyTermL i j‖*C)
    (fun i _ => LocalSmoothJetBudget.finite_sum Finset.univ
      (fun j => (fixedBallWeakEnergyTermL i j) ∘ U i j)
      (fun j => ‖fixedBallWeakEnergyTermL i j‖*C) (fun j _ => hData i j))
  have hEq : (fun t => fixedBallSmoothEnergyL
      (ha.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun z => a (t,z)))) =
      fun t => ∑ i : I dim,∑ j : I dim,fixedBallWeakEnergyTermL i j (U i j t) :=
    funext (commonSupport_fixedBallSmoothEnergy_formula a ha J hJ hSupp)
  rw [hEq]
  simpa only [fixedBallWeakEnergyJetBudget,Finset.sum_mul] using hSum

end CalderonN

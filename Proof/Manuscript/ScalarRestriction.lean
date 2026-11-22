module

public import Proof.Manuscript.ScalarSolutionSpace
public import Proof.Manuscript.ClosedCrossSeries
public import Proof.CalderonN.CrossRestrictionSpectrum

import Proof.CalderonN.HarmonicTaylorApproximation
import Proof.CalderonN.InteriorJetCutoff
import Mathlib.Tactic

public section

open Set Metric Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

@[expose] def smallAuxiliaryBall : Set (X 3) := ball 0 (1/2)

theorem smallAuxiliaryBall_subset : smallAuxiliaryBall ⊆ auxiliaryBall :=
  ball_subset_ball (by norm_num)

@[expose] def augmentedObservation (S : Set (X n)) : Set (X (n+3)) :=
  splitAux ⁻¹' (S ×ˢ smallAuxiliaryBall)

theorem augmentedObservation_subset {S D : Set (X n)} (hSD : S ⊆ D) :
    augmentedObservation S ⊆ augmentedDomain D :=
  preimage_mono (prod_mono hSD smallAuxiliaryBall_subset)

theorem augmentedObservation_measurable {S : Set (X n)} (hS : MeasurableSet S) :
    MeasurableSet (augmentedObservation S) :=
  (hS.prod measurableSet_ball).preimage splitAux.continuous.measurable

theorem augmentedObservation_compactBuffer {S K D : Set (X n)} (hK : IsCompact K)
    (hSK : S ⊆ K) (hKD : K ⊆ D) :
    ∃ C : Set (X (n+3)), IsCompact C ∧ augmentedObservation S ⊆ C ∧ C ⊆ augmentedDomain D := by
  let P := K ×ˢ closedBall (0 : X 3) (1/2)
  let C := splitAux.symm '' P
  refine ⟨C,(hK.prod (isCompact_closedBall _ _)).image splitAux.symm.continuous,?_,?_⟩
  · intro z hz
    exact ⟨splitAux z, ⟨hSK hz.1,ball_subset_closedBall hz.2⟩,splitAux.symm_apply_apply z⟩
  · rintro z ⟨q,hq,rfl⟩
    change splitAux (splitAux.symm q) ∈ D ×ˢ auxiliaryBall
    rw [splitAux.apply_symm_apply]
    exact ⟨hKD hq.1, closedBall_subset_ball (by norm_num) hq.2⟩

def observedAuxProfile : ChartL2 smallAuxiliaryBall :=
  restrictL2 (Measure.restrict_mono_set volume smallAuxiliaryBall_subset) auxProfileLp

theorem observedAuxProfile_ae :
    (observedAuxProfile : X 3 → ℝ) =ᵐ[volume.restrict smallAuxiliaryBall] auxProfile :=
  (restrictL2_ae _ _).trans
    (ae_mono (Measure.restrict_mono_set volume smallAuxiliaryBall_subset) auxProfileLp_ae)

theorem norm_observedAuxProfile_pos : 0 < ‖observedAuxProfile‖ := by
  by_contra! h
  have hZero := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hEq : (0 : X 3 → ℝ) =ᵐ[volume.restrict smallAuxiliaryBall] auxProfile :=
    (Lp.coeFn_zero ℝ 2 _).symm.trans (hZero ▸ observedAuxProfile_ae)
  have hPoint := Measure.eqOn_open_of_ae_eq hEq isOpen_ball continuous_const.continuousOn
    auxProfile_smooth.continuous.continuousOn
  have h0 : 0 ∈ smallAuxiliaryBall := mem_ball_self (by norm_num)
  exact (auxProfile_pos (smallAuxiliaryBall_subset h0)).ne' (hPoint h0).symm

theorem splitObserve_measurePreserving {S : Set (X n)} (hS : MeasurableSet S) :
    MeasurePreserving (splitAux (n := n)) (volume.restrict (augmentedObservation S))
      ((volume.restrict S).prod (volume.restrict smallAuxiliaryBall)) := by
  rw [Measure.prod_restrict]
  exact (splitAux_measurePreserving n).restrict_preimage (hS.prod measurableSet_ball)

@[expose] def observationJoin (z : X 3 × X n) : X (n+3) := splitAux.symm z.swap

theorem observationJoin_measurePreserving {S : Set (X n)} (hS : MeasurableSet S) :
    MeasurePreserving observationJoin ((volume.restrict smallAuxiliaryBall).prod (volume.restrict S))
      (volume.restrict (augmentedObservation S)) := by
  let e : X (n+3) ≃ᵐ X n × X 3 := splitAux.toHomeomorph.toMeasurableEquiv
  exact ((splitObserve_measurePreserving hS).symm e).comp Measure.measurePreserving_swap

/-- Pair with the same nonzero auxiliary profile after aligning Lebesgue
measures. This recovers the base restriction linearly. -/
def recoverObserved {S : Set (X n)} (hS : MeasurableSet S) :
    ChartL2 (augmentedObservation S) →L[ℝ] ChartL2 S :=
  ((‖observedAuxProfile‖^2)⁻¹ • tensorCoefficient observedAuxProfile).comp
    (Lp.compMeasurePreservingₗᵢ ℝ observationJoin (observationJoin_measurePreserving hS)).toContinuousLinearMap

theorem recoverObserved_lift {S D : Set (X n)} (hD : IsOpen D) (hS : MeasurableSet S)
    [IsFiniteMeasure ((volume : Measure (X n)).restrict S)] (hSD : S ⊆ D) (u : ChartL2 D) :
    recoverObserved hS
        (restrictL2 (Measure.restrict_mono_set volume (augmentedObservation_subset hSD)) (scalarLiftL2 hD u)) =
      restrictL2 (Measure.restrict_mono_set volume hSD) u := by
  let q := restrictL2 (Measure.restrict_mono_set volume (augmentedObservation_subset hSD)) (scalarLiftL2 hD u)
  let O := Lp.compMeasurePreserving observationJoin (observationJoin_measurePreserving hS) q
  let w := observedAuxProfile
  let p := (‖w‖^2)⁻¹
  have hq : (q : X (n+3) → ℝ) =ᵐ[volume.restrict (augmentedObservation S)] liftedFunction u :=
    (restrictL2_ae _ _).trans (ae_mono (Measure.restrict_mono_set volume (augmentedObservation_subset hSD))
      (scalarLiftL2_ae hD u))
  have hJoin (z : X 3 × X n) : splitAux (observationJoin z) = z.swap :=
    splitAux.apply_symm_apply _
  have hO : (O : X 3 × X n → ℝ) =ᵐ[
      (volume.restrict smallAuxiliaryBall).prod (volume.restrict S)] fun z => u z.2 * w z.1 := by
    have hA := (Lp.coeFn_compMeasurePreserving q (observationJoin_measurePreserving hS)).trans
      ((observationJoin_measurePreserving hS).quasiMeasurePreserving.ae_eq_comp hq)
    have hw := (Measure.quasiMeasurePreserving_fst (ν := volume.restrict S)).ae_eq_comp observedAuxProfile_ae
    filter_upwards [hA,hw] with z hz hW
    have hb : baseProjection (observationJoin z) = z.2 := congrArg Prod.fst (hJoin z)
    have ha : auxiliaryProjection (observationJoin z) = z.1 := congrArg Prod.snd (hJoin z)
    change w z.1 = auxProfile z.1 at hW
    simpa only [Function.comp_apply,liftedFunction,hb,ha,← hW] using hz
  have hSlice : ∀ᵐ y ∂(volume.restrict S), ∀ᵐ x ∂(volume.restrict smallAuxiliaryBall),
      O (x,y) = u y * w x :=
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
      (μ := volume.restrict S) (ν := volume.restrict smallAuxiliaryBall)).quasiMeasurePreserving.ae hO)
  change p • (tensorCoefficient w O) = _
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul p (tensorCoefficient w O),
    tensorCoefficient_ae_integral w O, hSlice,
    restrictL2_ae (Measure.restrict_mono_set volume hSD) u] with y hS hI hy hR
  change _ = p * tensorCoefficient w O y at hS
  rw [hS,hI,hR]
  have heq : (∫ x in smallAuxiliaryBall, w x * O (x,y)) =
      ∫ x in smallAuxiliaryBall, u y * (w x)^2 := by
    apply integral_congr_ae
    filter_upwards [hy] with x hx
    rw [hx]
    ring
  rw [heq, integral_const_mul, integral_sq_eq_norm_sq w]
  have hwpos : 0 < ‖w‖ := norm_observedAuxProfile_pos
  dsimp only [p]
  field_simp

def scalarLiftHarmonic {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D) (hL : L.SmoothOn D) :
    scalarSolutionL2 hD hL →L[ℝ] harmonicL2Space (augmentedDomain_open hD)
      (augmentedMetric_smoothOnDomain hD hL) :=
  ((scalarLiftL2 hD).comp (scalarSolutionL2 hD hL).toSubmodule.subtypeL).codRestrict _
    (scalarLiftL2_mem_harmonic hD hL)

theorem scalarLiftHarmonic_norm_le {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D)
    (hL : L.SmoothOn D) : ‖scalarLiftHarmonic hD hL‖ ≤ ‖auxProfileLp‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  change ‖scalarLiftL2 hD u.1‖ ≤ ‖auxProfileLp‖ * ‖u.1‖
  rw [norm_scalarLiftL2,mul_comm]

/-- The base scalar restriction factors through the harmonic restriction
on the observed set times the smaller auxiliary ball. -/
theorem closedRestrict_factor_augmented {L : ScalarElliptic n} {D S : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (hS : MeasurableSet S)
    [IsFiniteMeasure ((volume : Measure (X n)).restrict S)] (hSD : S ⊆ D) :
    closedRestrict (scalarSolutionL2 hD hL) hSD =
      (recoverObserved hS).comp ((harmonicRestrict (augmentedDomain_open hD)
          (augmentedMetric_smoothOnDomain hD hL) (augmentedObservation_subset hSD)).comp
        (scalarLiftHarmonic hD hL)) := by
  let hU := augmentedDomain_open hD
  let hG := augmentedMetric_smoothOnDomain hD hL
  let hSub := augmentedObservation_subset hSD
  ext1 u
  have hEq : harmonicRestrict hU hG hSub (scalarLiftHarmonic hD hL u) =
      restrictL2 (Measure.restrict_mono_set volume hSub) (scalarLiftL2 hD u.1) :=
    Lp.ext ((harmonicRestrict_ae hU hG hSub (scalarLiftHarmonic hD hL u)).trans
      (restrictL2_ae _ (scalarLiftL2 hD u.1)).symm)
  change restrictL2 (Measure.restrict_mono_set volume hSD) u.1 =
    recoverObserved hS (harmonicRestrict hU hG hSub (scalarLiftHarmonic hD hL u))
  rw [hEq, recoverObserved_lift hD hS hSD u.1]

/-- The L² factorization cost depends only on the observation set and
the auxiliary profile. -/
@[expose] def scalarRestrictionCost {S : Set (X n)} (hS : MeasurableSet S)
    [IsFiniteMeasure ((volume : Measure (X n)).restrict S)] : ℝ :=
  ‖recoverObserved hS‖ * ‖auxProfileLp‖

theorem scalarRestrictionCost_nonneg {S : Set (X n)} (hS : MeasurableSet S)
    [IsFiniteMeasure ((volume : Measure (X n)).restrict S)] : 0 ≤ scalarRestrictionCost hS := by
  unfold scalarRestrictionCost
  positivity

set_option maxHeartbeats 1600000 in
/-- Transfer an existing counted harmonic approximation through the
exact scalar factorization, multiplying the error by a fixed cost. -/
theorem counted_scalar_restriction_of_counted_harmonic {L : ScalarElliptic n}
    {D S : Set (X n)} (hD : IsOpen D) (hL : L.SmoothOn D) (hS : MeasurableSet S)
    [IsFiniteMeasure ((volume : Measure (X n)).restrict S)] (hSD : S ⊆ D)
    {s N A₀ : ℕ} {B : ℝ}
    (hA : HasRestrictionApprox (augmentedDomain_open hD) (augmentedMetric_smoothOnDomain hD hL)
      (augmentedObservation_subset hSD) s N A₀ B) :
    ∀ A : ℕ, A₀ ≤ A → ∃ P : scalarSolutionL2 hD hL →L[ℝ] ChartL2 S,
      FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * A ^ (n+3) ∧
      ‖closedRestrict (scalarSolutionL2 hD hL) hSD - P‖ * (A : ℝ)^s ≤ scalarRestrictionCost hS * max B 0 := by
  let : NeZero (n+3) := ⟨by omega⟩
  let U := augmentedDomain D
  let V := augmentedObservation S
  have hU : IsOpen U := augmentedDomain_open hD
  have hG := augmentedMetric_smoothOnDomain hD hL
  have hSub : V ⊆ U := augmentedObservation_subset hSD
  let R := harmonicRestrict hU hG hSub
  let Q := recoverObserved hS
  let T := scalarLiftHarmonic hD hL
  have hFact : closedRestrict (scalarSolutionL2 hD hL) hSD = Q.comp (R.comp T) :=
    closedRestrict_factor_augmented hD hL hS hSD
  let cost := ‖Q‖ * ‖auxProfileLp‖
  have hcost : 0 ≤ cost := by positivity
  intro A hA₀
  obtain ⟨W,hW,hWrank,hWerr⟩ := hA A hA₀
  let P := Q.comp (W.comp T)
  let jW := LinearMap.range W.toLinearMap
  have hRange : LinearMap.range P.toLinearMap ≤ jW.map Q.toLinearMap := by
    rintro _ ⟨u,rfl⟩
    exact ⟨W (T u),⟨T u,rfl⟩,rfl⟩
  let : FiniteDimensional ℝ jW := hW
  refine ⟨P, Submodule.finiteDimensional_of_le hRange, ?_, ?_⟩
  · exact (Submodule.finrank_mono hRange).trans ((Submodule.finrank_map_le _ _).trans hWrank)
  · have hDiff : closedRestrict (scalarSolutionL2 hD hL) hSD - P =
        Q.comp ((R-W).comp T) := by
      rw [hFact]
      ext1 u
      simp [P]
    have hBound : ‖Q.comp ((R-W).comp T)‖ ≤ cost * ‖R-W‖ := by
      refine (Q.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left
        ((R-W).opNorm_comp_le T) (norm_nonneg _)).trans ?_)
      have hh := mul_le_mul_of_nonneg_left (scalarLiftHarmonic_norm_le hD hL)
        (mul_nonneg (norm_nonneg Q) (norm_nonneg (R-W)))
      dsimp only [cost]
      have hT : ‖T‖ = ‖scalarLiftHarmonic hD hL‖ := rfl
      rw [hT]
      nlinarith only [hh]
    rw [hDiff]
    refine (mul_le_mul_of_nonneg_right hBound (by positivity)).trans ?_
    change cost * ‖R-W‖ * _ ≤ cost * max B 0
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hWerr.trans (le_max_left _ _)) hcost

set_option maxHeartbeats 1600000 in
/-- Transferring the released harmonic Taylor approximants through the
factorization yields finite-rank approximants for scalar restriction.
The larger dimension affects only the count of ranks. -/
theorem exists_counted_scalar_restriction {L : ScalarElliptic n} {D S K : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (hS : MeasurableSet S) (hK : IsCompact K)
    (hSK : S ⊆ K) (hKD : K ⊆ D) (s : ℕ) :
    ∃ (B : ℝ) (N A₀ : ℕ), 0 ≤ B ∧ ∀ A : ℕ, A₀ ≤ A →
      ∃ P : scalarSolutionL2 hD hL →L[ℝ] ChartL2 S,
        FiniteDimensional ℝ (LinearMap.range P.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range P.toLinearMap) ≤ N * A ^ (n+3) ∧
        ‖closedRestrict (scalarSolutionL2 hD hL) (hSK.trans hKD) - P‖ * (A : ℝ)^s ≤ B := by
  let : NeZero (n+3) := ⟨by omega⟩
  let : IsFiniteMeasure ((volume : Measure (X n)).restrict S) :=
    isFiniteMeasure_restrict.mpr ((measure_mono hSK).trans_lt hK.measure_lt_top).ne
  let U := augmentedDomain D
  let V := augmentedObservation S
  have hU : IsOpen U := augmentedDomain_open hD
  have hG := augmentedMetric_smoothOnDomain hD hL
  have hV : MeasurableSet V := augmentedObservation_measurable hS
  obtain ⟨J,hJ,hVJ,hJU⟩ := augmentedObservation_compactBuffer hK hSK hKD
  obtain ⟨B,N,A₀,hA⟩ := exists_counted_harmonic_restrictionApprox hU hG
    (harmonicInteriorJets_of_smoothMetric hU hG) hV hJ hVJ hJU s
  exact ⟨scalarRestrictionCost hS * max B 0,N,A₀,
    mul_nonneg (scalarRestrictionCost_nonneg hS) (le_max_right _ _),
    counted_scalar_restriction_of_counted_harmonic hD hL hS (hSK.trans hKD) hA⟩

end CalderonPaper.ScalarElliptic

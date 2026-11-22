module

public import Proof.Manuscript.ScalarHarmonicLift
public import Proof.CalderonN.HarmonicL2Space
public import Proof.CalderonN.CrossTensor

import Proof.CalderonN.ChartUniqueContinuation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Real.Pi.Bounds
import Proof.CalderonN.GreenWeak
import Mathlib.Tactic

public section

open Set Metric Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff ENNReal Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

@[expose] def auxiliaryBall : Set (X 3) := ball 0 1

@[expose] def augmentedDomain (D : Set (X n)) : Set (X (n+3)) :=
  splitAux ⁻¹' (D ×ˢ auxiliaryBall)

theorem augmentedDomain_open {D : Set (X n)} (hD : IsOpen D) : IsOpen (augmentedDomain D) :=
  (hD.prod isOpen_ball).preimage splitAux.continuous

theorem auxProfile_pos {w : X 3} (hw : w ∈ auxiliaryBall) : 0 < auxProfile w := by
  have hcoord : |w 1| ≤ ‖w‖ := (Real.norm_eq_abs (w 1)) ▸ PiLp.norm_apply_le w 1
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hAbs := abs_lt.mp (hcoord.trans_lt hw')
  have hcos : 0 < Real.cos (w 1) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_gt_three, hAbs.1], by linarith [Real.pi_gt_three, hAbs.2]⟩
  exact mul_pos (Real.exp_pos _) hcos

theorem augmentedDomain_connected {D : Set (X n)} (hD : IsConnected D) :
    IsConnected (augmentedDomain D) := by
  have hball : IsConnected auxiliaryBall := (convex_ball (0 : X 3) 1).isConnected
    ⟨0, mem_ball_self one_pos⟩
  have heq : augmentedDomain D = splitAux.symm '' (D ×ˢ auxiliaryBall) := by
    ext z
    constructor
    · intro hz
      exact ⟨splitAux z, hz, splitAux.symm_apply_apply z⟩
    · rintro ⟨q, hq, rfl⟩
      change splitAux (splitAux.symm q) ∈ D ×ˢ auxiliaryBall
      rwa [splitAux.apply_symm_apply]
  rw [heq]
  exact (hD.prod hball).image _ splitAux.symm.continuous.continuousOn

theorem augmentedMetric_smoothOnDomain {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) :
    SmoothMetric (augmentedDomain D) L.augmentedMetric := by
  have h := augmentedMetric_smooth hD hL
  exact ⟨fun i j => (h.1 i j).mono (fun _ hz => hz.1), fun x hz => h.2 x hz.1⟩

theorem SolvesOn.augmentedHarmonic {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) {u : X n → ℝ} (hu : L.SolvesOn D u) :
    Harmonic (augmentedDomain D) L.augmentedMetric (liftedFunction u) := by
  refine ⟨(liftedFunction_smooth hu.1).mono (fun _ hz => hz.1), fun z hz => ?_⟩
  rw [laplace_liftedFunction hD hL hu.1 hz.1, hu.2 _ (show baseProjection z ∈ D from hz.1), zero_mul]

theorem solvesOn_of_liftedHarmonic {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u D)
    (hHar : Harmonic (augmentedDomain D) L.augmentedMetric (liftedFunction u)) :
    L.SolvesOn D u := by
  refine ⟨hu, fun x hx => ?_⟩
  let z := (splitAux (n := n)).symm (x,0)
  have hz : splitAux z = (x,0) := splitAux.apply_symm_apply _
  have hp : baseProjection z = x := congrArg Prod.fst hz
  have hq : auxiliaryProjection z = 0 := congrArg Prod.snd hz
  have hzD : z ∈ augmentedDomain D := by
    change splitAux z ∈ D ×ˢ auxiliaryBall
    rw [hz]
    exact ⟨hx, mem_ball_self (by norm_num)⟩
  have h₀ := hHar.2 z hzD
  rw [laplace_liftedFunction hD hL hu hzD.1, hp, hq] at h₀
  exact (mul_eq_zero.mp h₀).resolve_right (auxProfile_pos (mem_ball_self (by norm_num))).ne'

theorem eqOn_of_solutions_eqOn_open {L : ScalarElliptic n} {D S : Set (X n)}
    (hD : IsOpen D) (hDC : IsConnected D) (hS : IsOpen S) (hSne : S.Nonempty) (hSD : S ⊆ D)
    (hL : L.SmoothOn D) {u v : X n → ℝ} (hu : L.SolvesOn D u) (hv : L.SolvesOn D v)
    (hEq : EqOn u v S) : EqOn u v D := by
  have hsub : augmentedDomain S ⊆ augmentedDomain D := fun _ hz => ⟨hSD hz.1, hz.2⟩
  obtain ⟨w, hw⟩ := hSne
  have hne : (augmentedDomain S).Nonempty :=
    ⟨splitAux.symm (w,0), by
      change splitAux (splitAux.symm (w,0)) ∈ S ×ˢ auxiliaryBall
      rw [splitAux.apply_symm_apply]
      exact ⟨hw, mem_ball_self one_pos⟩⟩
  have haux : EqOn (liftedFunction u) (liftedFunction v) (augmentedDomain S) := by
    intro z hz
    simp only [liftedFunction, hEq (show baseProjection z ∈ S from hz.1)]
  have hfull := harmonic_eqOn_of_eqOn_open (augmentedDomain_open hD) (augmentedDomain_connected hDC)
    (augmentedDomain_open hS) hne hsub (augmentedMetric_smoothOnDomain hD hL)
    (hu.augmentedHarmonic hD hL) (hv.augmentedHarmonic hD hL) haux
  intro x hx
  let z := (splitAux (n := n)).symm (x,0)
  have hz : splitAux z = (x,0) := splitAux.apply_symm_apply _
  have hp : baseProjection z = x := congrArg Prod.fst hz
  have hq : auxiliaryProjection z = 0 := congrArg Prod.snd hz
  have hzD : z ∈ augmentedDomain D := by
    change splitAux z ∈ D ×ˢ auxiliaryBall
    rw [hz]
    exact ⟨hx, mem_ball_self one_pos⟩
  have h := hfull hzD
  simp only [liftedFunction, hp, hq] at h
  exact mul_right_cancel₀ (auxProfile_pos (mem_ball_self one_pos)).ne' h

theorem splitAux_measurePreserving (n : ℕ) :
    MeasurePreserving (splitAux (n := n)) volume volume := by
  let e : X (n+3) ≃ₗᵢ[ℝ] WithLp 2 (X n × X 3) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))
  exact (WithLp.volume_preserving_ofLp (X n) (X 3)).comp e.measurePreserving

theorem splitAux_measurePreserving_restrict {D : Set (X n)} (hD : IsOpen D) :
    MeasurePreserving (splitAux (n := n)) (volume.restrict (augmentedDomain D))
      ((volume.restrict D).prod (volume.restrict auxiliaryBall)) := by
  rw [Measure.prod_restrict]
  exact (splitAux_measurePreserving n).restrict_preimage
    (hD.measurableSet.prod measurableSet_ball)

private theorem auxProfile_memLp :
    MemLp auxProfile 2 (volume.restrict auxiliaryBall) := by
  let : IsFiniteMeasure ((volume : Measure (X 3)).restrict auxiliaryBall) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
  apply MemLp.of_bound auxProfile_smooth.continuous.aestronglyMeasurable (Real.exp 1)
  filter_upwards [ae_restrict_mem (s := auxiliaryBall) measurableSet_ball] with w hw
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have h0 : w 0 < 1 := by
    have := PiLp.norm_apply_le w 0
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans_lt hw'
  rw [auxProfile, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (Real.abs_cos_le_one _) |>.trans
    (Real.exp_le_exp.mpr h0.le)

def auxProfileLp : ChartL2 auxiliaryBall := auxProfile_memLp.toLp auxProfile

theorem auxProfileLp_ae : (auxProfileLp : X 3 → ℝ) =ᵐ[volume.restrict auxiliaryBall] auxProfile :=
  auxProfile_memLp.coeFn_toLp

private def tensorAuxProfile (D : Set (X n)) :
    ChartL2 D →L[ℝ] Lp ℝ 2 ((volume.restrict D).prod (volume.restrict auxiliaryBall)) := by
  let T : ChartL2 D →ₗ[ℝ] Lp ℝ 2 ((volume.restrict D).prod (volume.restrict auxiliaryBall)) :=
    { toFun := fun u => tensorLp u auxProfileLp
      map_add' := fun u v => by
        apply Lp.ext
        have hu := (Measure.quasiMeasurePreserving_fst (ν := volume.restrict auxiliaryBall)).ae_eq_comp
          (Lp.coeFn_add u v)
        filter_upwards [tensorLp_ae (u+v) auxProfileLp, tensorLp_ae u auxProfileLp,
          tensorLp_ae v auxProfileLp, Lp.coeFn_add (tensorLp u auxProfileLp) (tensorLp v auxProfileLp),
          hu] with z hUV hU hV hAdd hUV'
        change (u+v) z.1 = u z.1 + v z.1 at hUV'
        change _ = (tensorLp u auxProfileLp) z + (tensorLp v auxProfileLp) z at hAdd
        rw [hUV,hAdd,hU,hV,hUV',add_mul]
      map_smul' := fun c u => by
        apply Lp.ext
        have hu := (Measure.quasiMeasurePreserving_fst (ν := volume.restrict auxiliaryBall)).ae_eq_comp
          (Lp.coeFn_smul c u)
        filter_upwards [tensorLp_ae (c • u) auxProfileLp, tensorLp_ae u auxProfileLp,
          Lp.coeFn_smul c (tensorLp u auxProfileLp), hu] with z hCU hU hC hCU'
        change (c • u) z.1 = c * u z.1 at hCU'
        change _ = c * (tensorLp u auxProfileLp) z at hC
        change _ = (c • tensorLp u auxProfileLp) z
        rw [hCU,hC,hU,hCU',mul_assoc] }
  refine T.mkContinuous ‖auxProfileLp‖ (fun u => ?_)
  change ‖tensorLp u auxProfileLp‖ ≤ ‖auxProfileLp‖ * ‖u‖
  rw [norm_tensorLp,mul_comm]

/-- Tensoring by the fixed auxiliary profile maps coordinate L² to
coordinate L² on the augmented domain. -/
def scalarLiftL2 {D : Set (X n)} (hD : IsOpen D) :
    ChartL2 D →L[ℝ] ChartL2 (augmentedDomain D) :=
  ((Lp.compMeasurePreservingₗᵢ ℝ splitAux (splitAux_measurePreserving_restrict hD)).toContinuousLinearMap).comp
    (tensorAuxProfile D)

theorem scalarLiftL2_ae {D : Set (X n)} (hD : IsOpen D) (u : ChartL2 D) :
    (scalarLiftL2 hD u : X (n+3) → ℝ) =ᵐ[volume.restrict (augmentedDomain D)] liftedFunction u := by
  let hs := splitAux_measurePreserving_restrict hD
  have hProfile : (auxProfileLp : X 3 → ℝ) =ᵐ[volume.restrict auxiliaryBall] auxProfile :=
    auxProfile_memLp.coeFn_toLp
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := volume.restrict D)).ae_eq_comp hProfile
  have hrep : (tensorLp u auxProfileLp : X n × X 3 → ℝ) =ᵐ[
      (volume.restrict D).prod (volume.restrict auxiliaryBall)]
      (fun z => u z.1 * auxProfile z.2) := by
    filter_upwards [tensorLp_ae u auxProfileLp, hprod] with z hz hp
    exact hz.trans (congrArg (u z.1 * ·) hp)
  exact (Lp.coeFn_compMeasurePreserving (tensorLp u auxProfileLp) hs).trans
    (hs.quasiMeasurePreserving.ae_eq_comp hrep)

theorem norm_scalarLiftL2 {D : Set (X n)} (hD : IsOpen D) (u : ChartL2 D) :
    ‖scalarLiftL2 hD u‖ = ‖u‖ * ‖auxProfileLp‖ := by
  change ‖Lp.compMeasurePreserving splitAux (splitAux_measurePreserving_restrict hD)
    (tensorLp u auxProfileLp)‖ = _
  rw [Lp.norm_compMeasurePreserving, norm_tensorLp]

/-- The coordinate L² space of the general smooth scalar equation. -/
def scalarSolutionL2 {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D)
    (hL : L.SmoothOn D) : ClosedSubmodule ℝ (ChartL2 D) :=
  (harmonicL2Space (augmentedDomain_open hD) (augmentedMetric_smoothOnDomain hD hL)).comap
    (scalarLiftL2 hD)

theorem scalarLiftL2_mem_harmonic {L : ScalarElliptic n} {D : Set (X n)} (hD : IsOpen D)
    (hL : L.SmoothOn D) (u : scalarSolutionL2 hD hL) :
    scalarLiftL2 hD u.1 ∈ harmonicL2Space (augmentedDomain_open hD)
      (augmentedMetric_smoothOnDomain hD hL) := u.2

/-- Membership in the closed space is exactly representability by a
classical scalar solution on the base domain. -/
theorem mem_scalarSolutionL2_iff {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) (u : ChartL2 D) :
    u ∈ scalarSolutionL2 hD hL ↔
      ∃ f : X n → ℝ, L.SolvesOn D f ∧ (u : X n → ℝ) =ᵐ[volume.restrict D] f := by
  let U := augmentedDomain D
  have hU : IsOpen U := augmentedDomain_open hD
  have hSmooth := augmentedMetric_smoothOnDomain hD hL
  change scalarLiftL2 hD u ∈ harmonicL2Space hU hSmooth ↔ _
  rw [mem_harmonicL2Space_iff hU hSmooth]
  let s : X (n+3) ≃ᵐ X n × X 3 := splitAux.toHomeomorph.toMeasurableEquiv
  let hP : MeasurePreserving s (volume.restrict U) ((volume.restrict D).prod (volume.restrict auxiliaryBall)) :=
    splitAux_measurePreserving_restrict hD
  have hBase : Measure.QuasiMeasurePreserving (baseProjection (n := n))
      (volume.restrict U) (volume.restrict D) :=
    Measure.quasiMeasurePreserving_fst.comp hP.quasiMeasurePreserving
  constructor
  · rintro ⟨G,hG,hGrep⟩
    have hGrep' : liftedFunction (u : X n → ℝ) =ᵐ[volume.restrict U] G :=
      (scalarLiftL2_ae hD u).symm.trans hGrep
    have hPair :
        ∀ᵐ z : X n × X 3 ∂(volume.restrict D).prod (volume.restrict auxiliaryBall),
          u z.1 * auxProfile z.2 = G (splitAux.symm z) := by
      filter_upwards [(hP.symm s).quasiMeasurePreserving.ae_eq_comp hGrep'] with z hz
      have hz' := splitAux.apply_symm_apply z
      have hb : baseProjection (splitAux.symm z) = z.1 := congrArg Prod.fst hz'
      have ha : auxiliaryProjection (splitAux.symm z) = z.2 := congrArg Prod.snd hz'
      change liftedFunction (u : X n → ℝ) (splitAux.symm z) = G (splitAux.symm z) at hz
      simpa only [liftedFunction, hb, ha] using hz
    have hSwap := (Measure.measurePreserving_swap (μ := volume.restrict auxiliaryBall)
      (ν := volume.restrict D)).quasiMeasurePreserving.ae hPair
    have hFub : ∀ᵐ a : X 3 ∂volume.restrict auxiliaryBall, ∀ᵐ x : X n ∂volume.restrict D,
        u x * auxProfile a = G (splitAux.symm (x,a)) :=
      Measure.ae_ae_of_ae_prod hSwap
    let : (ae (volume.restrict auxiliaryBall)).NeBot := ae_neBot.mpr <| by
      rw [← Measure.measure_univ_ne_zero, Measure.restrict_apply_univ]
      exact (measure_ball_pos (μ := volume) (0 : X 3) one_pos).ne'
    obtain ⟨a,ha,hGa⟩ := ((ae_restrict_mem (s := auxiliaryBall) measurableSet_ball).and hFub).exists
    let f (x : X n) := G (splitAux.symm (x,a)) / auxProfile a
    have hfEq : (u : X n → ℝ) =ᵐ[volume.restrict D] f :=
      hGa.mono fun x hx => (eq_div_iff (auxProfile_pos ha).ne').mpr hx
    have hf : ContDiffOn ℝ ∞ f D := by
      refine (hG.1.comp (splitAux.symm.contDiff.comp (contDiff_id.prodMk contDiff_const)).contDiffOn
        (fun x hx => ?_)).div_const (auxProfile a)
      change splitAux (splitAux.symm (x,a)) ∈ D ×ˢ auxiliaryBall
      rw [splitAux.apply_symm_apply]
      exact ⟨hx,ha⟩
    have hSame : G =ᵐ[volume.restrict U] liftedFunction f := by
      apply hGrep'.symm.trans
      filter_upwards [hBase.ae_eq_comp hfEq] with z hz
      exact congrArg (· * auxProfile (auxiliaryProjection z)) hz
    have hLiftSmooth : ContDiffOn ℝ ∞ (liftedFunction f) U :=
      (liftedFunction_smooth hf).mono (fun _ hz => hz.1)
    have hPoint := Measure.eqOn_open_of_ae_eq hSame hU hG.1.continuousOn hLiftSmooth.continuousOn
    have hfHarm : Harmonic U L.augmentedMetric (liftedFunction f) := by
      refine ⟨hLiftSmooth,fun x hx => ?_⟩
      rw [← laplace_congrOn hU (fun _ _ => rfl) hPoint hx]
      exact hG.2 x hx
    exact ⟨f,solvesOn_of_liftedHarmonic hD hL hf hfHarm,hfEq⟩
  · rintro ⟨f,hf,hfu⟩
    refine ⟨liftedFunction f,hf.augmentedHarmonic hD hL,(scalarLiftL2_ae hD u).trans ?_⟩
    filter_upwards [hBase.ae_eq_comp hfu] with z hz
    exact congrArg (· * auxProfile (auxiliaryProjection z)) hz

end CalderonPaper.ScalarElliptic

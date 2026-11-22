module

public import Proof.Manuscript.MovingTrace.SmoothCollarLift
public import Proof.Manuscript.MovingTrace.ParametricTrialWave
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000

open CalderonN CalderonPatch.BoundaryLayer Set Filter Metric
open scoped ContDiff Topology

namespace CalderonPaper

variable {n : ℕ}
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

def liftedAngularTrial (v : ↥S) (u : (P × X n) × ℝ → ℂ) :
    P × Z → ℂ :=
  collarLift (stereographicPolarCollar v)
    (fun (q : P × (X n × ℝ)) => u ((q.1,q.2.1),q.2.2))

theorem liftedAngularTrial_value (v : ↥S) (u : (P × X n) × ℝ → ℂ)
    (p : P) (x : X n) {t : ℝ} (ht : t < 1) :
    liftedAngularTrial v u (p,polarCollar (angularPoint v) (x,t)) = u ((p,x),t) :=
  collarLift_readout (stereographicPolarCollar v) _ ht

theorem liftedAngularTrial_contDiff (v : ↥S) {u : (P × X n) × ℝ → ℂ}
    (hu : ContDiff ℝ ∞ u) {K : Set (X n × ℝ)} (hK : IsCompact K)
    (hK' : ∀ q ∈ K, q.2 < 1) (hSupp : ∀ p x, x ∉ K → u ((p,x.1),x.2) = 0) :
    ContDiff ℝ ∞ (liftedAngularTrial v u) :=
  contDiff_collarLift (stereographicPolarCollar v) (polarReadout_contDiffOn v)
    (hu.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)).contDiffOn
    hK hK' hSupp

theorem liftedAngularTrial_outwardNormal
    (v : ↥S) {u : (P × X n) × ℝ → ℂ}
    (hu : ContDiff ℝ ∞ (liftedAngularTrial v u)) (p : P) (x : X n) :
    fderiv ℝ (fun z => liftedAngularTrial v u (p,z)) (angularPoint v x) (angularPoint v x) =
      -deriv (fun t => u ((p,x),t)) 0 := by
  let w := angularPoint v x
  let U (z : Z) := liftedAngularTrial v u (p,z)
  let F (r : ℝ) := (1-r) • w
  have hU : ContDiff ℝ ∞ U := hu.comp (contDiff_const.prodMk contDiff_id)
  have hEq : (U ∘ F) =ᶠ[𝓝 (0 : ℝ)] (fun t => u ((p,x),t)) := by
    filter_upwards [Iio_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)] with t ht
    exact liftedAngularTrial_value v u p x ht
  have hF : HasDerivAt F (-w) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).const_sub 1).smul_const w using 1 <;> simp [F]
  have h₀ : F 0 = w := by simp [F]
  have hD : HasFDerivAt U (fderiv ℝ U w) (F 0) := by
    rw [h₀]
    exact (hU.differentiable (by simp) w).hasFDerivAt
  have h := (hD.comp_hasDerivAt 0 hF).deriv
  rw [hEq.deriv_eq,map_neg] at h
  change fderiv ℝ U w w = _
  rw [h,neg_neg]

theorem scaled_dephased_outward_trial
    {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)
    (v : ↥S) (a : P × X n → ℂ) (η : ℝ → ℝ)
    (hη : HasDerivAt η 0 0) (hη₀ : η 0 = 1) (phase : P × X n → ℝ)
    (M : ℕ) {h : ℝ} (hh : h ≠ 0)
    (hw : ContDiff ℝ ∞ (liftedAngularTrial v (B.finiteWave a η phase M h))) (p : P) (x : X n) :
    (h : ℂ) * (Complex.exp (Complex.I * (phase (p,x)/h : ℝ)))⁻¹ *
      fderiv ℝ (fun z => liftedAngularTrial v (B.finiteWave a η phase M h) (p,z))
        (angularPoint v x) (angularPoint v x) =
      ∑ j ∈ Finset.range (M+1), (h : ℂ)^j * (-B.traceCoefficient a j (p,x)) := by
  rw [liftedAngularTrial_outwardNormal v hw,mul_assoc,mul_neg,
    B.finiteWave_dephased_normal a η hη hη₀ phase M h (p,x)]
  simp only [mul_neg,Finset.mul_sum,Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [div_eq_mul_inv,← mul_assoc,mul_left_comm (h : ℂ),mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hh),one_mul]

end CalderonPaper

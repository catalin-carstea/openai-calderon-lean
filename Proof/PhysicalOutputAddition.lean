import Proof.MovingTraceDriftField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 15
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace ShrinkingSpheres

def PhysicalOutputRealization.add {Y : Set X} {g : MetricField} {e : Frame} {F G : Field}
    (P : PhysicalOutputRealization Y g e F) (Q : PhysicalOutputRealization Y g e G) :
    PhysicalOutputRealization Y g e (fun p => F p+G p) where
  representative := P.representative+Q.representative
  continuous := P.continuous.add Q.continuous
  eqOn := by intro y hy w;exact congrArg₂ (fun z v : ℂ => z+v) (P.eqOn y hy w) (Q.eqOn y hy w)
  memLp := P.memLp.add Q.memLp

theorem PhysicalOutputRealization.output_add {Y : Set X} {g : MetricField} {e : Frame} {F G : Field}
    (P : PhysicalOutputRealization Y g e F) (Q : PhysicalOutputRealization Y g e G) :
    (P.add Q).output = P.output+Q.output := by
  apply Lp.ext
  filter_upwards [(P.add Q).memLp.coeFn_toLp,P.memLp.coeFn_toLp,Q.memLp.coeFn_toLp,
    Lp.coeFn_add P.output Q.output] with p hsum hp hq hAdd
  exact hsum.trans ((congrArg₂ (fun z v : ℂ => z+v) hp.symm hq.symm).trans hAdd.symm)

def PhysicalOutputRealization.congr {Y : Set X} {g : MetricField} {e : Frame} {F G : Field}
    (P : PhysicalOutputRealization Y g e F) (hEq : ∀ p,F p = G p) : PhysicalOutputRealization Y g e G where
  representative := P.representative
  continuous := P.continuous
  eqOn := fun y hy w => (P.eqOn y hy w).trans (hEq _)
  memLp := P.memLp

theorem PhysicalOutputRealization.output_congr {Y : Set X} {g : MetricField} {e : Frame} {F G : Field}
    (P : PhysicalOutputRealization Y g e F) (hEq : ∀ p,F p = G p) :
    (P.congr hEq).output = P.output := rfl

def fullTraceOutputOfPrincipalDrift {Y : Set X} {d : Data} {φ : Field}
    (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ))
    (PD : PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ)) :
    PhysicalOutputRealization Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ) :=
  (PP.add PD).congr (fun p => (movingTrace_principal_add_drift d.γ d.g₂ d.radius d.adjoint φ p).symm)

theorem fullTraceOutputOfPrincipalDrift_output {Y : Set X} {d : Data} {φ : Field}
    (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ))
    (PD : PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ)) :
    (fullTraceOutputOfPrincipalDrift PP PD).output = PP.output+PD.output := PP.output_add PD

theorem fullTraceOutputOfPrincipalDrift_norm {Y : Set X} (hY : IsOpen Y) {d : Data} {φ : Field}
    (hDensity : ContinuousOn (metricDensity d.γ) Y)
    (PP : PhysicalOutputRealization Y d.γ d.frame (principalMovingTrace d.γ d.g₂ d.radius d.adjoint φ))
    (PD : PhysicalOutputRealization Y d.γ d.frame (movingTraceDrift d.γ d.g₂ d.radius d.adjoint φ)) :
    ‖PP.output+PD.output‖ = traceNorm Y d φ := by
  let P := fullTraceOutputOfPrincipalDrift PP PD
  have hNorm := P.normSq hY hDensity
  have hOutput := fullTraceOutputOfPrincipalDrift_output PP PD
  change ‖PP.output+PD.output‖ = Real.sqrt (outputSq Y d.γ d.frame (movingTrace d.γ d.g₂ d.radius d.adjoint φ))
  rw [← hNorm,hOutput,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

end ShrinkingSpheres

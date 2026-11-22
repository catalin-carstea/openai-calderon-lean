module

public import Proof.Manuscript.MovingTrace.VelocityChartPlaneDatum
public import Proof.Manuscript.MovingTrace.AngularChartCutoffs
public import Proof.Manuscript.CompactAngularFourier
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 5500000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

theorem chartPlaneWave_zero_outside_chart (ζ : E → ℂ) (p : P) (ξ : E)
    (w : ↥S) (hw : w ∉ (stereographic' ((n+1)-1) C.pole).source) :
    C.chartPlaneWave ζ p ξ w = 0 := by
  let κ := stereographic' ((n+1)-1) C.pole
  have hwv : w = C.pole := by
    by_contra h
    apply hw
    rw [stereographic'_source]
    exact h
  have hNot : (w : Z) ∉ (stereographicPolarCollar C.pole).target := by
    intro h
    have hn : ‖(w : Z)‖ = 1 := mem_sphere_zero_iff_norm.mp w.property
    have hd : direction (w : Z) = w := by simp [direction,hn]
    apply h.2
    rw [hd,hwv,real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp C.pole.property,one_pow]
  simp [chartPlaneWave,physicalDatum,liftedAngularTrial,collarLift,hNot]

theorem chartPlaneWave_restrict_sphere (ζ : E → ℂ) (p : P) (ξ : E) (w : ↥S) :
    C.chartPlaneWave ζ p ξ w =
      C.chartPlaneWave ζ p 0 w * angularFourierPhase (dim := n+1) (stereographic' ((n+1)-1) C.pole w) ξ := by
  let κ := stereographic' ((n+1)-1) C.pole
  by_cases hw : w ∈ κ.source
  · have hInv : angularPoint C.pole (κ w) = w := congrArg Subtype.val (κ.left_inv hw)
    have hRead (ξ : E) : C.chartPlaneWave ζ p ξ w =
        angularFourierPhase (dim := n+1) (κ w) ξ * ζ (κ w) := by
      calc
        _ = C.chartPlaneWave ζ p ξ (angularPoint C.pole (κ w)) :=
          congrArg (C.chartPlaneWave ζ p ξ) hInv.symm
        _ = _ := by
          rw [C.chartPlaneWave_value,phase_eq_angularFourierPhase,inv_one,one_smul]
    change _ = C.chartPlaneWave ζ p 0 w * angularFourierPhase (dim := n+1) (κ w) ξ
    rw [hRead ξ,hRead 0]
    simp [angularFourierPhase,mul_comm]
  · rw [C.chartPlaneWave_zero_outside_chart ζ p ξ w hw,
      C.chartPlaneWave_zero_outside_chart ζ p 0 w hw,zero_mul]

theorem localizedDatum_eq_chartPlaneWaveZero (ζ : E → ℂ) (p : P)
    (η u : Z → ℂ) (hη : angularSupport η ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (hOne : EqOn ζ 1 (angularChartSupport C.pole η)) (w : ↥S) :
    η w * u w = C.chartPlaneWave ζ p 0 w *
      (η (angularPoint C.pole (stereographic' ((n+1)-1) C.pole w)) *
        u (angularPoint C.pole (stereographic' ((n+1)-1) C.pole w))) := by
  let κ := stereographic' ((n+1)-1) C.pole
  by_cases hw : w ∈ κ.source
  · have hInv : angularPoint C.pole (κ w) = w := congrArg Subtype.val (κ.left_inv hw)
    have hZ : C.chartPlaneWave ζ p 0 w = ζ (κ w) := by
      calc
        _ = C.chartPlaneWave ζ p 0 (angularPoint C.pole (κ w)) :=
          congrArg (C.chartPlaneWave ζ p 0) hInv.symm
        _ = _ := by
          rw [C.chartPlaneWave_value,phase_eq_angularFourierPhase]
          simp [angularFourierPhase]
    change η w * u w = C.chartPlaneWave ζ p 0 w * (η (angularPoint C.pole (κ w)) * _)
    rw [hZ,hInv]
    by_cases hηw : η w = 0
    · simp [hηw]
    · have hOne' : ζ (κ w) = 1 := hOne (mem_image_of_mem κ (subset_closure hηw))
      simp [hOne']
  · have hηw : η w = 0 := by
      by_contra h
      exact hw (hη (subset_closure h))
    simp [hηw,C.chartPlaneWave_zero_outside_chart ζ p 0 w hw]


end SignedPoissonCollar
end CalderonPaper

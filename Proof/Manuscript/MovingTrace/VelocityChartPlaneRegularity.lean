module

public import Proof.Manuscript.MovingTrace.VelocityChartDatumRestriction
public import Proof.Manuscript.AngularFourierResponse
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

/-- The plane-wave response is a continuous function on the whole unit
sphere because its output cutoff is supported in the selected chart. -/
theorem velocity_chart_planeResponse_regular
    (A : SmoothRadialVelocity G) (p : P) {χ : Z → ℂ}
    (hχS : angularSupport χ ⊆ (stereographic' ((n+1)-1) C.pole).source)
    (ζ : E → ℂ) {s : Q → E → ℂ} (hS : Continuous fun q : E × E => s (p,q.1) q.2)
    {B : ℝ} (hB : 0 ≤ B) (hGrowth : ∀ x ξ, ‖s (p,x) ξ‖ ≤ B*(1+‖ξ‖))
    (hExact : ∀ x ξ, s (p,x) ξ = C.actualVelocityChartSymbol A (χ ∘ angularPoint C.pole) ζ (p,x) ξ) :
    let κ := stereographic' ((n+1)-1) C.pole
    let K (q : ↥S × E) := χ q.1 * A.operator p (C.chartPlaneWave ζ p q.2) q.1
    Continuous K ∧ (∀ w ξ, ‖K (w,ξ)‖ ≤ B*(1+‖ξ‖)) ∧
      ∀ w ∈ κ.source, ∀ ξ,
        K (w,ξ) = angularFourierPhase (dim := n+1) (κ w) ξ * s (p,κ w) ξ := by
  let κ := stereographic' ((n+1)-1) C.pole
  let K (q : ↥S × E) := χ q.1 * A.operator p (C.chartPlaneWave ζ p q.2) q.1
  have hKChart (w : ↥S) (ξ : E) (hw : w ∈ κ.source) :
      K (w,ξ) = angularFourierPhase (dim := n+1) (κ w) ξ * s (p,κ w) ξ := by
    have he : angularPoint C.pole (κ w) = w := congrArg Subtype.val (κ.left_inv hw)
    have hPh := phase_eq_angularFourierPhase (P := P) (n := n) 1 (p,ξ) (κ w)
    simp only [inv_one,one_smul] at hPh
    have hInv : angularFourierPhase (dim := n+1) (κ w) ξ * dephase 1 ((p,ξ),κ w) = 1 := by
      change _ * (phase 1 ((p,ξ),κ w))⁻¹ = 1
      rw [← hPh]
      exact mul_inv_cancel₀ (Complex.exp_ne_zero _)
    change χ w * A.operator p (C.chartPlaneWave ζ p ξ) w = _
    rw [hExact,actualVelocityChartSymbol,Function.comp_apply,he]
    calc
      _ = (angularFourierPhase (dim := n+1) (κ w) ξ * dephase 1 ((p,ξ),κ w)) *
          (χ w * A.operator p (C.chartPlaneWave ζ p ξ) w) := by rw [hInv,one_mul]
      _ = _ := by ring
  have hK0 (w : ↥S) (ξ : E) (hw : w ∉ angularSupport χ) : K (w,ξ) = 0 := by
    have h : χ w = 0 := by by_contra hn; exact hw (subset_closure hn)
    simp [K,h]
  have hPhase : Continuous (fun q : E × E => angularFourierPhase (dim := n+1) q.1 q.2) := by
    unfold angularFourierPhase
    fun_prop
  have hKO : ContinuousOn K (κ.source ×ˢ (univ : Set E)) := by
    have hM : ContinuousOn (fun q : ↥S × E => (κ q.1,q.2)) (κ.source ×ˢ univ) :=
      (κ.continuousOn.comp continuousOn_fst (fun _ h => h.1)).prodMk continuousOn_snd
    exact ((hPhase.mul hS).continuousOn.comp hM (fun _ _ => mem_univ _)).congr
      (fun q hq => hKChart q.1 q.2 hq.1)
  have hKC : Continuous K := by
    rw [continuous_iff_continuousAt]
    intro q
    by_cases hq : q.1 ∈ κ.source
    · exact hKO.continuousAt ((κ.open_source.prod isOpen_univ).mem_nhds ⟨hq,mem_univ _⟩)
    · have hn : q.1 ∉ angularSupport χ := fun h => hq (hχS h)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [(isClosed_closure.isOpen_compl.prod isOpen_univ).mem_nhds
        (show q ∈ (angularSupport χ)ᶜ ×ˢ (univ : Set E) from ⟨hn,mem_univ _⟩)] with z hz
      exact hK0 z.1 z.2 hz.1
  have hKB (w : ↥S) (ξ : E) : ‖K (w,ξ)‖ ≤ B*(1+‖ξ‖) := by
    by_cases hw : w ∈ κ.source
    · rw [hKChart w ξ hw,norm_mul,angularFourierPhase_norm (d := n+1),one_mul]
      exact hGrowth (κ w) ξ
    · rw [hK0 w ξ (fun h => hw (hχS h)),norm_zero]
      positivity
  exact ⟨hKC,hKB,fun w hw ξ => hKChart w ξ hw⟩

end SignedPoissonCollar
end CalderonPaper

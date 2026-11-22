module

public import Proof.Manuscript.MovingTrace.FiniteCollarPoissonTrial
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => sphere (0 : Z) 1
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def phase (h : ℝ) (q : Q × E) : ℂ :=
  Complex.exp (Complex.I * ((ParametricLayerCoefficients.planePhase covector q)/h : ℝ))

theorem phase_contDiff (h : ℝ) : ContDiff ℝ ∞ (phase (P := P) (n := n) h) := by
  unfold phase
  have hf : ContDiff ℝ ∞ (ParametricLayerCoefficients.planePhase (covector (P := P) (n := n))) :=
    ParametricLayerCoefficients.planePhase_contDiff covector_contDiff
  exact (contDiff_const (c := Complex.I) |>.mul (Complex.ofRealCLM.contDiff.comp (hf.div_const h))).cexp

theorem phase_eq_angularFourierPhase (h : ℝ) (p : Q) (x : E) :
    phase h (p,x) = angularFourierPhase (dim := n+1) x (h⁻¹ • p.2) := by
  unfold phase angularFourierPhase
  rw [planePhase_covector_eq,real_inner_smul_right,div_eq_mul_inv]
  congr 1
  simp only [Complex.ofReal_mul]
  ring

theorem physicalDatum_chart (a : Q × E → ℂ) (h : ℝ) (p : Q) (x : E) :
    C.physicalDatum a h (p,angularPoint C.pole x) = phase h (p,x) * a (p,x) := by
  have hC : polarCollar (angularPoint C.pole) (x,(0:ℝ)) = angularPoint C.pole x := by
    change (1-(0:ℝ)) • angularPoint C.pole x = _
    rw [sub_zero,one_smul]
  rw [← hC,physicalDatum,liftedAngularTrial_value _ _ _ _ zero_lt_one]
  simp only [phase,collarDepthCutoff_one C.pos (by simpa using C.pos.le : |(0:ℝ)| ≤ C.δ),
    Complex.ofReal_one,one_mul]

theorem physicalDatum_zero_off_trialSupport (a : Q × E → ℂ) {Kx : Set E}
    (ha₀ : ∀ (p : Q) (x : E), x ∉ Kx → a (p,x) = 0)
    (h : ℝ) (p : Q) (z : Z) (hz : z ∉ C.trialSupport Kx) :
    C.physicalDatum a h (p,z) = 0 := by
  apply collarLift_zero_off_image (stereographicPolarCollar C.pole)
    (fun q : Q × (E × ℝ) => collarDepthCutoff C.δ q.2.2 *
      phase h (q.1,q.2.1) * a (q.1,q.2.1)) (K := Kx ×ˢ Icc (-2*C.δ) (2*C.δ)) _ (p,z) hz
  intro q x hx
  by_cases h : x.1 ∈ Kx
  · have hDepth : 2*C.δ ≤ |x.2| := by
      by_contra! ht
      obtain ⟨hlo,hhi⟩ := abs_lt.mp ht
      exact hx ⟨h,by constructor <;> linarith⟩
    simp [collarDepthCutoff_zero C.pos hDepth]
  · simp [ha₀ q x.1 h]

theorem physicalDatum_contDiff {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a)
    {Kx : Set E} (hKx : IsCompact Kx) (ha₀ : ∀ (p : Q) (x : E), x ∉ Kx → a (p,x) = 0)
    (h : ℝ) : ContDiff ℝ ∞ (C.physicalDatum a h) := by
  have hWave : ContDiff ℝ ∞ (fun q : (Q × E) × ℝ => collarDepthCutoff C.δ q.2 *
      phase h q.1 * a q.1) :=
    ((Complex.ofRealCLM.contDiff.comp ((collarDepthCutoff_contDiff C.δ).comp contDiff_snd)).mul
      ((phase_contDiff h).comp contDiff_fst)).mul (ha.comp contDiff_fst)
  apply liftedAngularTrial_contDiff C.pole hWave (hKx.prod (isCompact_Icc (a := -2*C.δ) (b := 2*C.δ)))
  · intro x hx
    exact hx.2.2.trans_lt (by linarith [C.small])
  · intro p x hx
    by_cases h : x.1 ∈ Kx
    · have hDepth : 2*C.δ ≤ |x.2| := by
        by_contra! ht
        obtain ⟨hlo,hhi⟩ := abs_lt.mp ht
        exact hx ⟨h,by constructor <;> linarith⟩
      simp [collarDepthCutoff_zero C.pos hDepth]
    · simp [ha₀ p x.1 h]

theorem angularPoissonReadout_physicalDatum_contDiffOn {a : Q × E → ℂ} (ha : ContDiff ℝ ∞ a)
    {Kx : Set E} (hKx : IsCompact Kx) (ha₀ : ∀ (p : Q) (x : E), x ∉ Kx → a (p,x) = 0)
    (h : ℝ) :
    ContDiffOn ℝ ∞ (G.angularPoissonReadout (angularPoint C.pole) (C.physicalDatum a h))
      ((G.V ×ˢ univ) ×ˢ univ) := by
  let u := C.physicalDatum a h
  let U := C.trialSupport Kx
  have hU : IsCompact U := (hKx.prod isCompact_Icc).image_of_continuousOn
    ((stereographicPolarCollar C.pole).continuousOn.mono (fun q hq => hq.2.2.trans_lt (by linarith [C.small])))
  have hu : ContDiff ℝ ∞ u := C.physicalDatum_contDiff ha hKx ha₀ h
  have hU₀ : ∀ (p : Q) z, z ∉ U → u (p,z) = 0 :=
    C.physicalDatum_zero_off_trialSupport a ha₀ h
  let A (q : Q × Z) := G.a (q.1.1,q.2)
  let f : Q × Z → ℂ := cutTrialResidual A u 1
  have hA : ContDiff ℝ ∞ A := G.smoothA.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hf : ContDiff ℝ ∞ f := cutTrialResidual_contDiff hA hu zero_lt_one
  have hfU : ∀ (p : Q) z, z ∉ U → f (p,z) = 0 :=
    fun p _ hz => cutTrialResidual_zero_off_support hU.isClosed hU₀ 1 p hz
  have hB (x : E) : angularPoint C.pole x ∈ closedBall (0:Z) 1 :=
    sphere_subset_closedBall ((stereographic' ((n+1)-1) C.pole).symm x).property
  obtain ⟨B,hB₀,hSolve⟩ := G.uniform_angularPoisson_trial_residual
    («Q» := E) (J := (∅ : Set P)) isCompact_empty (empty_subset _)
    (angularPoint C.pole) (angularPoint_contDiff C.pole) hB (K := (∅ : Set E)) isCompact_empty 0
  exact (hSolve u u f hu hf U hU hfU (fun _ _ _ _ => rfl)
    (fun p _ z hz => (cutTrialResidual_eq_on_closedBall A u zero_lt_one p (ball_subset_closedBall hz)).symm)).1

theorem physicalDatum_scale_eq (a : P × E → ℂ) (b : Q × E → ℂ)
    (p : P) (ν : E) (hb : ∀ x, b ((p,ν),x) = a (p,x)) (h : ℝ) (z : Z) :
    C.physicalDatum b h ((p,ν),z) =
      C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,h⁻¹ • ν),z) := by
  have hPhase (x : E) : phase h ((p,ν),x) = phase 1 ((p,h⁻¹ • ν),x) := by
    rw [phase_eq_angularFourierPhase,phase_eq_angularFourierPhase,inv_one,one_smul]
  unfold physicalDatum liftedAngularTrial
  simp only [collarLift]
  split
  · change _ * phase h ((p,ν),_) * b ((p,ν),_) =
      _ * phase 1 ((p,h⁻¹ • ν),_) * a (p,_)
    rw [hPhase,hb]
  · rfl

end SignedPoissonCollar
end CalderonPaper

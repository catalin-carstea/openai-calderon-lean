module

public import Proof.Manuscript.MovingTrace.LocalPoissonAnnulus
public import Proof.Manuscript.MovingTrace.VelocityChartPlaneDatum
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 5300000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch.BoundaryLayer Set Metric Filter
open OAI.AnisotropicCalderon.SmoothSphereRotation
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

theorem normalInput_chartPlaneWave_eq_datum (A : SmoothRadialVelocity G)
    (ζ : E → ℂ) (a : Q → ℂ) (p : P) (ξ : E)
    (ha : ∀ x, a (p,x) = ζ x * C.rawChartNormalAmplitude A (p,x)) :
    EqOn (fun z => C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,ξ),z))
      (A.normalInput (C.chartPlaneWave ζ p ξ) p) (standardSphere (n+1)) := by
  let e := stereographicPolarCollar C.pole
  intro z hz
  change C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,ξ),z) =
    A.normalInput (C.chartPlaneWave ζ p ξ) p z
  by_cases hze : z ∈ e.target
  · let x : E := (e.symm z).1
    have h0 : (e.symm z).2 = 0 := by
      change 1-‖z‖ = 0
      rw [mem_sphere_zero_iff_norm.mp hz,sub_self]
    have hw : angularPoint C.pole x = z := by
      have he := e.right_inv hze
      change (1-(e.symm z).2) • angularPoint C.pole x = z at he
      rwa [h0,sub_zero,one_smul] at he
    rw [← hw,C.physicalDatum_chart,ha]
    change _ = C.chartPlaneWave ζ p ξ (angularPoint C.pole x) * C.rawChartNormalAmplitude A (p,x)
    rw [C.chartPlaneWave_value,mul_assoc]
  · have hZero (b : (Q × E) → ℂ) : C.physicalDatum b 1 ((p,ξ),z) = 0 := by
      have hze' : z ∉ (stereographicPolarCollar C.pole).target := hze
      simp [physicalDatum,liftedAngularTrial,collarLift,hze']
    rw [hZero]
    change 0 = C.chartPlaneWave ζ p ξ z * _
    unfold chartPlaneWave
    rw [hZero,zero_mul]

private theorem chartPlaneWave_normal_readout (A : SmoothRadialVelocity G)
    {ζ : E → ℂ} {a : Q → ℂ} {p : P} (hp : p ∈ A.U)
    {ξ : E} (hφ : ContDiff ℝ ∞ (C.chartPlaneWave ζ p ξ))
    (hAmp : ∀ x, a (p,x) = ζ x * C.rawChartNormalAmplitude A (p,x)) (x : E) :
    let w : Z := angularPoint C.pole x
    dephase (P := P) (n := n) 1 ((p,ξ),x) * fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z))
      (A.normalInput (C.chartPlaneWave ζ p ξ) p)) w w = C.rawPoissonSymbol a (p,x) ξ := by
  let w : Z := angularPoint C.pole x
  have hw : w ∈ standardSphere (n+1) := ((stereographic' ((n+1)-1) C.pole).symm x).property
  let b := fun z => C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,ξ),z)
  let d := A.normalInput (C.chartPlaneWave ζ p ξ) p
  have hInput : ContDiffOn ℝ ∞ d A.S := A.normalInput_contDiffOn hp Subset.rfl hφ.contDiffOn
  have hEq : EqOn b d (standardSphere (n+1)) := C.normalInput_chartPlaneWave_eq_datum A ζ a p ξ hAmp
  have hDer := A.complexFixedBallPoisson_fderiv_congr hp ⟨A.S,A.openS,A.sphere_mem,hInput⟩ hEq
      (sphere_subset_closedBall hw)
  change dephase (P := P) (n := n) 1 ((p,ξ),x) * fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z)) d) w w = _
  rw [← hDer]
  rfl

private theorem chartPlaneWave_rotation_readout (A : SmoothRadialVelocity G)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {V : P × Z → Z} (hV : ContDiff ℝ ∞ V)
    {W : Set Z} (hW : IsOpen W) (hSW : standardSphere (n+1) ⊆ W)
    {p : P} (hEqV : EqOn (fun z => V (p,z)) (fun z => A.velocity (p,z)) W)
    (i j : I (n+1)) (x ξ : E) :
    let w : Z := angularPoint C.pole x
    fderiv ℝ (fun z => C.chartPlaneWave ζ p ξ z * A.rotationWeight i j (p,z)) w (rotationVector i j w) =
      phase (P := P) (n := n) 1 ((p,ξ),x) * (C.localRotationLow i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) +
        C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) ξ) := by
  let w : Z := angularPoint C.pole x
  let φ : Z → ℂ := C.chartPlaneWave ζ p ξ
  have hw : w ∈ standardSphere (n+1) := ((stereographic' ((n+1)-1) C.pole).symm x).property
  have hEq : (fun z => φ z * A.rotationWeight i j (p,z)) =ᶠ[𝓝 w]
      (fun z => φ z * rotationCoeff V i j (p,z)) := by
    filter_upwards [hW.mem_nhds (hSW hw)] with z hz
    have hVz : V (p,z) = A.velocity (p,z) := hEqV hz
    simp only [rotationCoeff,SmoothRadialVelocity.rotationWeight,hVz]
  change fderiv ℝ (fun z => φ z * A.rotationWeight i j (p,z)) w (rotationVector i j w) = _
  rw [hEq.fderiv_eq]
  exact C.rotationDerivative_physicalDatum isOpen_univ (hζ.comp contDiff_snd)
    (rotationCoeff_contDiff hV i j).contDiffOn i j p (mem_univ _) x ξ

/-- Dephase the exact angular response into its elliptic normal readout
and its first-order angular rotation terms. -/
theorem chartPlaneWave_adjoint_readout (A : SmoothRadialVelocity G)
    {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E}
    (hKζ : IsCompact Kζ) (hζ₀ : ∀ x ∉ Kζ, ζ x = 0)
    {V : P × Z → Z} (hV : ContDiff ℝ ∞ V)
    {W : Set Z} (hW : IsOpen W) (hSW : standardSphere (n+1) ⊆ W)
    {a : Q → ℂ} {p : P} (hp : p ∈ A.U)
    (hEqV : EqOn (fun z => V (p,z)) (fun z => A.velocity (p,z)) W)
    (hAmp : ∀ x, a (p,x) = ζ x * C.rawChartNormalAmplitude A (p,x)) (x ξ : E) :
    dephase (P := P) (n := n) 1 ((p,ξ),x) * A.operator p (C.chartPlaneWave ζ p ξ) (angularPoint C.pole x) =
      (C.chartWeight A (p,x) : ℂ) * C.rawPoissonSymbol a (p,x) ξ -
        ∑ i, ∑ j, (C.localRotationLow i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) +
          C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) ξ) := by
  let w : Z := angularPoint C.pole x
  let φ : Z → ℂ := C.chartPlaneWave ζ p ξ
  let θ : ℂ := dephase (P := P) (n := n) 1 ((p,ξ),x)
  let osc : ℂ := phase (P := P) (n := n) 1 ((p,ξ),x)
  let H : ℂ := fderiv ℝ (complexFixedBallPoisson (fun z => G.g (p,z)) (A.normalInput φ p)) w w
  let R (i j : I (n+1)) : ℂ := fderiv ℝ (fun z => φ z * A.rotationWeight i j (p,z)) w (rotationVector i j w)
  let B (i j : I (n+1)) : ℂ := C.localRotationLow i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) +
    C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff V i j) (p,x) ξ
  have hw : w ∈ standardSphere (n+1) := ((stereographic' ((n+1)-1) C.pole).symm x).property
  have hφ : ContDiff ℝ ∞ φ := (C.chartPlaneWave_contDiff hζ hKζ hζ₀).comp
    ((contDiff_const (c := (p,ξ))).prodMk contDiff_id)
  have hModel : A.operator p φ w = (A.weight (p,w):ℂ) * H - ∑ i, ∑ j, R i j :=
    A.operator_eq_complex_formula (p := p) (φ := φ) («S» := A.S) (z := w) hp A.openS A.sphere_mem Subset.rfl hφ.contDiffOn (A.sphere_mem hw)
  have hNormal : θ * H = C.rawPoissonSymbol a (p,x) ξ := C.chartPlaneWave_normal_readout A (ζ := ζ) (a := a) (p := p) hp (ξ := ξ) hφ hAmp x
  have hRot (i j : I (n+1)) : R i j = osc * B i j :=
    C.chartPlaneWave_rotation_readout A (ζ := ζ) hζ (V := V) hV (W := W) hW hSW (p := p) hEqV i j x ξ
  have hPhase : θ * osc = 1 := inv_mul_cancel₀ (Complex.exp_ne_zero _)
  have hRotSum : θ * (∑ i, ∑ j, R i j) = ∑ i, ∑ j, B i j := by
    calc
      _ = ∑ i, ∑ j, θ * R i j := by simp only [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = θ * (osc * B i j) := congrArg (θ * ·) (hRot i j)
          _ = _ := by rw [← mul_assoc,hPhase,one_mul]
  change θ * A.operator p φ w = (A.weight (p,w) : ℂ) * C.rawPoissonSymbol a (p,x) ξ - ∑ i, ∑ j, B i j
  calc
    _ = θ * ((A.weight (p,w):ℂ) * H - ∑ i, ∑ j, R i j) := congrArg (θ * ·) hModel
    _ = (A.weight (p,w):ℂ) * (θ * H) - θ * (∑ i, ∑ j, R i j) := by ring
    _ = _ := congrArg₂ (· - ·) (congrArg ((A.weight (p,w):ℂ) * ·) hNormal) hRotSum

end SignedPoissonCollar
end CalderonPaper

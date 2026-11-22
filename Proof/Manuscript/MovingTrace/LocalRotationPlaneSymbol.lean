module

public import Proof.Manuscript.MovingTrace.PlaneWaveDirichletData
public import Proof.CalderonN.ParametricBallVelocityAdjoint
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch.BoundaryLayer Set Metric Filter
open OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

def localRotationAmplitude (a : Q → ℂ) (H : P × Z → ℂ) (q : P × Z) : ℂ :=
  a (q.1,(polarReadout C.pole q.2).1) * H q

def localRotationLow (i j : I (n+1)) (a : Q → ℂ) (H : P × Z → ℂ) (q : Q) : ℂ :=
  fderiv ℝ (C.localRotationAmplitude a H) (q.1,angularPoint C.pole q.2)
    (0,rotationVector i j (angularPoint C.pole q.2))

def localRotationHigh (i j : I (n+1)) (a : Q → ℂ) (H : P × Z → ℂ) (q : Q) (ξ : E) : ℂ :=
  let w := angularPoint C.pole q.2
  let D := fderiv ℝ (fun z => (polarReadout C.pole z).1) w (rotationVector i j w)
  Complex.I * ((2*Real.pi*⟪ξ,D⟫_ℝ : ℝ) : ℂ) * C.localRotationAmplitude a H (q.1,w)

theorem localRotationHigh_smul (i j : I (n+1)) (a : Q → ℂ) (H : P × Z → ℂ)
    (q : Q) (ξ : E) (c : ℝ) :
    C.localRotationHigh i j a H q (c • ξ) = c • C.localRotationHigh i j a H q ξ := by
  simp only [localRotationHigh,real_inner_smul_left,Complex.ofReal_mul,Complex.real_smul]
  ring

theorem angularPoint_mem_collar_target (x : E) : angularPoint C.pole x ∈ (stereographicPolarCollar C.pole).target := by
  have h := (stereographicPolarCollar C.pole).map_source (show (x,(0:ℝ)) ∈
    (stereographicPolarCollar C.pole).source from by change (0:ℝ) < 1; exact zero_lt_one)
  change (1-(0:ℝ)) • angularPoint C.pole x ∈ _ at h
  rwa [sub_zero,one_smul] at h

theorem polarReadout_angularPoint (x : E) : polarReadout C.pole (angularPoint C.pole x) = (x,0) := by
  have h := polarReadout_polarCollar C.pole (x,(0:ℝ)) zero_lt_one
  change polarReadout C.pole ((1-(0:ℝ)) • angularPoint C.pole x) = _ at h
  rwa [sub_zero,one_smul] at h

theorem localRotationAmplitude_contDiffOn {U : Set P} {a : Q → ℂ} (ha : ContDiff ℝ ∞ a)
    {H : P × Z → ℂ} (hH : ContDiffOn ℝ ∞ H (U ×ˢ (stereographicPolarCollar C.pole).target)) :
    ContDiffOn ℝ ∞ (C.localRotationAmplitude a H) (U ×ˢ (stereographicPolarCollar C.pole).target) := by
  have hRead := (polarReadout_contDiffOn C.pole).fst.comp contDiffOn_snd
    (fun q (hq : q ∈ U ×ˢ (stereographicPolarCollar C.pole).target) => hq.2)
  exact (ha.contDiffOn.comp (contDiffOn_fst.prodMk hRead) (fun _ _ => mem_univ _)).mul hH

theorem localRotationSymbol_contDiffOn {U : Set P} (hU : IsOpen U) {a : Q → ℂ}
    (ha : ContDiff ℝ ∞ a) {H : P × Z → ℂ}
    (hH : ContDiffOn ℝ ∞ H (U ×ˢ (stereographicPolarCollar C.pole).target))
    (i j : I (n+1)) :
    ContDiffOn ℝ ∞ (C.localRotationLow i j a H) (U ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (C.localRotationHigh i j a H)) ((U ×ˢ univ) ×ˢ univ) := by
  let e := stereographicPolarCollar C.pole
  let T := U ×ˢ e.target
  let w : E → Z := angularPoint C.pole
  have hT : IsOpen T := hU.prod e.open_target
  have hA := C.localRotationAmplitude_contDiffOn ha hH
  have hw : ContDiff ℝ ∞ w := angularPoint_contDiff C.pole
  have hrot := (contDiff_rotationVector i j).comp hw
  have hp : MapsTo (fun q : Q => (q.1,w q.2)) (U ×ˢ (univ : Set E)) T :=
    fun q hq => ⟨hq.1,C.angularPoint_mem_collar_target q.2⟩
  have hW : ContDiffOn ℝ ∞ (fun q : Q => (q.1,w q.2)) (U ×ˢ univ) :=
    (contDiff_fst.prodMk (hw.comp contDiff_snd)).contDiffOn
  have hV : ContDiff ℝ ∞ (fun q : Q => ((0 : P),rotationVector i j (w q.2))) :=
    contDiff_const.prodMk (hrot.comp contDiff_snd)
  have hLow : ContDiffOn ℝ ∞ (C.localRotationLow i j a H) (U ×ˢ univ) :=
    ((hA.fderiv_of_isOpen (m := ∞) hT (by simp)).comp hW hp).clm_apply hV.contDiffOn
  have hRead : ContDiffOn ℝ ∞ (fun z => (polarReadout C.pole z).1) e.target :=
    (polarReadout_contDiffOn C.pole).fst
  have hL : ContDiff ℝ ∞ (fun x : E => fderiv ℝ (fun z => (polarReadout C.pole z).1)
      (w x) (rotationVector i j (w x))) := by
    apply contDiffOn_univ.mp
    exact ((hRead.fderiv_of_isOpen (m := ∞) e.open_target (by simp)).comp hw.contDiffOn
      (fun x _ => C.angularPoint_mem_collar_target x)).clm_apply hrot.contDiffOn
  have hInner : ContDiff ℝ ∞ (fun q : Q × E =>
      ⟪q.2,fderiv ℝ (fun z => (polarReadout C.pole z).1) (w q.1.2)
        (rotationVector i j (w q.1.2))⟫_ℝ) :=
    contDiff_snd.inner ℝ (hL.comp contDiff_fst.snd)
  have hAH : ContDiffOn ℝ ∞ (fun q : Q × E => C.localRotationAmplitude a H (q.1.1,w q.1.2))
      ((U ×ˢ univ) ×ˢ univ) := (hA.comp hW hp).comp contDiffOn_fst (fun _ h => h.1)
  have hC : ContDiff ℝ ∞ (fun q : Q × E => Complex.I *
      ((2*Real.pi*⟪q.2,fderiv ℝ (fun z => (polarReadout C.pole z).1) (w q.1.2)
        (rotationVector i j (w q.1.2))⟫_ℝ : ℝ) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hInner))
  exact ⟨hLow,hC.contDiffOn.mul hAH⟩

theorem rotationDerivative_physicalDatum
    {U : Set P} (hU : IsOpen U) {a : Q → ℂ} (ha : ContDiff ℝ ∞ a)
    {H : P × Z → ℂ} (hH : ContDiffOn ℝ ∞ H (U ×ˢ (stereographicPolarCollar C.pole).target))
    (i j : I (n+1)) (p : P) (hp : p ∈ U) (x ξ : E) :
    fderiv ℝ (fun z => C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,ξ),z) * H (p,z))
      (angularPoint C.pole x) (rotationVector i j (angularPoint C.pole x)) =
      phase 1 ((p,ξ),x) * (C.localRotationLow i j a H (p,x) + C.localRotationHigh i j a H (p,x) ξ) := by
  let e := stereographicPolarCollar C.pole
  let w := angularPoint C.pole x
  let X (z : Z) := (polarReadout C.pole z).1
  let θ : E →L[ℝ] ℝ := (2*Real.pi) • innerSL ℝ ξ
  let F (z : Z) := Complex.exp (Complex.I * (θ (X z) : ℝ))
  let B (z : Z) := C.localRotationAmplitude a H (p,z)
  have hw : w ∈ e.target := C.angularPoint_mem_collar_target x
  have hx : X w = x := congrArg Prod.fst (C.polarReadout_angularPoint x)
  have hD : DifferentiableAt ℝ X w :=
    (((polarReadout_contDiffOn C.pole).fst).contDiffAt (e.open_target.mem_nhds hw)).differentiableAt (by simp)
  have hC' (z : Z) : θ (X z) = ParametricLayerCoefficients.planePhase covector ((p,ξ),X z) := by
    rw [planePhase_covector_eq,real_inner_comm]
    rfl
  have hF0 : F w = phase 1 ((p,ξ),x) := by
    simp only [F,phase,hC',hx,div_one]
  have hDepth : ∀ᶠ z : Z in 𝓝 w, |(polarReadout C.pole z).2| < C.δ := by
    have h := ((polarReadout_contDiffOn C.pole).snd.continuousOn.continuousAt (e.open_target.mem_nhds hw)).abs
    apply h.eventually (eventually_lt_nhds ?_)
    change |(polarReadout C.pole (angularPoint C.pole x)).2| < C.δ
    rw [C.polarReadout_angularPoint,abs_zero]
    exact C.pos
  have hEq : (fun z => C.physicalDatum (fun q => a (q.1.1,q.2)) 1 ((p,ξ),z) * H (p,z))
      =ᶠ[𝓝 w] fun z => F z * B z := by
    filter_upwards [e.open_target.mem_nhds hw,hDepth] with z hz hdz
    have hzn : z ∈ (stereographicPolarCollar C.pole).target := hz
    simp only [physicalDatum,liftedAngularTrial,collarLift,ite_eq_left hzn,div_one,F,B,localRotationAmplitude]
    change (collarDepthCutoff C.δ (polarReadout C.pole z).2 : ℂ) *
      Complex.exp (Complex.I * (ParametricLayerCoefficients.planePhase covector ((p,ξ),X z) : ℝ)) *
        a (p,X z) * H (p,z) = _
    rw [collarDepthCutoff_one C.pos hdz.le,Complex.ofReal_one,one_mul,hC',mul_assoc]
  let hCLM := ((ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM).comp θ
  have hθ : HasFDerivAt (fun z => Complex.I * (θ (X z) : ℝ))
      (hCLM.comp (fderiv ℝ X w)) w := by
    have he : (fun z => Complex.I * (θ (X z) : ℝ)) = hCLM ∘ X := by
      funext z
      simp [hCLM]
    rw [he]
    exact hCLM.hasFDerivAt.comp w hD.hasFDerivAt
  have hF : HasFDerivAt F (F w • hCLM.comp (fderiv ℝ X w)) w := hθ.cexp
  have hB0 := (C.localRotationAmplitude_contDiffOn ha hH).contDiffAt
    ((hU.prod e.open_target).mem_nhds (show (p,w) ∈ U ×ˢ e.target from ⟨hp,hw⟩))
  have hB : HasFDerivAt B ((fderiv ℝ (C.localRotationAmplitude a H) (p,w)).comp
      (ContinuousLinearMap.inr ℝ P Z)) w :=
    ((hB0.differentiableAt (by simp)).hasFDerivAt.comp w (hasFDerivAt_prodMk_right p w))
  rw [hEq.fderiv_eq]
  change fderiv ℝ (F*B) w (rotationVector i j w) = _
  rw [(hF.mul hB).fderiv]
  rw [← hF0]
  have hMul (z : ℂ) : ContinuousLinearMap.mul ℝ ℂ Complex.I z = Complex.I * z := rfl
  simp only [localRotationLow,localRotationHigh,B,hCLM,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.inr_apply,ContinuousLinearMap.mul_apply,
    Complex.ofRealCLM_apply,smul_eq_mul,θ,innerSL_apply_apply,Complex.ofReal_mul,ContinuousLinearMap.add_apply, hMul, w, X]
  ring_nf
  rfl

theorem localRotation_zero_off_support {K : Set E} (hK : IsClosed K)
    {a : Q → ℂ} (ha₀ : ∀ (p : P) x, x ∉ K → a (p,x) = 0)
    (H : P × Z → ℂ) (i j : I (n+1)) (p : P) {x : E} (hx : x ∉ K) (ξ : E) :
    C.localRotationLow i j a H (p,x) = 0 ∧ C.localRotationHigh i j a H (p,x) ξ = 0 := by
  let w := angularPoint C.pole x
  have hw := C.angularPoint_mem_collar_target x
  have hR0 : ContinuousAt (fun z : Z => (polarReadout C.pole z).1) w :=
    ((polarReadout_contDiffOn C.pole).fst.continuousOn).continuousAt
      ((stereographicPolarCollar C.pole).open_target.mem_nhds hw)
  have hProj : ContinuousAt (fun q : P × Z => q.2) (p,w) := continuousAt_snd
  have hRec : (polarReadout C.pole w).1 = x := congrArg Prod.fst (C.polarReadout_angularPoint x)
  have hA : C.localRotationAmplitude a H =ᶠ[𝓝 (p,w)] 0 := by
    have hS := hK.isOpen_compl.mem_nhds hx
    rw [← hRec] at hS
    have hS' := hR0.preimage_mem_nhds hS
    filter_upwards [hProj.preimage_mem_nhds hS'] with z hz
    exact (congrArg (fun t => t * H z) (ha₀ z.1 _ hz)).trans (zero_mul _)
  have hZero : C.localRotationAmplitude a H (p,w) = 0 := hA.eq_of_nhds
  refine ⟨?_,?_⟩
  · change (fderiv ℝ (C.localRotationAmplitude a H) (p,w)) _ = 0
    rw [hA.fderiv_eq]
    simp
  · simp [localRotationHigh,hZero,w]

end SignedPoissonCollar
end CalderonPaper

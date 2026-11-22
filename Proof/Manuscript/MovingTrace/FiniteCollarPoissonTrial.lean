module

public import Proof.Manuscript.MovingTrace.CollarPoissonTransport
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 5800000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonPatch CalderonPatch.BoundaryLayer Set Metric Matrix
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

def cutoffWave (a : Q × E → ℂ) (M : ℕ) (h : ℝ) : ((Q × E) × ℝ) → ℂ :=
  C.coefficients.finiteWave a (collarDepthCutoff C.δ)
    (ParametricLayerCoefficients.planePhase covector) M h

def physicalTrial (a : Q × E → ℂ) (M : ℕ) (h : ℝ) : Q × Z → ℂ :=
  liftedAngularTrial C.pole (C.cutoffWave a M h)

def physicalDatum (a : Q × E → ℂ) (h : ℝ) : Q × Z → ℂ :=
  liftedAngularTrial C.pole fun q => collarDepthCutoff C.δ q.2 *
    Complex.exp (Complex.I * ((ParametricLayerCoefficients.planePhase covector q.1)/h : ℝ)) * a q.1

def physicalResidual (a : Q × E → ℂ) (M : ℕ) (h : ℝ) : Q × Z → ℂ :=
  cutTrialResidual (fun q => G.a (q.1.1,q.2)) (C.physicalTrial a M h) h

def trialSupport (Kx : Set E) : Set Z :=
  (stereographicPolarCollar C.pole) '' (Kx ×ˢ Icc (-2*C.δ) (2*C.δ))

def residualSupport (Kx : Set E) : Set Z :=
  (stereographicPolarCollar C.pole) '' (Kx ×ˢ Icc (-C.δ/2) (2*C.δ))

theorem depth_lt_one (q : (Q × E) × ℝ) (hq : q ∈ C.collarDomain) : q.2 < 1 :=
  hq.2.2.trans (by linarith [C.small])

theorem residualSupport_compact {Kx : Set E} (hKx : IsCompact Kx) :
    IsCompact (C.residualSupport Kx) :=
  (hKx.prod isCompact_Icc).image_of_continuousOn
    ((stereographicPolarCollar C.pole).continuousOn.mono (fun q hq => hq.2.2.trans_lt (by linarith [C.small])))

variable {K : Set ((P × X n) × X n)} (hK : IsClosed K) (hKU : K ⊆ baseDomain G)
variable (a : (P × X n) × X n → ℂ) (ha : ContDiffOn ℝ ∞ a (baseDomain G)) (ha₀ : ∀ q ∉ K, a q = 0)
variable {Kx : Set (X n)} (hKx : IsCompact Kx) (hKproj : ∀ q ∈ K, q.2 ∈ Kx)

include hK hKU ha ha₀ in
theorem cutoffWave_contDiff (M : ℕ) (h : ℝ) : ContDiff ℝ ∞ (C.cutoffWave a M h) :=
  C.coefficients.finiteWave_joint_contDiff (baseDomain_open (G := G)) hK hKU a ha ha₀
    (collarDepthCutoff C.δ) (collarDepthCutoff_contDiff C.δ)
    (ParametricLayerCoefficients.planePhase_contDiff covector_contDiff) M h

include hK hKU ha ha₀ hKx hKproj in
theorem physicalTrial_contDiff (M : ℕ) (h : ℝ) : ContDiff ℝ ∞ (C.physicalTrial a M h) := by
  apply liftedAngularTrial_contDiff C.pole (C.cutoffWave_contDiff hK hKU a ha ha₀ M h)
    (hKx.prod (isCompact_Icc (a := -2*C.δ) (b := 2*C.δ)))
  · exact fun q hq => hq.2.2.trans_lt (by linarith [C.small])
  · exact finiteWave_eq_zero_of_lon_or_depth C.coefficients
      (baseDomain_open (G := G)) hK a ha ha₀ hKproj C.pos _ M h

include hK ha ha₀ hKproj in
theorem physicalTrial_zero_off_support (M : ℕ) (h : ℝ) (p : Q) (z : Z)
    (hz : z ∉ C.trialSupport Kx) : C.physicalTrial a M h (p,z) = 0 :=
  collarLift_zero_off_image (stereographicPolarCollar C.pole)
    (fun q : Q × (E × ℝ) => C.cutoffWave a M h ((q.1,q.2.1),q.2.2))
    (finiteWave_eq_zero_of_lon_or_depth C.coefficients (baseDomain_open (G := G)) hK a ha ha₀
      hKproj C.pos (ParametricLayerCoefficients.planePhase covector) M h) (p,z) hz

theorem physicalTrial_eq_datum (M : ℕ) (h : ℝ) (p : Q) :
    EqOn (fun z => C.physicalTrial a M h (p,z)) (fun z => C.physicalDatum a h (p,z)) (standardSphere (n+1)) := by
  let e := stereographicPolarCollar C.pole
  intro z hz
  have hZ : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  unfold physicalTrial physicalDatum liftedAngularTrial
  by_cases hze : z ∈ (stereographicPolarCollar C.pole).target
  · simp only [collarLift,ite_eq_left hze]
    let x := (e.symm z).1
    have ht : (e.symm z).2 = 0 := by change 1 - ‖z‖ = 0; rw [hZ,sub_self]
    change C.cutoffWave a M h ((p,x),(e.symm z).2) =
      collarDepthCutoff C.δ (e.symm z).2 * Complex.exp (Complex.I *
        ((ParametricLayerCoefficients.planePhase covector (p,x))/h : ℝ)) * a (p,x)
    rw [ht,cutoffWave,C.coefficients.finiteWave_face a _ (collarDepthCutoff_one C.pos (by simp [C.pos.le] : |(0:ℝ)| ≤ C.δ))]
    simp [collarDepthCutoff_one C.pos (by simp [C.pos.le] : |(0:ℝ)| ≤ C.δ)]
  · simp [collarLift,hze]

include hK hKU ha ha₀ hKx hKproj in
theorem physicalResidual_contDiff (M : ℕ) {h : ℝ} (hh : 0 < h) :
    ContDiff ℝ ∞ (C.physicalResidual a M h) :=
  cutTrialResidual_contDiff (G.smoothA.comp ((contDiff_fst.fst).prodMk contDiff_snd))
    (C.physicalTrial_contDiff hK hKU a ha ha₀ hKx hKproj M h) hh

include hK a ha ha₀ hKx hKproj in
theorem physicalResidual_zero_off_support (M : ℕ) {h : ℝ} (hh : 0 < h) (hδ : h ≤ C.δ/2)
    (p : Q) (z : Z) (hz : z ∉ C.residualSupport Kx) : C.physicalResidual a M h (p,z) = 0 :=
  residual_cutTrialResidual_zero_off_signed_collar C.pole hKx C.pos (by linarith [C.small])
    (C.physicalTrial_zero_off_support hK a ha ha₀ hKproj M h) hh hδ p hz

theorem physicalResidual_eq_trial (M : ℕ) {h : ℝ} (hh : 0 < h) (p : Q) :
    EqOn (complexNegativeBallDivergence (fun z => G.a (p.1,z))
      (fun z => C.physicalTrial a M h (p,z))) (fun z => C.physicalResidual a M h (p,z))
      (ball (0:Z) 1) := by
  intro z hz
  exact (cutTrialResidual_eq_on_closedBall (fun q : Q × Z => G.a (q.1.1,q.2))
    (C.physicalTrial a M h) hh p (ball_subset_closedBall hz)).symm

include hK hKU a ha ha₀ hKx hKproj in
theorem physicalTrial_normal_readout (M : ℕ) {h : ℝ} (hh : h ≠ 0) (q : Q × E) :
    (h : ℂ) * (Complex.exp (Complex.I * ((ParametricLayerCoefficients.planePhase covector q)/h : ℝ)))⁻¹ *
      fderiv ℝ (fun z => C.physicalTrial a M h (q.1,z)) (angularPoint C.pole q.2) (angularPoint C.pole q.2) =
      ∑ j ∈ Finset.range (M+1), (h : ℂ)^j * (-C.coefficients.traceCoefficient a j q) :=
  scaled_dephased_outward_trial C.coefficients C.pole a (collarDepthCutoff C.δ)
    (collarDepthCutoff_hasDerivAt_zero C.pos)
    (collarDepthCutoff_one C.pos (by simp [C.pos.le] : |(0:ℝ)| ≤ C.δ))
    _ M hh (C.physicalTrial_contDiff hK hKU a ha ha₀ hKx hKproj M h) q.1 q.2

include hK hKU a ha ha₀ hKx hKproj in
/-- Carry the exact all-orders transport residual through the signed angular
collar. The forcing agrees with the trial equation throughout the ball. -/
theorem uniform_physicalResidual_bound
    {J : Set Q} (hJ : IsCompact J) (hJV : J ⊆ G.V ×ˢ ({0}ᶜ : Set E)) (M N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ h : ℝ, 0 < h → h ≤ C.δ/2 → ∀ p ∈ J, ∀ z : Z, ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (C.physicalResidual a M h) (p,z)‖ ≤
        B * (h⁻¹^N * (h^(M+1) * h⁻¹^(2*N+2))) := by
  let R := Kx ×ˢ Icc (-C.δ/2) (2*C.δ)
  let B := J ×ˢ Kx
  let Γ : Set ((Q × E) × ℝ) := {q | q.1.1 ∈ J ∧ (q.1.2,q.2) ∈ R}
  have hB : IsCompact B := hJ.prod hKx
  have hBU : B ⊆ baseDomain G := fun q hq => ⟨hJV hq.1,mem_univ _⟩
  have hR : IsCompact R := hKx.prod isCompact_Icc
  have hΓEq : Γ = B ×ˢ Icc (-C.δ/2) (2*C.δ) := by
    ext q
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,fun h => ⟨h.1.1,⟨h.1.2,h.2⟩⟩⟩
  have hΓ : IsCompact Γ := hΓEq.symm ▸ (hB.prod isCompact_Icc)
  have hΓseg : ∀ q ∈ Γ, ∀ s ∈ Icc (0:ℝ) 1, (q.1,s*q.2) ∈ C.collarDomain := by
    intro q hq s hs
    have hD : q.2 ∈ Icc (-C.δ/2) (2*C.δ) := hq.2.2
    have hP := C.pos
    refine ⟨⟨⟨(hJV hq.1).1,mem_univ _⟩,mem_univ _⟩,?_,?_⟩
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hD.1),
        mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ C.δ/2 by positivity)]
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hD.2),
        mul_nonneg (sub_nonneg.mpr hs.2) (show 0 ≤ 2*C.δ by positivity)]
  have hΓB : ∀ q ∈ Γ, q.1 ∈ B := fun q hq => ⟨hq.1,hq.2.1⟩
  have hSplit := splitOperatorLayerCoefficients_residual_envelope
    C.collarDomain_open (baseDomain_open (G := G)) C.baseFace (tangential G C.pole) C.split_smooth.1
    (fun q hq => collarTangential_symm (C.metric_posDef hq))
    (fun q hq => collarTangential_posDef (C.metric_posDef (C.baseFace hq)))
    (normalDrift G C.pole) C.split_smooth.2.1 (tangentialDrift G C.pole) C.split_smooth.2.2
    covector covector_contDiff (fun q hq => covector_ne_zero hq)
    hB hBU hK hKU a ha ha₀ hΓ hΓB hΓseg
    (collarDepthCutoff C.δ) (collarDepthCutoff_contDiff C.δ) C.pos
    (fun q hq ht => collarDepthCutoff_derivatives_zero C.pos ⟨hq.2.1,ht⟩) M N
  let W : Set (Q × Z) := (fun q : Q × Z => (q.1.1,q.2)) ⁻¹' G.U
  have hW : IsOpen W := G.openU.preimage (continuous_fst.fst.prodMk continuous_snd)
  refine exists_uniform_physical_residual_of_collar_model C.pole hW
    (fun q => G.g (q.1.1,q.2)) (fun q => G.a (q.1.1,q.2))
    (fun i j => (G.smoothG i j).comp (contDiff_fst.fst.prodMk contDiff_snd).contDiffOn (fun _ h => h))
    (fun q hq => G.posG _ hq) (fun q hq => G.eqCoeff _ hq)
    (C.physicalTrial a M) (C.physicalTrial_contDiff hK hKU a ha ha₀ hKx hKproj M)
    (C.cutoffWave a M) (C.cutoffWave_contDiff hK hKU a ha ha₀ M)
    (fun h p x t ht => liftedAngularTrial_value C.pole _ p x ht)
    hJ hR (fun q hq => hq.2.2.trans_lt (by linarith [C.small])) C.collarDomain_open
    (fun p hp q hq => by simpa only [one_mul] using hΓseg ((p,q.1),q.2) ⟨hp,hq⟩ 1 (by simp))
    (fun q hq => C.physical_mem hq) C.depth_lt_one
    (fun q hq => C.mixed q.1.1.1 hq.1.1.1 q.1.2 q.2 hq.2)
    (by linarith [C.small]) ?_ N (fun h => h^(M+1) * h⁻¹^(2*N+2)) (fun h hh _ => by positivity) ?_
  · exact fun h hh hhδ p z hz => C.physicalResidual_zero_off_support hK a ha ha₀ hKx hKproj M hh hhδ p z hz
  · exact hSplit

end SignedPoissonCollar
end CalderonPaper

module

public import Proof.Manuscript.MovingTrace.AnnularPoissonCorrection
public import Proof.Manuscript.MovingTrace.LocalRotationPlaneSymbol
public import Proof.Manuscript.MovingTrace.RadialVelocityPairingChart
public import Proof.Manuscript.MovingTrace.NormalizedPlaneAmplitude
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

def chartPlaneWave (ζ : E → ℂ) (p : P) (ξ : E) (z : Z) : ℂ :=
  C.physicalDatum (fun q => ζ q.2) 1 ((p,ξ),z)

theorem chartPlaneWave_contDiff {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ) {Kζ : Set E}
    (hKζ : IsCompact Kζ) (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) :
    ContDiff ℝ ∞ (fun q : Q × Z => C.chartPlaneWave ζ q.1.1 q.1.2 q.2) :=
  C.physicalDatum_contDiff (hζ.comp contDiff_snd) hKζ (fun _ => hζ₀) 1

theorem chartPlaneWave_value (ζ : E → ℂ) (p : P) (ξ x : E) :
    C.chartPlaneWave ζ p ξ (angularPoint C.pole x) = phase 1 ((p,ξ),x) * ζ x :=
  C.physicalDatum_chart _ 1 _ _

def chartWeight (A : SmoothRadialVelocity G) (q : Q) : ℝ :=
  A.weight (q.1,angularPoint C.pole q.2)

theorem chartWeight_contDiffOn (A : SmoothRadialVelocity G) :
    ContDiffOn ℝ ∞ (C.chartWeight A) (A.U ×ˢ univ) := by
  have hMap : ContDiff ℝ ∞ (fun q : Q => (q.1,angularPoint C.pole q.2)) :=
    contDiff_fst.prodMk ((angularPoint_contDiff C.pole).comp contDiff_snd)
  exact A.smoothW.comp hMap.contDiffOn (fun q hq => ⟨hq.1,
    A.sphere_mem ((stereographic' ((n+1)-1) C.pole).symm q.2).property⟩)

theorem chartWeight_ne_zero (A : SmoothRadialVelocity G) {p : P} (hp : p ∈ A.U) (x : E) :
    C.chartWeight A (p,x) ≠ 0 :=
  A.weight_ne_zero _ ⟨hp,A.sphere_mem ((stereographic' ((n+1)-1) C.pole).symm x).property⟩

def rawChartNormalAmplitude (A : SmoothRadialVelocity G) (q : Q) : ℂ :=
  ((⟪angularPoint C.pole q.2,A.velocity (q.1,angularPoint C.pole q.2)⟫_ℝ / C.chartWeight A q : ℝ) : ℂ)

theorem rawChartNormalAmplitude_contDiffOn (A : SmoothRadialVelocity G) :
    ContDiffOn ℝ ∞ (C.rawChartNormalAmplitude A) (A.U ×ˢ univ) := by
  have hw : ContDiff ℝ ∞ (fun q : Q => angularPoint C.pole q.2) :=
    (angularPoint_contDiff C.pole).comp contDiff_snd
  have hV : ContDiffOn ℝ ∞ (fun q : Q => A.velocity (q.1,angularPoint C.pole q.2)) (A.U ×ˢ univ) :=
    A.smoothV.comp (contDiff_fst.prodMk hw).contDiffOn
      (fun q hq => ⟨hq.1,A.sphere_mem ((stereographic' ((n+1)-1) C.pole).symm q.2).property⟩)
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hw.contDiffOn.inner ℝ hV).div (C.chartWeight_contDiffOn A)
      (fun q hq => C.chartWeight_ne_zero A hq.1 q.2))

/-- Extend the smooth velocity and the chart normal multiplier only for
the finite parametrix. They agree in spatial neighborhoods of every
selected sphere, and the input amplitude retains its angular support. -/
theorem exists_chart_velocity_plane_data (A : SmoothRadialVelocity G)
    {J : Set P} (hJ : IsCompact J) (hJU : J ⊆ A.U) {ζ : E → ℂ} (hζ : ContDiff ℝ ∞ ζ)
    {Kζ : Set E} (hKζ : IsCompact Kζ) (hζ₀ : ∀ x ∉ Kζ, ζ x = 0) :
    ∃ (U : Set P) (W : Set Z) (V : P × Z → Z) (a : Q → ℂ),
      IsOpen U ∧ J ⊆ U ∧ U ⊆ A.U ∧ IsOpen W ∧ standardSphere (n+1) ⊆ W ∧
      ContDiff ℝ ∞ V ∧ EqOn V A.velocity (U ×ˢ W) ∧
      ContDiff ℝ ∞ a ∧ (∀ (p : P) x, x ∉ Kζ → a (p,x) = 0) ∧
      ∀ p ∈ U, ∀ x, a (p,x) = ζ x * C.rawChartNormalAmplitude A (p,x) := by
  have hSp : IsCompact (standardSphere (n+1)) := isCompact_sphere _ _
  obtain ⟨V,hV,_,T,hT,hJT,hTA,hEqV⟩ := exists_contDiff_extension_near_compact
    (A.openU.prod A.openS) (hJ.prod hSp) (Set.prod_mono hJU A.sphere_mem) A.smoothV
  obtain ⟨U₁,W,hU₁,hW,hJU₁,hSW,hU₁W⟩ := generalized_tube_lemma hJ hSp hT hJT
  obtain ⟨b,hb,_,T',hT',hKT',hT'A,hEqB⟩ := exists_contDiff_extension_near_compact
    (A.openU.prod isOpen_univ) (hJ.prod hKζ) (Set.prod_mono hJU (subset_univ _))
    (C.rawChartNormalAmplitude_contDiffOn A)
  obtain ⟨U₂,D,hU₂,hD,hJU₂,hKD,hU₂D⟩ := generalized_tube_lemma hJ hKζ hT' hKT'
  let U := (A.U ∩ U₁) ∩ U₂
  let a (q : Q) := ζ q.2 * b q
  refine ⟨U,W,V,a,(A.openU.inter hU₁).inter hU₂,fun _ h => ⟨⟨hJU h,hJU₁ h⟩,hJU₂ h⟩,
    inter_subset_left.trans inter_subset_left,hW,hSW,hV,?_,
    (hζ.comp contDiff_snd).mul hb,fun p x hx => by simp [a,hζ₀ x hx],?_⟩
  · exact fun q hq => hEqV (hU₁W ⟨hq.1.1.2,hq.2⟩)
  · intro p hp x
    by_cases hx : x ∈ Kζ
    · exact congrArg (ζ x * ·) (hEqB (hU₂D ⟨hp.2,hKD hx⟩))
    · simp [a,hζ₀ x hx]

def rotationCoeff (V : P × Z → Z) (i j : I (n+1)) (q : P × Z) : ℂ :=
  ((q.2 i * V q j : ℝ) : ℂ)

theorem rotationCoeff_contDiff {V : P × Z → Z} (hV : ContDiff ℝ ∞ V) (i j : I (n+1)) :
    ContDiff ℝ ∞ (rotationCoeff V i j) :=
  Complex.ofRealCLM.contDiff.comp (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).mul
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hV))

def velocityPrincipalSymbol (A : SmoothRadialVelocity G) (χ ζ : E → ℂ)
    (q : Q) (ξ : E) : ℂ :=
  let ν := ‖ξ‖⁻¹ • ξ
  let w := angularPoint C.pole q.2
  (‖ξ‖ : ℂ) * (χ q.2 * ((C.coefficients.kappa ((q.1,ν),q.2) : ℂ) * ζ q.2 *
       (⟪w,A.velocity (q.1,w)⟫_ℝ : ℝ)) -
    χ q.2 * ∑ i, ∑ j, C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff A.velocity i j) q ν)

def actualVelocityChartSymbol (A : SmoothRadialVelocity G) (χ ζ : E → ℂ)
    (q : Q) (ξ : E) : ℂ :=
  χ q.2 * (dephase 1 ((q.1,ξ),q.2) *
    A.operator q.1 (C.chartPlaneWave ζ q.1 ξ) (angularPoint C.pole q.2))


end SignedPoissonCollar
end CalderonPaper

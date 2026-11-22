module

public import Proof.CalderonN.SmoothConormalTraceOperators
public import Proof.CalderonN.AdmittedNormalPoissonEquation

import Proof.CalderonN.AdmittedScaledVelocitySmooth
import Proof.CalderonN.FlatAngularAdjoint
import Mathlib.Tactic

/-! The Gauss formula for the frozen moving adjoint, expressed as a product
of smooth trace operators on the actual first-metric sphere. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon.SmoothSphereRotation TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

abbrev SmoothBallVelocity (dim : ℕ) := {V : X dim → X dim // ContDiff ℝ ∞ V}

@[expose] def smoothVelocityNormal (V : SmoothBallVelocity dim) : SmoothData dim :=
  ⟨fun z => ⟪z,V.1 z⟫_ℝ,contDiff_id.inner ℝ V.2⟩

@[expose] def smoothVelocityAngular (V : SmoothBallVelocity dim) (i j : I dim) : SmoothData dim :=
  ⟨fun z => z i*V.1 z j,(EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.mul
    ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp V.2)⟩

@[expose] def smoothSphereVelocityTangent (V : SmoothBallVelocity dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  ∑ i,∑ j,smoothSphereTraceRotation i j*smoothSphereTraceMul (smoothVelocityAngular V i j)

@[expose] def smoothSphereGaussAdjoint (N : Module.End ℝ (SmoothSphereTrace dim))
    (V : SmoothBallVelocity dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  N*smoothSphereTraceMul (smoothVelocityNormal V)-smoothSphereVelocityTangent V

theorem smoothSphereVelocityTangent_apply (V : SmoothBallVelocity dim) (f : SmoothData dim)
    (z : ↥(standardSphere dim)) :
    (smoothSphereVelocityTangent V (smoothSphereTrace f)).1 z =
      ∑ i,∑ j,sphereRotationDerivative i j (fun x => f.1 x*(x i*V.1 x j)) z := by
  unfold smoothSphereVelocityTangent
  simp only [LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (smoothSphereTraceRotation i j (smoothSphereTraceMul (smoothVelocityAngular V i j)
    (smoothSphereTrace f))).1 z = _
  let m := smoothVelocityAngular V i j
  let u : SmoothData dim := ⟨fun x => f.1 x*m.1 x,f.2.mul m.2⟩
  have hMul : smoothSphereTraceMul m (smoothSphereTrace f) = smoothSphereTrace u := by
    apply Subtype.ext
    funext w
    rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
    exact mul_comm _ _
  change (smoothSphereTraceRotation i j (smoothSphereTraceMul m (smoothSphereTrace f))).1 z = _
  rw [hMul,smoothSphereTraceRotation_apply,smoothSphereTrace_apply]
  rfl

theorem admitted_smoothSphereGaussAdjoint_eq
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ)
    (i : I dim) {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (hAa : EqOn A (fun z => firstNormalVelocityCoefficient d y
      (d.radius y • frameVector d.frame y z)) (ball (0 : X dim) 1))
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim, ConormalTaylorSolutions A ell f)
    (W WI : SmoothData dim)
    (hW : EqOn W.1 (firstNormalRadialWeight d y (d.radius y)) (standardSphere dim))
    (hWI : EqOn WI.1 (fun z => (W.1 z)⁻¹) (standardSphere dim))
    (V : SmoothBallVelocity dim)
    (hV : EqOn V.1 (fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y)
      (fderiv ℝ d.radius y (axis i)) z (axis i)) (standardSphere dim))
    (fR fI : SmoothData dim)
    (hfR : EqOn fR.1 (fun z => (v (y,frameVector d.frame y z)).re) (standardSphere dim))
    (hfI : EqOn fI.1 (fun z => (v (y,frameVector d.frame y z)).im) (standardSphere dim)) :
    let N := smoothSphereTraceMul W *
      ((LinearMap.fst ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S)) * smoothSphereTraceMul WI
    ∀ z : ↥(standardSphere dim),
      (d.radius y : ℂ)*adjointField d.adjoint i v (y,frameVector d.frame y z) =
        ⟨(smoothSphereGaussAdjoint N V (smoothSphereTrace fR)).1 z,
         (smoothSphereGaussAdjoint N V (smoothSphereTrace fI)).1 z⟩ := by
  dsimp only
  let r := d.radius y
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let V₀ (z : X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y r
    (fderiv ℝ d.radius y (axis i)) z (axis i)
  let ψ (z : X dim) := v (y,frameVector d.frame y z)
  let W₀ := firstNormalRadialWeight d y r
  let N := smoothSphereTraceMul W *
    ((LinearMap.fst ℝ _ _).comp (smoothSphereTaylorResponses hA hEll S)) * smoothSphereTraceMul WI
  obtain ⟨bR,bI,hbR,hbI,hGauss⟩ := admitted_gauss_radial_trace_adjoint hn hY hΩ hd hK hy hrρ i hv
  obtain ⟨U,hU,hBU,hV₀,_⟩ := exists_admitted_scaledVelocity_smooth hd hy hrρ (axis i)
    (fderiv ℝ d.radius y (axis i))
  obtain ⟨T,hT,hBT,hvT⟩ := hv
  let ζ (z : X dim) := (y,frameVector d.frame y z)
  have hζ : ContDiff ℝ ∞ ζ := by
    simp only [ζ,← frameVectorLinear_apply]
    exact contDiff_const.prodMk (frameVectorLinear d.frame y).contDiff
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hζ' (z : X dim) (hz : z ∈ standardSphere dim) : ζ z ∈ T :=
    hBT ⟨hy,frameVector_mem_sphere d.γ d.frame y hFrame ⟨z,hz⟩⟩
  have hSide (p : ℂ → ℝ) (hp : ContDiff ℝ ∞ p) (f : SmoothData dim)
      (hf : EqOn f.1 (p ∘ ψ) (standardSphere dim))
      (b : X dim → ℝ) (hb : FixedBallSolution g
        (fun z => p (ψ z)*⟪z,V₀ z⟫_ℝ/W₀ z) b) (z : ↥(standardSphere dim)) :
      (smoothSphereGaussAdjoint N V (smoothSphereTrace f)).1 z =
        W₀ z*fderiv ℝ b z z -
          ∑ j,∑ k,sphereRotationDerivative j k (fun x => p (ψ x)*(x j*V₀ x k)) z := by
    let h := smoothDataMul WI (smoothDataMul (smoothVelocityNormal V) f)
    let q := S h
    let b' : SmoothData dim := ⟨b,hb.1⟩
    have hTrace : EqOn q.actual.1 b (standardSphere dim) := by
      intro x hx
      rw [show q.actual.1 x = h.1 x from q.actualTrace hx,
        show b x = p (ψ x)*⟪x,V₀ x⟫_ℝ/W₀ x from hb.2.1 hx]
      change WI.1 x*(⟪x,V.1 x⟫_ℝ*f.1 x) = _
      rw [hWI hx]
      change (W.1 x)⁻¹*(⟪x,V.1 x⟫_ℝ*f.1 x) = _
      rw [hW hx,hV hx,hf hx]
      simp only [Function.comp_apply,div_eq_mul_inv]
      ring
    have hH : EqOn (negativeBallDivergence A b) 0 (ball (0 : X dim) 1) := by
      have hDiv := (admitted_fixedBallSolution_iff_normalDivergence hΩ hd hK hy hrρ
        b' (fun x => p (ψ x)*⟪x,V₀ x⟫_ℝ/W₀ x)).mp hb
      intro x hx
      have hAg : A =ᶠ[𝓝 x] fun w => firstNormalVelocityCoefficient d y
          (r • frameVector d.frame y w) := by
        filter_upwards [isOpen_ball.mem_nhds hx] with w hw using hAa hw
      rw [negativeBallDivergence_congr_germ hAg EventuallyEq.rfl]
      exact hDiv.2 hx
    have hSame := eqOn_closedUnitBall_of_equal_ball_forcing hA hEll (fun _ _ => rfl) q.actual b'
      (fun x hx => (q.actualEquation hx).trans (hH hx).symm) hTrace
    have hRad := eqOn_radialDerivative_of_eqOn_closedUnitBall hSame z.2
    have hMul (m u : SmoothData dim) : smoothSphereTraceMul m (smoothSphereTrace u) =
        smoothSphereTrace (smoothDataMul m u) := by
      apply Subtype.ext
      funext w
      rw [smoothSphereTraceMul_apply,smoothSphereTrace_apply,smoothSphereTrace_apply]
      rfl
    change (N (smoothSphereTraceMul (smoothVelocityNormal V) (smoothSphereTrace f))).1 z-
      (smoothSphereVelocityTangent V (smoothSphereTrace f)).1 z = _
    rw [hMul,smoothSphereVelocityTangent_apply]
    have hNorm : (N (smoothSphereTrace (smoothDataMul (smoothVelocityNormal V) f))).1 z =
        W₀ z*fderiv ℝ b z z := by
      change (smoothSphereTraceMul W ((smoothSphereTaylorResponses hA hEll S
        (smoothSphereTraceMul WI (smoothSphereTrace (smoothDataMul (smoothVelocityNormal V) f)))).1)).1 z = _
      rw [hMul,smoothSphereTaylorResponses_apply,smoothSphereTraceMul_apply,smoothSphereTrace_apply,hW z.2]
      change W₀ z*fderiv ℝ q.actual.1 z z = _
      exact congrArg (W₀ z * ·) hRad
    rw [hNorm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hDiffV : ContDiffAt ℝ ∞ V₀ z :=
      hV₀.contDiffAt (hU.mem_nhds (hBU (sphere_subset_closedBall z.2)))
    have hDiffψ : ContDiffAt ℝ ∞ ψ z :=
      (hvT.contDiffAt (hT.mem_nhds (hζ' z z.2))).comp z.1 hζ.contDiffAt
    let jL := EuclideanSpace.proj (𝕜:=ℝ) j
    let kL := EuclideanSpace.proj (𝕜:=ℝ) k
    apply sphereRotationDerivative_congr_of_eqOn_sphere z.2
      ((f.2.mul (smoothVelocityAngular V j k).2).differentiable (by simp) z) ?_ ?_ j k
    · exact ((hp.contDiffAt.comp z.1 hDiffψ).mul
        (jL.contDiff.contDiffAt.mul (kL.contDiff.contDiffAt.comp z.1 hDiffV))).differentiableAt (by simp)
    · intro x hx
      change f.1 x*(x j*V.1 x k) = p (ψ x)*(x j*V₀ x k)
      rw [hV hx,hf hx]
      rfl
  intro z
  rw [hGauss z z.2]
  apply Complex.ext
  · exact (hSide Complex.re Complex.reCLM.contDiff fR hfR bR hbR z).symm
  · exact (hSide Complex.im Complex.imCLM.contDiff fI hfI bI hbI z).symm

end CalderonN

module

public import Proof.CalderonN.SupportedMovingTrace
public import Proof.CalderonN.ActualAdjointAffineNormalForm

import Proof.CalderonN.ActualAngularRadialWeights
import Proof.CalderonN.AdmittedScaledVelocitySmooth
import Proof.CalderonN.NormalizedCoefficientLifts
import Proof.CalderonN.ActualConormalRadialRow
import Proof.CalderonN.BallRegularity.UniformStrongInverse
import Proof.CalderonN.CompactSmoothExtension
import Mathlib.Tactic

/-! The actual physical Gauss adjoints as endomorphisms of smooth
sphere traces, with smooth compactly supported section lifts. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ActualGaussFiberData (d : Data dim) (y : X dim) where
  coefficient : X dim → Mat dim
  smoothCoefficient : ContDiff ℝ ∞ coefficient
  coefficientEq : EqOn coefficient (fun z => firstNormalVelocityCoefficient d y
    (d.radius y • frameVector d.frame y z)) (ball (0:X dim) 1)
  lo : ℝ
  hi : ℝ
  ellipticCoefficient : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) coefficient lo hi
  solve : ∀ f : SmoothData dim, ConormalTaylorSolutions coefficient (firstDensityCenterLinear d y) f
  weight : SmoothData dim
  reciprocal : SmoothData dim
  weightConormal : ∀ u : SmoothData dim, EqOn (smoothBallConormal coefficient u.1)
    (fun z => weight.1 z*fderiv ℝ u.1 z z) (standardSphere dim)
  weightEq : EqOn weight.1 (firstNormalRadialWeight d y (d.radius y)) (standardSphere dim)
  reciprocalEq : EqOn reciprocal.1 (fun z => (weight.1 z)⁻¹) (standardSphere dim)
  velocity : I dim → SmoothBallVelocity dim
  velocityEq : ∀ i, EqOn (velocity i).1
    (fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y)
      (fderiv ℝ d.radius y (axis i)) z (axis i)) (standardSphere dim)

@[expose] def ActualGaussFiberData.adjoint {d : Data dim} {y : X dim}
    (F : ActualGaussFiberData d y) (i : I dim) : Module.End ℝ (SmoothSphereTrace dim) :=
  let N := smoothSphereTraceMul F.weight *
    ((LinearMap.fst ℝ _ _).comp (smoothSphereTaylorResponses F.smoothCoefficient F.ellipticCoefficient F.solve)) *
    smoothSphereTraceMul F.reciprocal
  (d.radius y)⁻¹ • smoothSphereGaussAdjoint N (F.velocity i)

theorem ActualGaussFiberData.adjoint_apply_physical
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) (F : ActualGaussFiberData d y)
    (i : I dim) {v : Field dim} (hv : smoothNear v (bundle Y d.γ))
    (fR fI : SmoothData dim)
    (hfR : EqOn fR.1 (fun z => (v (y,frameVector d.frame y z)).re) (standardSphere dim))
    (hfI : EqOn fI.1 (fun z => (v (y,frameVector d.frame y z)).im) (standardSphere dim))
    (z : UnitSphere dim) :
    adjointField d.adjoint i v (y,frameVector d.frame y z) =
      ⟨(F.adjoint i (smoothSphereTrace fR)).1 z,(F.adjoint i (smoothSphereTrace fI)).1 z⟩ := by
  have hEq := admitted_smoothSphereGaussAdjoint_eq hn hY hΩ hd hK hy hrρ i hv
    F.smoothCoefficient F.coefficientEq F.ellipticCoefficient F.solve F.weight F.reciprocal
    F.weightEq F.reciprocalEq (F.velocity i) (F.velocityEq i) fR fI hfR hfI z
  have hr : (d.radius y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd.2.2.2.2.1.2 y hy).1.ne'
  have hR := congrArg (fun b : ℂ => (d.radius y : ℂ)⁻¹*b) hEq
  rw [← mul_assoc,inv_mul_cancel₀ hr,one_mul] at hR
  rw [hR]
  apply Complex.ext
  · simp [ActualGaussFiberData.adjoint,Complex.mul_re]
  · simp [ActualGaussFiberData.adjoint,Complex.mul_im]

private theorem physicalTrace_component_has_sphere_extension
    {Y : Set (X dim)} {d : Data dim} {y : X dim} (hy : y ∈ Y)
    (hFrame : ∀ i j, metricPair d.γ y (d.frame y i) (d.frame y j) = if i=j then 1 else 0)
    {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) (L : ℂ →L[ℝ] ℝ) :
    ∃ f : SmoothData dim, EqOn f.1 (fun z => L (v (y,frameVector d.frame y z))) (standardSphere dim) := by
  let F (z : X dim) := (y,frameVectorLinear d.frame y z)
  have hF : ContDiff ℝ ∞ F := contDiff_const.prodMk (frameVectorLinear d.frame y).contDiff
  obtain ⟨U,hU,hBU,hS⟩ := hv
  have hB : standardSphere dim ⊆ F ⁻¹' U := by
    intro z hz
    apply hBU
    exact ⟨hy,by simpa only [F,frameVectorLinear_apply] using frameVector_mem_sphere d.γ d.frame y hFrame ⟨z,hz⟩⟩
  have hComp : ContDiffOn ℝ ∞ (fun z => L (v (F z))) (F ⁻¹' U) :=
    L.contDiff.comp_contDiffOn (hS.comp hF.contDiffOn (fun _ h => h))
  obtain ⟨f,hf,_,V,_,hSV,_,hEq⟩ := exists_contDiff_extension_near_compact
    (hU.preimage hF.continuous) (isCompact_sphere (0:X dim) 1) hB hComp
  exact ⟨⟨f,hf⟩,fun z hz => by simpa only [F,frameVectorLinear_apply] using hEq (hSV hz)⟩

theorem actualGaussFiber_matches
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (hrρ : ∀ y ∈ Y, 2*d.radius y < ρ)
    (F : ∀ y ∈ Y,ActualGaussFiberData d y) (i : I dim) :
    let C (y : X dim) := if hy : y ∈ Y then (F y hy).adjoint i else 0
    MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i C Complex.reCLM ∧
      MovingAdjointFiberMatches (Y:=Y) d.γ d.frame d.adjoint i C Complex.imCLM := by
  classical
  dsimp only
  constructor
  · intro v hv u hu x hx z
    dsimp only
    rw [dite_eq_left hx]
    obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
    let fR : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
    have hF := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
    obtain ⟨fI,hfI⟩ := physicalTrace_component_has_sphere_extension hx hF hv Complex.imCLM
    have hfR : EqOn fR.1 (fun w => (v (x,frameVector d.frame x w)).re) (standardSphere dim) :=
      fun w hw => (hRep x ⟨w,hw⟩).symm.trans (hu x hx ⟨w,hw⟩)
    have hRep' : smoothSupportedTraceFiberL x u = smoothSphereTrace fR := Subtype.ext (funext (hRep x))
    rw [hRep',(F x hx).adjoint_apply_physical hn hY hΩ hd hK hx (hrρ x hx) i hv fR fI hfR hfI z]
    rfl
  · intro v hv u hu x hx z
    dsimp only
    rw [dite_eq_left hx]
    obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
    let fI : SmoothData dim := ⟨fun w => G (x,w),hG.comp (contDiff_const.prodMk contDiff_id)⟩
    have hF := hd.1.2.2.2.2.2.2.2 x (hd.2.1.center_mem hx)
    obtain ⟨fR,hfR⟩ := physicalTrace_component_has_sphere_extension hx hF hv Complex.reCLM
    have hfI : EqOn fI.1 (fun w => (v (x,frameVector d.frame x w)).im) (standardSphere dim) :=
      fun w hw => (hRep x ⟨w,hw⟩).symm.trans (hu x hx ⟨w,hw⟩)
    have hRep' : smoothSupportedTraceFiberL x u = smoothSphereTrace fI := Subtype.ext (funext (hRep x))
    rw [hRep',(F x hx).adjoint_apply_physical hn hY hΩ hd hK hx (hrρ x hx) i hv fR fI hfR hfI z]
    rfl


private theorem exists_gaussVelocityData
    {Y Ω : Set (X dim)} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) (i : I dim) :
    ∃ V : SmoothBallVelocity dim, EqOn V.1
      (fun z => scaledNormalTraceVelocity d.γ d.expMap d.frame y (d.radius y)
        (fderiv ℝ d.radius y (axis i)) z (axis i)) (standardSphere dim) := by
  obtain ⟨U,hU,hBU,hV,_⟩ := exists_admitted_scaledVelocity_smooth hd hy hrρ
    (axis i) (fderiv ℝ d.radius y (axis i))
  obtain ⟨V,hV',_,W,_,hBW,_,hEq⟩ := exists_contDiff_extension_near_compact hU
    (isCompact_closedBall (0:X dim) 1) hBU hV
  exact ⟨⟨V,hV'⟩,fun _ hz => hEq (hBW (sphere_subset_closedBall hz))⟩

private theorem gaussFiberWeight_eq_of_radial_form
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ)
    (A : X dim → Mat dim) (W : SmoothData dim)
    (hEq : EqOn A (fun z => firstNormalVelocityCoefficient d y
      (d.radius y • frameVector d.frame y z)) (ball (0:X dim) (5/4)))
    (hW : ∀ u : SmoothData dim, EqOn (smoothBallConormal A u.1)
      (fun z => W.1 z*fderiv ℝ u.1 z z) (standardSphere dim)) :
    EqOn W.1 (firstNormalRadialWeight d y (d.radius y)) (standardSphere dim) := by
  intro z hz
  let r := d.radius y
  let a (z : X dim) := firstNormalVelocityCoefficient d y (r • frameVector d.frame y z)
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hw := frameVector_mem_disk d.γ d.frame y z 1 hFrame (sphere_subset_closedBall hz)
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hv : r • frameVector d.frame y z ∈ interior (disk d.γ y (max ρ r)) := by
    apply mem_interior_disk_of_metricPair_lt
    rw [metricPair_smul_left,metricPair_smul_right]
    have hw' : metricPair d.γ y (frameVector d.frame y z) (frameVector d.frame y z) ≤ 1 := by
      simpa only [disk,one_pow,mem_setOf_eq] using hw
    have hLt : r^2 < (max ρ r)^2 := by
      apply (sq_lt_sq₀ hr.le (hr.le.trans (le_max_right _ _))).2
      exact (show r < ρ by linarith).trans_le (le_max_left _ _)
    calc
      _ = r^2*metricPair d.γ y (frameVector d.frame y z) (frameVector d.frame y z) := by ring
      _ ≤ r^2 := (mul_le_mul_of_nonneg_left hw' (sq_nonneg r)).trans_eq (mul_one _)
      _ < _ := hLt
  let ℓ : X dim →L[ℝ] ℝ := innerSL ℝ z
  let u : SmoothData dim := ⟨ℓ,ℓ.contDiff⟩
  have hD : fderiv ℝ u.1 z z = 1 := by
    change fderiv ℝ (⇑ℓ) z z = 1
    rw [ℓ.fderiv]
    change ⟪z,z⟫_ℝ = 1
    rw [real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp hz,one_pow]
  have hF : smoothBallFlux A u.1 z = smoothBallFlux a u.1 z := by
    have hEqz := hEq (closedBall_subset_ball (by norm_num : (1:ℝ) < 5/4) (sphere_subset_closedBall hz))
    ext k
    simp only [smoothBallFlux_apply,hEqz,a,r]
  have hActual := hd.inner_actualNormalFlux_radial_row hn hΩ hK hy hr.ne' z hv u.1
  have hTest := hW u hz
  change smoothBallConormal A u.1 z = W.1 z*fderiv ℝ u.1 z z at hTest
  rw [smoothBallConormal,hF,hActual,hD,mul_one,mul_one] at hTest
  exact hTest.symm

theorem uniform_exists_actualGaussFiberData
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, Nonempty (ActualGaussFiberData d y) := by
  obtain ⟨η,_,_,hη,_,_,hCoeff⟩ := uniform_normalized_coefficient_lifts (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηW,_,hηW,_,hWeight⟩ := uniform_actual_angular_radial_weights (Y:=Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨F₀,hF₀⟩ := exists_flatCoefficientMatrix dim 2
  let τ := min (min η ηW) (ρ/4)
  refine ⟨τ,lt_min (lt_min hη hηW) (by positivity),?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let r := d.radius y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hb)).trans (hd.2.2.2.2.2 y hy).2
  have hrρ : 2*r < ρ := by
    have hh := hrε.trans (hSmall.trans (min_le_right _ _))
    linarith
  obtain ⟨F,F₁,hEq,_,_,_,lo,hi,hEll⟩ := hCoeff F₀ hF₀ floor hf ε hε
    (hSmall.trans ((min_le_left _ _).trans (min_le_left _ _))) d hd y hy
  let A := coefficientMatrixField 2 F
  have hA : ContDiff ℝ ∞ A := contDiff_coefficientMatrixField 2 F
  obtain ⟨_,W,D,WI,hW,_,hWI,_⟩ := hWeight floor hf ε hε
    (hSmall.trans ((min_le_left _ _).trans (min_le_right _ _))) d hd y hy A hA hEq
  let S (f : SmoothData dim) := Classical.choice (exists_conormalTaylorSolutions_of_extension F F₀ hF₀
    (show EqOn (coefficientMatrixField 2 F) A (ball (0:X dim) 1) from fun _ _ => rfl)
    hEll (firstDensityCenterLinear d y) f)
  have hW' := gaussFiberWeight_eq_of_radial_form hn hΩ hd (zero_lt_one.trans_le hK) hy hrρ A W hEq hW
  have hWI' : EqOn WI.1 (fun z => (W.1 z)⁻¹) (standardSphere dim) := by
    intro z hz
    have hProd := (hWI z (sphere_subset_closedBall hz)).1
    have hNonzero : W.1 z ≠ 0 := by
      intro h
      rw [h,mul_zero] at hProd
      exact zero_ne_one hProd
    simpa only [one_div] using (eq_div_iff hNonzero).2 hProd
  choose V hV using fun i => exists_gaussVelocityData hd hy hrρ i
  exact ⟨⟨A,hA,hEq.mono (ball_subset_ball (by norm_num)),lo,hi,hEll,S,W,WI,hW,hW',hWI',V,hV⟩⟩

end CalderonN

module

public import Proof.CalderonN.TraceCoordinateLowerOrderBounds
public import Proof.CalderonN.TraceCoordinateModelCommBounds
public import Proof.CalderonN.PhysicalTraceLowerOrderMass

import Mathlib.Tactic

/-! Assemble the actual lower-order operator from its four fiber
pieces. The profile makes the base derivative cost harmless after the
physical radius factor is restored. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

theorem actualSupportedMovingTrace_lowerOrder_fiber_bound
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair d.γ x (d.frame x i) (d.frame x j) = if i=j then 1 else 0)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
    (hb : ∀ k,ContDiffOn ℝ ∞ (fun x => drift d.γ d.g₂ x k) Y)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    {x : X dim} (hx : x ∈ Y) {β C D U : ℝ} (hβ : 1 ≤ β)
    (hCp : 0 ≤ C) (hDp : 0 ≤ D) (hUp : 0 ≤ U) (hrp : 0 ≤ d.radius x) (hR : d.radius x*β ≤ 1)
    (hQ₁ : ∀ i j, |principal d.γ d.g₂ x i j| ≤ D)
    (hk : ∀ i, |traceCoordinateDrift d.γ d.g₂ i x| ≤ D)
    (hEntry : ∀ i a, |traceFrameCoordinate d.γ d.frame a i x| ≤ D)
    (hDEntry : ∀ i j a, |coordDeriv i (traceFrameCoordinate d.γ d.frame a j) x| ≤ D)
    (hΓ : ∀ i a b, |frameConnectionCoefficient d.γ d.frame x (axis i) a b| ≤ D)
    (hl : ∀ i, |traceCoordinateLogGradient d.radius i x| ≤ D*β)
    (hRaise : ∀ a : I dim, SmoothTraceAngularBound hn 1 C
      (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) a))
    (hAffine : ∀ i,SupportedTraceFiberBound hn x 0 U (actualSupportedAffine hY F hF i))
    (G : I dim → X dim → Module.End ℝ (SmoothSphereTrace dim))
    (hG : ∀ i,SmoothSupportedTraceFiberRegular Y (G i))
    (hAdj : ∀ i y, y ∈ Y → SmoothTraceAdjoint hn (actualGaussLowerVelocityFamily F i y) (G i y))
    (hW : ∀ i,SmoothSupportedTraceCoefficientBounds hn (smoothTraceFlatDegree hA hEll S) hY x β 1 U
      (actualGaussLowerVelocityFamily F i) (actualGaussLowerVelocityFamily_regular hY hg he hr hr₀ hlog hA hEll S F hC hF hn i)) :
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let b := supportedCoordinateTraceDrift hY hg hK hr hQ hb
    let V := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let P := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let F₁ := actualSupportedAffine hY F hF
    let R := (dim:ℝ)*(D*C)
    let T := (dim:ℝ)*(D*C+D*R)
    let W := U+(dim:ℝ)^2*(D*U)+D*U
    SupportedTraceFiberBound hn x 1 ((dim:ℝ)^2*(D*(T+(R*U+U*R))+D*W)+(dim:ℝ)*(D*R))
      (movingTraceLowerOrder a b V P E F₁) := by
  dsimp only
  rw [actualSupportedMovingTrace_lowerOrder_cancel_radius hn hY hg hK he hr hr₀ hlog hQ hb hA hEll S F hC hF]
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let P := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
  let H := supportedCoordinateHorizontal hY hg hK he
  let R := supportedCoordinateRaising hY hg he hA hEll S
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let F₁ := actualSupportedAffine hY F hF
  let R₀ := (dim:ℝ)*(D*C)
  let T₀ := (dim:ℝ)*(D*C+D*R₀)
  let W₀ := U+(dim:ℝ)^2*(D*U)+D*U
  have hR₀ : 0 ≤ R₀ := by dsimp only [R₀]; positivity
  have hT₀ : 0 ≤ T₀ := by dsimp only [T₀,R₀]; positivity
  have hW₀ : 0 ≤ W₀ := by dsimp only [W₀]; positivity
  have hR₁ (i : I dim) : SupportedTraceFiberBound hn x 1 R₀ (R i) :=
    supportedCoordinateRaising_fiber_bound hn hY hg he hA hEll S hx C D hCp hRaise hEntry i
  have hH (i j : I dim) : SupportedTraceFiberBound hn x 1 T₀ (H i*R j-R j*H i) :=
    supportedCoordinateHorizontal_comm_raising_bound hn hY hg hK he hA hEll S hframe
      hx C D hCp hDp hRaise hEntry hDEntry hΓ i j
  have hTerm (i j : I dim) : SupportedTraceFiberBound hn x 1 (D*(T₀+(R₀*U+U*R₀)))
      (smoothSupportedTraceBaseMul hY (fun y => principal d.γ d.g₂ y i j) (hQ i j) *
        ((H i*R j-R j*H i)+(R i*F₁ j+F₁ i*R j))) := by
    have h₁ : SupportedTraceFiberBound hn x 1 (R₀*U) (R i*F₁ j) :=
      (hR₁ i).mul (hAffine j) hR₀
    have h₂ : SupportedTraceFiberBound hn x 1 (U*R₀) (F₁ i*R j) :=
      (hAffine i).mul (hR₁ j) hUp
    exact (((hH i j).add (h₁.add h₂)).base_mul hY _ (hQ i j)).enlarge
      (mul_le_mul_of_nonneg_right (hQ₁ i j) (by positivity))
  have hComm (i j : I dim) : SupportedTraceFiberBound hn x 1 (W₀*β)
      (P i*(E j+F₁ j)-(E j+F₁ j)*P i) := by
    change SupportedTraceFiberBound hn x 1 (W₀*β) _
    have heq := actualSupportedGaussLowerVelocity_eq_action hY hg he hr hr₀ hlog hA hEll S F hC hF hn j
    change E j+F₁ j = _ at heq
    rw [heq]
    exact supportedCoordinateModelDerivative_comm_fiber_bound hn hY hg hK he hlog hA hEll S hx hβ hDp
      _ (G j) _ (hG j) (hAdj j) (hW j) i (hΓ i) (hl i)
  have hPert (i j : I dim) : SupportedTraceFiberBound hn x 1 (D*W₀)
      (a i j*(P i*(E j+F₁ j)-(E j+F₁ j)*P i)) := by
    have h := (hComm i j).base_mul hY (fun y => d.radius y*principal d.γ d.g₂ y i j) (hr.mul (hQ i j))
    apply h.enlarge
    rw [abs_mul,abs_of_nonneg hrp]
    calc
      _ = (d.radius x*β)*(|principal d.γ d.g₂ x i j| * W₀) := by ring
      _ ≤ 1*(D*W₀) := mul_le_mul hR (mul_le_mul_of_nonneg_right (hQ₁ i j) hW₀) (by positivity) zero_le_one
      _ = _ := one_mul _
  have hDrift (i : I dim) : SupportedTraceFiberBound hn x 1 (D*R₀)
      (smoothSupportedTraceBaseMul hY (traceCoordinateDrift d.γ d.g₂ i)
        (contDiffOn_traceCoordinateDrift hY hg hK hQ hb i)*R i) :=
    ((hR₁ i).base_mul hY _ _).enlarge (mul_le_mul_of_nonneg_right (hk i) hR₀)
  have hSum {T : I dim → I dim → Module.End ℝ (SmoothSupportedTraceSection Y)} {s : ℝ}
      (h : ∀ i j,SupportedTraceFiberBound hn x 1 s (T i j)) :
      SupportedTraceFiberBound hn x 1 ((dim:ℝ)^2*s) (∑ i,∑ j,T i j) := by
    have hh := SupportedTraceFiberBound.sum Finset.univ (fun i : I dim => ∑ j,T i j)
      (fun _ => ∑ _j : I dim,s) (fun i _ => SupportedTraceFiberBound.sum Finset.univ (T i)
        (fun _ => s) (fun j _ => h i j))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,pow_two,mul_assoc] using hh
  have hLast := SupportedTraceFiberBound.sum Finset.univ _ (fun _ : I dim => D*R₀) (fun i _ => hDrift i)
  have hAll := ((hSum hTerm).add (hSum hPert)).add hLast
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hAll
  have hEq : (dim:ℝ)^2*(D*(T₀+(R₀*U+U*R₀)))+(dim:ℝ)^2*(D*W₀)+(dim:ℝ)*(D*R₀) =
      (dim:ℝ)^2*(D*(T₀+(R₀*U+U*R₀))+D*W₀)+(dim:ℝ)*(D*R₀) := by ring
  rw [hEq] at hAll
  exact hAll

end CalderonN

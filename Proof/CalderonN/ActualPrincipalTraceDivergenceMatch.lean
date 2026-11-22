module

public import Proof.CalderonN.ActualPrincipalTraceNormalMatch

import Mathlib.Tactic

/-! The drift-free physical perturbation equals the implemented
coordinate divergence form. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4650000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

private theorem divergence_sum_cancel {R ι : Type*} [Ring R] [Fintype ι]
    (P Q C : ι → ι → R) (B D : ι → R) (h : ∀ i j,P i j = Q i j+C i j*D j) :
    (∑ i,∑ j,P i j)+(∑ j,(B j-(∑ i,C i j))*D j) =
      (∑ i,∑ j,Q i j)+(∑ j,B j*D j) := by
  simp only [h,Finset.sum_add_distrib,sub_mul,Finset.sum_mul]
  rw [Finset.sum_sub_distrib (fun j => B j*D j) (fun j => ∑ i,C i j*D j)]
  rw [Finset.sum_comm (f := fun i j => C i j*D j)]
  abel

theorem actual_principalTrace_divergence_match
    (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
    (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
    (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
    (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y) (hg₂ : SmoothMetric Y d.g₂)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
    (F : ∀ x ∈ Y,ActualGaussFiberData d x)
    (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
    (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))
    (V : ActualTraceVelocityFactors hn Y) (hV : ∀ x (hx : x ∈ Y),V.Matches (F x hx)) :
    let P := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    let a := supportedPrincipalTraceCoeff hY hr hQ
    let g := supportedReferenceTraceCoeff hY hg hK hr
    let R := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
    let D := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
    let G := actualSupportedAffine hY F hF
    (P.divergence hY).action hY = movingTracePerturbation a (a-g) 0 R D E G := by
  dsimp only
  let P := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
  let U := P.divergence hY
  let a := supportedPrincipalTraceCoeff hY hr hQ
  let g := supportedReferenceTraceCoeff hY hg hK hr
  let R := supportedLeadingTraceVelocity hY hg he hr hr₀ hA hEll S
  let H := supportedCoordinateModelDerivative hY hg hK he hlog hA hEll S
  let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF
  let G := actualSupportedAffine hY F hF
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let K₀ := supportedCoordinateModelPotential hY hg hK he hA hEll S hlog
  let K₁ := supportedCoordinateModelPotentialDerivative hY hg hK he hA hEll S hlog
  change U.action hY = movingTracePerturbation a (a-g) 0 R H E G
  have hH : H = D+K₀ :=
    funext (supportedCoordinateModelDerivative_eq_base_add_potential hY hg hK he hA hEll S hlog)
  rw [hH,movingTracePerturbation_base_normal _ _ _ _ _ _ _ _ _
    (supportedCoordinateModelPotential_comm_base hY hg hK he hA hEll S hlog hn)]
  obtain ⟨hFirst,hZero⟩ := actual_principalTrace_normalCoefficients_match hn hY hg hK he hr hr₀ hlog hQ hg₂
    hA hEll S F hC hF V hV
  let X (i j : I dim) := U.baseAdjoint hY i*(U.second i j).forward.action hY*D j
  let Y₀ (i j : I dim) := a i j*(D i*D j)
  let C (i j : I dim) := (P.principalDerivative i i j).forward.action hY+
    (P.density i).forward.action hY*a i j
  let B (i : I dim) := (P.firstNormal hY i).forward.action hY
  have hX (i j : I dim) : X i j = Y₀ i j+C i j*D j :=
    actualCoordinatePrincipalTrace_principal_normal hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V i j
  have hC' (j : I dim) : (U.first j).forward.action hY = B j-(∑ i,C i j) := by
    simp only [U,CoordinatePrincipalTraceFactors.divergence,CoordinatePrincipalTraceFactors.first,
      CoordinatePrincipalTraceFactors.densityAdjustment,PairedTraceFiberFamily.sub,PairedTraceFiberFamily.finiteSum,
      PairedTraceFiberFamily.add,PairedTraceFiberFamily.mul,RegularTraceFiberFamily.action_sub,
      RegularTraceFiberFamily.action_finiteSum,RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_mul]
    rfl
  change U.principal hY+(∑ i,(U.first i).forward.action hY*D i)+(P.zero hY).forward.action hY = _
  rw [hZero]
  have hSumC : (∑ i,(U.first i).forward.action hY*D i) = ∑ i,(B i-(∑ j,C j i))*D i :=
    Finset.sum_congr rfl (fun i _ => congrArg (· *D i) (hC' i))
  have hSumB : (∑ i,movingTraceFirstBaseCoeff a (a-g) 0 R K₀ E G i*D i) = ∑ i,B i*D i :=
    Finset.sum_congr rfl (fun i _ => congrArg (· *D i) (hFirst i).symm)
  rw [hSumC,hSumB]
  change (∑ i,∑ j,X i j)+(∑ j,(B j-(∑ i,C i j))*D j)+_ =
    (∑ i,∑ j,Y₀ i j)+(∑ i,B i*D i)+_
  rw [divergence_sum_cancel X Y₀ C B D hX]

end CalderonN

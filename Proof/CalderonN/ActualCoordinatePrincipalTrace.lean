module

public import Proof.CalderonN.CoordinatePrincipalTraceFactors
public import Proof.CalderonN.ActualPrincipalTraceScalarJets

import Proof.CalderonN.ActualMovingTraceBaseNormal
import Proof.CalderonN.PrincipalMetric
import Mathlib.Tactic

/-! The coordinate divergence form represents the genuine principal
perturbation after the direct drift split. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5300000
set_option maxSynthPendingDepth 29
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim} {d : Data dim}

variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
  (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
  (hQ : ∀ i j,ContDiffOn ℝ ∞ (fun x => principal d.γ d.g₂ x i j) Y)
  (hg₂ : SmoothMetric Y d.g₂)
  {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
  (V : ActualTraceVelocityFactors hn Y)

@[expose] def actualCoordinatePrincipalTraceFactors : CoordinatePrincipalTraceFactors hn Y where
  principal := fun i j => PairedTraceFiberFamily.scalar hY
    (fun x => d.radius x*principal d.γ d.g₂ x i j) (hr.mul (hQ i j))
  principalDerivative := fun k i j => PairedTraceFiberFamily.scalar hY
    (coordDeriv k (fun x => d.radius x*principal d.γ d.g₂ x i j))
    ((((hr.mul (hQ i j)).fderiv_of_isOpen (m:=∞) hY (by simp))).clm_apply contDiffOn_const)
  smallDifference := fun i j => PairedTraceFiberFamily.scalar hY (tracePrincipalSmallDifference d i j)
    (contDiffOn_tracePrincipalSmallDifference (hg.smoothMetric hK) hg₂ hr hr₀ i j)
  density := fun i => PairedTraceFiberFamily.scalar hY (traceDensityDivergence (metricDensity d.γ) (fun _ => axis i))
    (contDiffOn_traceDensityDivergence hY _ (hg.contDiffOn_density hK)
      (fun x hx => metricDensity_pos hg hK hx) _ contDiffOn_const)
  radius := PairedTraceFiberFamily.scalar hY d.radius hr
  model := actualCoordinateTraceModelFactors hY hg hK he hlog hA hEll S
  velocity := V

theorem actualCoordinatePrincipalTrace_baseAdjoint (i : I dim) :
    let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    PairedAdjoint (smoothSupportedTracePairingL hn hY (metricDensity d.γ) (hg.contDiffOn_density hK))
      (smoothSupportedTraceBaseDiff (axis i)) ((F.divergence hY).baseAdjoint hY i) :=
  coordinateTraceBaseAdjoint hn hY (metricDensity d.γ) (hg.contDiffOn_density hK)
    (fun x hx => metricDensity_pos hg hK hx) i

theorem actualCoordinatePrincipalTrace_scalar_comm (i j : I dim) (G : RegularTraceFiberFamily Y) :
    let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    G.action hY*((F.divergence hY).second i j).forward.action hY =
      ((F.divergence hY).second i j).forward.action hY*G.action hY := by
  dsimp only
  simp only [CoordinatePrincipalTraceFactors.divergence,actualCoordinatePrincipalTraceFactors,
    PairedTraceFiberFamily.neg,RegularTraceFiberFamily.action_neg]
  let a := PairedTraceFiberFamily.scalar (hn:=hn) hY (fun x => d.radius x*principal d.γ d.g₂ x i j)
    (hr.mul (hQ i j))
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  simp only [Module.End.mul_apply,LinearMap.neg_apply,map_neg,PairedTraceFiberFamily.scalar,
    PairedTraceFiberFamily.symmetric,RegularTraceFiberFamily.scalar,RegularTraceFiberFamily.action_fiber,
    LinearMap.smul_apply,Module.End.one_apply,map_smul]

theorem actualCoordinatePrincipalTrace_second_symm (i j : I dim) :
    let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    ((F.divergence hY).second i j).reverse.action hY =
      ((F.divergence hY).second j i).forward.action hY := by
  dsimp only
  simp only [CoordinatePrincipalTraceFactors.divergence,actualCoordinatePrincipalTraceFactors,PairedTraceFiberFamily.neg,
    PairedTraceFiberFamily.scalar,PairedTraceFiberFamily.symmetric,RegularTraceFiberFamily.action_neg,
    RegularTraceFiberFamily.action_scalar]
  congr 1
  apply smoothSupportedTraceBaseMul_congr
  intro x hx
  congr 1
  have hSym : (d.g₂ x).transpose = d.g₂ x := Matrix.isHermitian_iff_isSymm.mp (hg₂.2 x hx).isHermitian
  have hInv : ((d.g₂ x)⁻¹).transpose = (d.g₂ x)⁻¹ := by rw [Matrix.transpose_nonsing_inv,hSym]
  unfold principal
  exact congrArg (fun M : Mat dim => d.radius x*(((dim:ℝ)/((d.γ x)*(d.g₂ x)⁻¹).trace) • M) j i) hInv

theorem actualCoordinatePrincipalTrace_principal_normal (i j : I dim) :
    let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
    let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
    let a := (F.principal i j).forward.action hY
    let density₀ := (F.density i).forward.action hY
    let b := (F.principalDerivative i i j).forward.action hY
    (F.divergence hY).baseAdjoint hY i*((F.divergence hY).second i j).forward.action hY*D j =
      a*(D i*D j)+(b+density₀*a)*D j := by
  dsimp only
  let F := actualCoordinatePrincipalTraceFactors hY hg hK he hr hr₀ hlog hQ hg₂ hA hEll S V
  let D (k : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis k)
  let a := (F.principal i j).forward.action hY
  let b := (F.principalDerivative i i j).forward.action hY
  let L := (F.density i).forward.action hY
  have hDb : D i*a-a*D i = b := by
    have h := smoothSupportedTraceBaseDiff_mul hY (axis i) (fun x => d.radius x*principal d.γ d.g₂ x i j)
      (hr.mul (hQ i j))
    change D i*a = a*D i+b at h
    rw [h]
    abel
  have h := normalToDivergence_base_two a (D i) (-D i-L) (D j) L rfl
  rw [hDb] at h
  simp only [CoordinatePrincipalTraceFactors.divergence,CoordinateTraceDivergence.baseAdjoint,
    PairedTraceFiberFamily.neg,RegularTraceFiberFamily.action_neg]
  exact (sub_eq_iff_eq_add.mp h.symm)

end CalderonN

module

public import Proof.CalderonN.ActualLowerOrderCancellation
public import Proof.CalderonN.ActualLowerOrderVelocity
public import Proof.CalderonN.SmoothSupportedTraceCoefficientBounds

import Mathlib.Tactic

/-! The sum of the affine and quadratic Gauss corrections is a genuine
fiber operator on the same sections used by the moving trace. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise Classical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {d : Data dim}

@[expose] def actualGaussLowerVelocityFamily
    (F : ∀ x ∈ Y,ActualGaussFiberData d x) (i : I dim) (x : X dim) :
    Module.End ℝ (SmoothSphereTrace dim) :=
  if hx : x ∈ Y then
    (F x hx).affineCorrection*(ActualGaussFiberData.translationMultiplier d x i+
      fderiv ℝ d.radius x (axis i) • 1)+d.radius x • (F x hx).velocityRemainder i
  else 0

variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K d.γ)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => d.frame x a) Y)
  (hr : ContDiffOn ℝ ∞ d.radius Y) (hr₀ : ∀ x ∈ Y,d.radius x ≠ 0)
  (hlog : ContDiffOn ℝ ∞ (fun x => Real.log (d.radius x)) Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)
variable (F : ∀ x ∈ Y,ActualGaussFiberData d x)
  (hC : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussFiberFamily F i))
  (hF : ∀ i,SmoothSupportedTraceFiberRegular Y (actualGaussAffineFamily F i))

theorem actualSupportedGaussLowerVelocity_fiber (hn : 3 ≤ dim) {x : X dim} (hx : x ∈ Y)
    (i : I dim) (u : SmoothSupportedTraceSection Y) :
    let E := actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i
    let G := actualSupportedAffine hY F hF i
    smoothSupportedTraceFiberL x ((E+G) u) = actualGaussLowerVelocityFamily F i x (smoothSupportedTraceFiberL x u) := by
  dsimp only
  rw [LinearMap.add_apply,map_add,actualSupportedGaussRemainder_fiber hY hg he hr hr₀ hlog hA hEll S F hC hF hn hx]
  simp only [actualSupportedAffine,smoothSupportedTraceFiberAction_fiber,actualGaussAffineFamily,
    actualGaussLowerVelocityFamily,dite_eq_left hx,LinearMap.add_apply,LinearMap.smul_apply,mul_add,
    mul_smul_comm,mul_one]
  abel

include hY hg he hr hr₀ hlog hA hEll S hC hF in
theorem actualGaussLowerVelocityFamily_regular (hn : 3 ≤ dim) (i : I dim) :
    SmoothSupportedTraceFiberRegular Y (actualGaussLowerVelocityFamily F i) := by
  intro u
  obtain ⟨g,hg',heq⟩ := smoothSupportedTraceSection_repr
    ((actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i+actualSupportedAffine hY F hF i) u)
  refine ⟨univ,g,isOpen_univ,subset_univ _,hg'.contDiffOn,?_⟩
  intro x hx z
  rw [← actualSupportedGaussLowerVelocity_fiber hY hg he hr hr₀ hlog hA hEll S F hC hF hn hx i u]
  exact (heq x z).symm

theorem actualSupportedGaussLowerVelocity_eq_action (hn : 3 ≤ dim) (i : I dim) :
    actualSupportedGaussRemainder hY hg he hr hr₀ hlog hA hEll S F hC hF i+actualSupportedAffine hY F hF i =
      smoothSupportedTraceFiberAction hY (actualGaussLowerVelocityFamily F i)
        (actualGaussLowerVelocityFamily_regular hY hg he hr hr₀ hlog hA hEll S F hC hF hn i) := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  rw [actualSupportedGaussLowerVelocity_fiber hY hg he hr hr₀ hlog hA hEll S F hC hF hn hx i u,
    smoothSupportedTraceFiberAction_fiber]

end CalderonN

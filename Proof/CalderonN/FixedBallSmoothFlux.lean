module

public import Proof.CalderonN.ClassicalBallBoundaryValue
public import Proof.CalderonN.BallRegularity.CoordinateFluxEnergy
public import Proof.CalderonN.GreenSourceCutoff

import Mathlib.Tactic

/-! Adapted from the released Proposition 5.3 `WeakFluxIntegration`.
The same smooth flux represents the weak energy and its actual sphere
pairing in the general-dimensional ball. -/

public section

noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 22
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet TauCeti PDE

variable {dim : ℕ}

/-- Coordinate flux of the actual divergence coefficient. -/
def smoothBallFlux (a : X dim → Mat dim) (u : X dim → ℝ) (x : X dim) : X dim :=
  WithLp.toLp 2 (fun i => ∑ j, a x i j * coordDeriv j u x)

theorem smoothBallFlux_apply (a : X dim → Mat dim) (u : X dim → ℝ) (x : X dim) (i : Fin dim) :
    smoothBallFlux a u x i = ∑ j, a x i j * coordDeriv j u x := by
  unfold smoothBallFlux
  rfl

theorem contDiff_smoothBallFlux {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    (u : SmoothData dim) : ContDiff ℝ ∞ (smoothBallFlux a u.1) := by
  unfold smoothBallFlux
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin dim => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro j hj
  have hA : ContDiff ℝ ∞ (fun x => a x i j) := (contDiff_pi.mp (contDiff_pi.mp ha i) j)
  exact hA.mul ((u.2.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)

theorem coordinateFluxDivergence_smoothBallFlux (a : X dim → Mat dim)
    (u : X dim → ℝ) (x : X dim) :
    coordinateFluxDivergence (smoothBallFlux a u) x = -negativeBallDivergence a u x := by
  simp only [coordinateFluxDivergence,smoothBallFlux_apply,negativeBallDivergence,
    Elliptic.Lop,Elliptic.pd,coordDeriv,neg_neg]

variable [NeZero dim]

theorem energyFormH1_smooth_left (a : X dim → Mat dim)
    (u : SmoothData dim) (v : FixedBallH1 dim) :
    PDE.energyFormH1 a 0 0 (smoothSobolev u) v =
      ∫ x in fixedBallOpens dim, ∑ i, W1p.gradient v x i * smoothBallFlux a u.1 x i := by
  rw [energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [gradient_smoothSobolev_ae u] with x hx
  simp only [energyIntegrand_apply,jetField_apply,driftForm_apply,massForm_apply,Pi.zero_apply,
    inner_zero_left,zero_mul,add_zero,matrixBilinearForm_apply,Matrix.mulVec,dotProduct,hx,
    smoothBallFlux_apply]
  have he (j : Fin dim) : gradient u.1 x j = coordDeriv j u.1 x := by
    rw [coordDeriv,← inner_gradient_left (𝕜 := ℝ)]
    simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
  simp only [he]

/-- A classically harmonic smooth representative satisfies the homogeneous
weak equation against the native zero-Dirichlet space. -/
theorem energyFormH1_smooth_zeroDirichlet {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    (u : SmoothData dim)
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1))
    (v : FixedBallH1Zero dim) :
    PDE.energyFormH1 a 0 0 (smoothSobolev u) (v : FixedBallH1 dim) = 0 := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let F := smoothBallFlux a u.1
  have hF : ContDiff ℝ ∞ F := contDiff_smoothBallFlux ha u
  let q (i : Fin dim) : SmoothData dim := ⟨fun x => F x i,
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF⟩
  let a₀ (i : Fin dim) := W1p.value (smoothSobolev (q i))
  let a₁ (i : Fin dim) := unitBallCoordinateGradientL i (smoothSobolev (q i))
  let b₁ (i : Fin dim) := unitBallCoordinateGradientL i (v : FixedBallH1 dim)
  have hA₀ (i : Fin dim) : a₀ i =ᵐ[μ] fun x => F x i := value_smoothSobolev_ae (q i)
  have hA₁ (i : Fin dim) : a₁ i =ᵐ[μ] coordDeriv i (q i).1 := unitBallCoordinateGradientL_smooth_ae (q i) i
  have hB₁ (i : Fin dim) : b₁ i =ᵐ[μ] fun x => W1p.gradient (v : FixedBallH1 dim) x i :=
    unitBallCoordinateGradientL_ae i v
  have h1 : PDE.energyFormH1 a 0 0 (smoothSobolev u) (v : FixedBallH1 dim) =
      ∫ x, ∑ i, ⟪a₀ i x, b₁ i x⟫_ℝ ∂μ := by
    rw [energyFormH1_smooth_left]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hA₀,ae_all_iff.mpr hB₁] with x hA hB
    simp only [RCLike.inner_apply,conj_trivial,hA,hB,F]
  have h2 : ∑ i, a₁ i = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ a₁,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ),
      ae_all_iff.mpr hA₁, ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with x hsum hzero hD hx
    rw [hsum, hzero]
    simp only [hD, Pi.zero_apply]
    change coordinateFluxDivergence F x = 0
    rw [coordinateFluxDivergence_smoothBallFlux, show negativeBallDivergence a u.1 x = 0 from hu hx, neg_zero]
  rw [h1, integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := ℝ) (a₀ i) (b₁ i))]
  simp only [← L2.inner_def]
  have hPart (i : Fin dim) : ⟪a₀ i, b₁ i⟫_ℝ = -⟪a₁ i, W1p.value (v : FixedBallH1 dim)⟫_ℝ := by
    linarith only [unitBall_coordinate_inner_integration (smoothSobolev (q i)) i v]
  simp_rw [hPart]
  rw [Finset.sum_neg_distrib, ← sum_inner, h2, inner_zero_left, neg_zero]

/-- Integrate a smooth divergence-free flux against the gradient of a
smooth scalar, on the ball with its probability-normalized boundary. -/
theorem integral_smoothFlux_gradient_eq_boundary [Nontrivial (Fin dim)]
    (F : X dim → X dim) (hF : ContDiff ℝ ∞ F) (v : SmoothData dim)
    (hZero : EqOn (coordinateFluxDivergence F) 0 (ball (0 : X dim) 1)) :
    (∫ x in fixedBallOpens dim, ∑ i, gradient v.1 x i * F x i) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),
        v.1 w * ⟪(w : X dim), F w⟫_ℝ ∂(sphereProbability dim) := by
  let W (x : X dim) := v.1 x • F x
  have hW : ContDiff ℝ ∞ W := v.2.smul hF
  have hD (x : X dim) (hx : x ∈ ball (0 : X dim) 1) :
      coordinateFluxDivergence W x = ∑ i, gradient v.1 x i * F x i := by
    have hProd (i : Fin dim) :
        coordDeriv i (fun z => W z i) x = v.1 x * coordDeriv i (fun z => F z i) x +
          gradient v.1 x i * F x i := by
      change coordDeriv i (fun z => v.1 z * F z i) x = _
      have hFi : DifferentiableAt ℝ (fun z => F z i) x :=
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF).differentiable (by simp) x
      simp only [coordDeriv, fderiv_fun_mul (v.2.differentiable (by simp) x) hFi,
        add_apply, smul_apply, smul_eq_mul]
      have hg : gradient v.1 x i = fderiv ℝ v.1 x (axis i) := by
        rw [← inner_gradient_left (𝕜 := ℝ)]
        simp only [axis,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
      rw [hg]
      ring
    change (∑ i, coordDeriv i (fun z => W z i) x) = _
    simp_rw [hProd]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← coordinateFluxDivergence]
    rw [show coordinateFluxDivergence F x = 0 from hZero hx]
    ring
  have hBulk : (∫ x in fixedBallOpens dim, ∑ i, gradient v.1 x i * F x i) =
      ∫ x in ball (0 : X dim) 1, coordinateFluxDivergence W x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with x hxB
    exact (hD x hxB).symm
  rw [hBulk, integral_unitBall_coordinateFluxDivergence W hW, unitSphereFlux,
    ← integral_unitSphereArea_mul_probability, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with w
  rw [show ⟪(w : X dim), W w⟫_ℝ = v.1 w * ⟪(w : X dim), F w⟫_ℝ from real_inner_smul_right _ _ _]

/-- For a smooth harmonic input and a smooth test, the same weak energy
is the sphere pairing with the physical conormal flux. -/
theorem energyFormH1_smooth_eq_boundary_flux [Nontrivial (Fin dim)]
    {a : X dim → Mat dim} (ha : ContDiff ℝ ∞ a) (u v : SmoothData dim)
    (hu : EqOn (negativeBallDivergence a u.1) 0 (ball (0 : X dim) 1)) :
    PDE.energyFormH1 a 0 0 (smoothSobolev u) (smoothSobolev v) =
      unitSphereArea dim * ∫ w : ↥(standardSphere dim),
        v.1 w * ⟪(w : X dim), smoothBallFlux a u.1 w⟫_ℝ ∂(sphereProbability dim) := by
  rw [energyFormH1_smooth_left]
  have hBulk : (∫ x in fixedBallOpens dim,
      ∑ i, W1p.gradient (smoothSobolev v) x i * smoothBallFlux a u.1 x i) =
      ∫ x in fixedBallOpens dim, ∑ i, gradient v.1 x i * smoothBallFlux a u.1 x i := by
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae v] with x hx
    rw [hx]
  rw [hBulk]
  apply integral_smoothFlux_gradient_eq_boundary _ (contDiff_smoothBallFlux ha u) v
  intro x hx
  rw [coordinateFluxDivergence_smoothBallFlux, show negativeBallDivergence a u.1 x = 0 from hu hx]
  exact neg_zero

end CalderonN

module

public import Proof.CalderonN.FixedBallSmoothFlux

import Mathlib.Tactic

/-! The weak zero-Dirichlet identity for a smooth divergence-free
flux, obtained from the fixed-ball proof before choosing a coefficient. -/

public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim]

theorem integral_smoothFlux_weak_zeroDirichlet
    (F : X dim → X dim) (hF : ContDiff ℝ ∞ F)
    (hDiv : EqOn (coordinateFluxDivergence F) 0 (ball (0 : X dim) 1)) (v : FixedBallH1Zero dim) :
    (∫ x in fixedBallOpens dim, ∑ i, W1p.gradient (v : FixedBallH1 dim) x i * F x i) = 0 := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let q (i : Fin dim) : SmoothData dim := ⟨fun x => F x i,
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF⟩
  let a₀ (i : Fin dim) := W1p.value (smoothSobolev (q i))
  let a₁ (i : Fin dim) := unitBallCoordinateGradientL i (smoothSobolev (q i))
  let b₁ (i : Fin dim) := unitBallCoordinateGradientL i (v : FixedBallH1 dim)
  have hA₀ (i : Fin dim) : a₀ i =ᵐ[μ] fun x => F x i := value_smoothSobolev_ae (q i)
  have hA₁ (i : Fin dim) : a₁ i =ᵐ[μ] coordDeriv i (q i).1 := unitBallCoordinateGradientL_smooth_ae (q i) i
  have hB₁ (i : Fin dim) : b₁ i =ᵐ[μ] fun x => W1p.gradient (v : FixedBallH1 dim) x i :=
    unitBallCoordinateGradientL_ae i v
  have h1 : (∫ x in fixedBallOpens dim, ∑ i, W1p.gradient (v : FixedBallH1 dim) x i * F x i) =
      ∫ x, ∑ i, ⟪a₀ i x, b₁ i x⟫_ℝ ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hA₀,ae_all_iff.mpr hB₁] with x hA hB
    simp only [RCLike.inner_apply,conj_trivial,hA,hB,mul_comm]
  have h2 : ∑ i, a₁ i = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ a₁,
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ),
      ae_all_iff.mpr hA₁, ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with x hsum hzero hD hx
    rw [hsum, hzero]
    simp only [hD, Pi.zero_apply]
    change coordinateFluxDivergence F x = 0
    exact hDiv hx
  rw [h1, integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := ℝ) (a₀ i) (b₁ i))]
  simp only [← L2.inner_def]
  have hPart (i : Fin dim) : ⟪a₀ i, b₁ i⟫_ℝ = -⟪a₁ i, W1p.value (v : FixedBallH1 dim)⟫_ℝ := by
    linarith only [unitBall_coordinate_inner_integration (smoothSobolev (q i)) i v]
  simp_rw [hPart]
  rw [Finset.sum_neg_distrib, ← sum_inner, h2, inner_zero_left, neg_zero]

theorem integrable_smoothFlux_weak_pair
    (F : X dim → X dim) (hF : ContDiff ℝ ∞ F) (v : FixedBallH1 dim) :
    IntegrableOn (fun x => ∑ i, W1p.gradient v x i * F x i) (fixedBallOpens dim : Set (X dim)) := by
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  let q (i : Fin dim) : SmoothData dim := ⟨fun x => F x i,
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF⟩
  let a (i : Fin dim) := W1p.value (smoothSobolev (q i))
  let b (i : Fin dim) := unitBallCoordinateGradientL i v
  have ha (i : Fin dim) : a i =ᵐ[μ] fun x => F x i := value_smoothSobolev_ae (q i)
  have hb (i : Fin dim) : b i =ᵐ[μ] fun x => W1p.gradient v x i := unitBallCoordinateGradientL_ae i v
  apply (integrable_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜:=ℝ) (a i) (b i))).congr
  filter_upwards [ae_all_iff.mpr ha,ae_all_iff.mpr hb] with x hx hy
  simp only [RCLike.inner_apply,conj_trivial,hx,hy,mul_comm]

theorem energyFormH1_two_smoothFluxes_zeroDirichlet
    {A G : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G)
    (u q : SmoothData dim)
    (hDiv : EqOn (coordinateFluxDivergence (smoothBallFlux A q.1+smoothBallFlux G u.1)) 0
      (ball (0 : X dim) 1)) (v : FixedBallH1Zero dim) :
    energyFormH1 A 0 0 (smoothSobolev q) (v : FixedBallH1 dim) +
      energyFormH1 G 0 0 (smoothSobolev u) (v : FixedBallH1 dim) = 0 := by
  have hF := contDiff_smoothBallFlux hA q
  have hE := contDiff_smoothBallFlux hG u
  have h := integral_smoothFlux_weak_zeroDirichlet _ (hF.add hE) hDiv v
  rw [energyFormH1_smooth_left,energyFormH1_smooth_left,
    ← integral_add (integrable_smoothFlux_weak_pair _ hF _) (integrable_smoothFlux_weak_pair _ hE _)]
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [PiLp.add_apply,mul_add,Finset.sum_add_distrib]

end CalderonN

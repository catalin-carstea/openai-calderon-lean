module

public import Proof.Manuscript.LowerGreen.WeakBallCommutator
public import Proof.Manuscript.LowerGreen.GreenCutoffOperators

import Proof.CalderonN.BallRegularity.StrongDerivativeValues
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Topology Matrix.Norms.Elementwise
open CalderonN CalderonN.BallDirichlet TauCeti

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 14
set_option backward.isDefEq.respectTransparency true

namespace CalderonPaper.LowerGreen

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NeZero n] [Nontrivial (Fin n)] [FiniteDimensional ℝ P] in
private theorem div_cutoffFirst_eq_twice_cutoffZero
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ : SmoothData n) (p : P)
    (hSym : ∀ z ∈ ball (0 : X n) 1, ∀ i j, a (p,z) i j = a (p,z) j i)
    {x : X n} (hx : x ∈ ball (0 : X n) 1) :
    (∑ j, coordDeriv j (fun z => greenCutoffFirstCoefficient a χ.1 j (p,z)) x) =
      2 * greenCutoffZeroCoefficient a χ.1 (p,x) := by
  let v (j : I n) (z : X n) := ∑ i, a (p,z) j i * coordDeriv i χ.1 z
  have hv (j : I n) : ContDiff ℝ ∞ (v j) :=
    ContDiff.sum fun i _ => (((Matrix.entryLinearMap ℝ ℝ j i).toContinuousLinearMap).contDiff.comp
      (ha.comp (contDiff_const.prodMk contDiff_id))).mul (Elliptic.contDiff_pd χ.2)
  have hloc (j : I n) : (fun z => greenCutoffFirstCoefficient a χ.1 j (p,z)) =ᶠ[𝓝 x]
      fun z => (-2 : ℝ) * v j z := by
    filter_upwards [isOpen_ball.mem_nhds hx] with z hz
    unfold greenCutoffFirstCoefficient
    dsimp only [v]
    simp_rw [hSym z hz]
  have hd (j : I n) : coordDeriv j (fun z => greenCutoffFirstCoefficient a χ.1 j (p,z)) x =
      (-2 : ℝ) * coordDeriv j (v j) x :=
    (congrArg (fun L : X n →L[ℝ] ℝ => L (axis j)) ((hloc j).fderiv_eq (𝕜 := ℝ))).trans
      (Elliptic.pd_const_mul _ (hv j) x)
  simp_rw [hd,← Finset.mul_sum]
  unfold greenCutoffZeroCoefficient negativeBallDivergence Elliptic.Lop
  change (-2 : ℝ) * (∑ j, coordDeriv j (v j) x) = 2 * -(∑ j, coordDeriv j (v j) x)
  ring

@[expose] def weakGreenCutoffFamily (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    FixedBallL2 n →L[ℝ] FixedBallH1Zero n →L[ℝ] ℝ :=
  weakFirstOrderBallL
    (fun j => commonSupportCoefficientFamily 1 (greenCutoffFirstCoefficient a χ.1 j)
      (contDiff_greenCutoffFirstCoefficient ha χ.2 j) (tsupport χ.1) hχ.isCompact
      (greenCutoffFirstCoefficient_vanishes a χ.1 j) p)
    (commonSupportCoefficientFamily 1 (greenCutoffZeroCoefficient a χ.1)
      (contDiff_greenCutoffZeroCoefficient ha χ.2) (tsupport χ.1) hχ.isCompact
      (greenCutoffZeroCoefficient_vanishes a χ.1) p)

theorem contDiff_weakGreenCutoffFamily
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ : SmoothData n) (hχ : HasCompactSupport χ.1) :
    ContDiff ℝ ∞ (weakGreenCutoffFamily a ha χ hχ) :=
  contDiff_weakFirstOrderBallL_family _ _ (contDiff_greenCutoffFirstCoefficient ha χ.2)
    (contDiff_greenCutoffZeroCoefficient ha χ.2) _ hχ.isCompact _ _

private theorem coefficientMultiplier_smoothBall_value
    (f g : SmoothData n) (c : SmoothCoefficientJets n 1)
    (hc : ∀ x, coefficientValue 1 c x * f.1 x = g.1 x) :
    coefficientMultiplier fixedSobolevCalculus 0 c (Wkp.value 0 (smoothBallSobolev 0 f)) =
      (Wkp.value 0 (smoothBallSobolev 0 g)) := by
  apply Lp.ext
  refine (coefficientMultiplier_value_ae fixedSobolevCalculus 0 c (smoothBallSobolev 0 f)).trans ?_
  refine ((Filter.EventuallyEq.rfl (f := coefficientValue 1 c)).mul
    (value_smoothBallSobolev_ae 0 f)).trans ?_
  exact (Filter.EventuallyEq.of_eq (funext hc)).trans (value_smoothBallSobolev_ae 0 g).symm

private theorem pointwise_cutoff_forcing_div
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ u : SmoothData n) (p : P)
    (hSym : ∀ z ∈ ball (0 : X n) 1, ∀ i j, a (p,z) i j = a (p,z) j i)
    (x : X n) (hx : x ∈ ball (0 : X n) 1) :
    greenSourceCutoffError (fun z => a (p,z)) χ.1 u.1 x =
      (∑ i, coordDeriv i (fun z => greenCutoffFirstCoefficient a χ.1 i (p,z) * u.1 z) x) -
        greenCutoffZeroCoefficient a χ.1 (p,x) * u.1 x := by
  have hd (i : I n) : ContDiff ℝ ∞ (fun z => greenCutoffFirstCoefficient a χ.1 i (p,z)) :=
    (contDiff_greenCutoffFirstCoefficient ha χ.2 i).comp (contDiff_const.prodMk contDiff_id)
  simp_rw [greenSourceCutoffError_firstOrder a χ.1 u.1 p x, Elliptic.pd_mul (hd _) u.2,
    Finset.sum_add_distrib, ← Finset.sum_mul, div_cutoffFirst_eq_twice_cutoffZero a ha χ p hSym hx]
  ring

/-- On a smooth argument the distributional commutator is the weak
forcing given by its classical differential expression. -/
theorem weakGreenCutoffFamily_apply_smooth
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a) (χ : SmoothData n) (hχ : HasCompactSupport χ.1)
    (p : P) (hSym : ∀ z ∈ ball (0 : X n) 1, ∀ i j, a (p,z) i j = a (p,z) j i)
    (u : SmoothData n) :
    weakGreenCutoffFamily a ha χ hχ p (Wkp.value 0 (smoothBallSobolev 0 u)) =
      PDE.dirichletForcing (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n) (Wkp.value 0 (smoothBallSobolev 0
        ⟨greenSourceCutoffError (fun z => a (p,z)) χ.1 u.1,
         contDiff_greenSourceCutoffError (ha.comp (contDiff_const.prodMk contDiff_id)) χ.2 u.2⟩)) := by
  let b (i : I n) := commonSupportCoefficientFamily 1 (greenCutoffFirstCoefficient a χ.1 i)
    (contDiff_greenCutoffFirstCoefficient ha χ.2 i) (tsupport χ.1) hχ.isCompact
    (greenCutoffFirstCoefficient_vanishes a χ.1 i) p
  let c := commonSupportCoefficientFamily 1 (greenCutoffZeroCoefficient a χ.1)
    (contDiff_greenCutoffZeroCoefficient ha χ.2) (tsupport χ.1) hχ.isCompact
    (greenCutoffZeroCoefficient_vanishes a χ.1) p
  let g (i : I n) : SmoothData n := ⟨fun z => greenCutoffFirstCoefficient a χ.1 i (p,z) * u.1 z,
    ((contDiff_greenCutoffFirstCoefficient ha χ.2 i).comp (contDiff_const.prodMk contDiff_id)).mul u.2⟩
  let h : SmoothData n := ⟨fun z => greenCutoffZeroCoefficient a χ.1 (p,z) * u.1 z,
    ((contDiff_greenCutoffZeroCoefficient ha χ.2).comp (contDiff_const.prodMk contDiff_id)).mul u.2⟩
  let f : SmoothData n := ⟨greenSourceCutoffError (fun z => a (p,z)) χ.1 u.1,
    contDiff_greenSourceCutoffError (ha.comp (contDiff_const.prodMk contDiff_id)) χ.2 u.2⟩
  let d (i : I n) : FixedBallL2 n :=
    Wkp.value 0 (unitBallCoordinateDerivativeL fixedSobolevCalculus 0 i (smoothBallSobolev 1 (g i)))
  have hb (i : I n) :
      coefficientMultiplier fixedSobolevCalculus 0 (b i) (Wkp.value 0 (smoothBallSobolev 0 u)) =
        Wkp.value 1 (smoothBallSobolev 1 (g i)) := by
    have hVal := (Wkp.value_succ 0 (smoothBallSobolev 1 (g i))).symm
    rw [lowerOrder_smoothBallSobolev] at hVal
    exact (coefficientMultiplier_smoothBall_value u (g i) (b i) (fun z => rfl)).trans hVal
  have hc : coefficientMultiplier fixedSobolevCalculus 0 c (Wkp.value 0 (smoothBallSobolev 0 u)) =
      Wkp.value 0 (smoothBallSobolev 0 h) :=
    coefficientMultiplier_smoothBall_value u h c (fun z => rfl)
  have hd (i : I n) : d i =ᵐ[volume.restrict (fixedBallOpens n)] coordDeriv i (g i).1 := by
    change Wkp.value 0 (unitBallCoordinateDerivativeL fixedSobolevCalculus 0 i
      (smoothBallSobolev 1 (g i))) =ᵐ[_] _
    rw [unitBallCoordinateDerivativeL_smooth]
    exact value_smoothBallSobolev_ae _ _
  have hf : Wkp.value 0 (smoothBallSobolev 0 f) =
      (∑ i, d i) - Wkp.value 0 (smoothBallSobolev 0 h) := by
    apply Lp.ext
    refine (value_smoothBallSobolev_ae 0 f).trans ?_
    apply Filter.EventuallyEq.trans _
      ((Lp.coeFn_sub _ _).trans ((Lp.coeFn_finsetSum _ _).sub (value_smoothBallSobolev_ae 0 h))).symm
    filter_upwards [Filter.eventually_all.2 hd,
      ae_restrict_mem (μ := (volume : Measure (X n))) (fixedBallOpens n).isOpen.measurableSet] with z hz hBall
    simp only [Pi.sub_apply, Finset.sum_apply]
    rw [Finset.sum_congr rfl (fun i _ => hz i)]
    exact pointwise_cutoff_forcing_div a ha χ u p hSym z hBall
  apply ContinuousLinearMap.ext
  intro φ
  change weakFirstOrderSumL (fun i => coefficientMultiplier fixedSobolevCalculus 0 (b i))
    (coefficientMultiplier fixedSobolevCalculus 0 c) (Wkp.value 0 (smoothBallSobolev 0 u)) φ =
      PDE.dirichletForcing (mu := (volume : Measure (X n))) (Omega := fixedBallOpens n) (Wkp.value 0 (smoothBallSobolev 0 f)) φ
  rw [weakFirstOrderSumL_apply,PDE.dirichletForcing_apply,hf,inner_sub_left,sum_inner,hc]
  simp_rw [hb]
  rw [← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ =>
    (unitBallCoordinateDerivative_inner_integration fixedSobolevCalculus 0 i
      (smoothBallSobolev 1 (g i)) φ).symm)

end CalderonPaper.LowerGreen

end

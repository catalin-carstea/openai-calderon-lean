import Proof.NormalHarmonicRepresentatives
import Proof.Archive.CoordinateFluxEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ENNReal InnerProductSpace ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.MetricOperator OAI.AnisotropicCalderon.ConnectionError

/-- The Sobolev energy pairing uses the actual assembled coordinate flux. -/
lemma energyFormH1_eq_sum_flux_inner (a : X → Mat) (u v : BallH1)
    (p : I → Lp ℝ 2 ((volume : Measure X).restrict ballOpens))
    (hp : ∀ i,p i =ᵐ[(volume : Measure X).restrict ballOpens]
      fun x => ∑ j,a x i j*(TauCeti.W1p.gradient u x) j) :
    TauCeti.PDE.energyFormH1 a 0 0 u v = ∑ i,⟪p i,unitBallCoordinateGradientL i v⟫_ℝ := by
  let z := fun (i : I) (x : X) => ⟪p i x,unitBallCoordinateGradientL i v x⟫_ℝ
  have hi (i : I) : Integrable (z i) ((volume : Measure X).restrict ballOpens) :=
    L2.integrable_inner (𝕜:=ℝ) (p i) (unitBallCoordinateGradientL i v)
  have hP := ae_all_iff.mpr hp
  have hG : ∀ᵐ x ∂((volume : Measure X).restrict ballOpens),∀ i,
      unitBallCoordinateGradientL i v x = (TauCeti.W1p.gradient v x) i :=
    ae_all_iff.mpr (fun i => unitBallCoordinateGradientL_ae i v)
  calc
    TauCeti.PDE.energyFormH1 a 0 0 u v = ∫ x in ballOpens,∑ i,z i x := by
      rw [TauCeti.PDE.energyFormH1_def]
      apply integral_congr_ae
      filter_upwards [hP,hG] with x hx hy
      simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,
        TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,Pi.zero_apply,
        inner_zero_left,zero_mul,add_zero,TauCeti.PDE.matrixBilinearForm_apply,Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [z,RCLike.inner_apply,conj_trivial]
      rw [hx i,hy i]
    _ = ∑ i,∫ x in ballOpens,z i x := integral_finsetSum Finset.univ (fun i _ => hi i)
    _ = _ := by simp only [L2.inner_def,z]

/-- A globally smooth divergence-free flux gives the exact weak homogeneous
    equation against every genuine zero-boundary Sobolev test. -/
theorem smooth_flux_weak_equation (a : X → Mat) (U : SmoothData) (F : X → X)
    (hF : ContDiff ℝ ∞ F)
    (hFlux : ∀ x ∈ (ballOpens : Set X),F x = matrixOperatorMap (a x) (gradient U.1 x))
    (hDiv : ∀ x ∈ (ballOpens : Set X),coordinateFluxDivergence F x = 0)
    (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 a 0 0 (smoothSobolev U) (v : BallH1) = 0 := by
  let Q : I → SmoothData := fun i => ⟨fun x => F x i,by
    simpa only [Function.comp_def,PiLp.proj_apply] using
      (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.comp hF⟩
  let p := fun i => TauCeti.W1p.value (smoothSobolev (Q i))
  have hMem : ∀ᵐ x ∂((volume : Measure X).restrict ballOpens),x ∈ (ballOpens : Set X) :=
    ae_restrict_mem ballOpens.isOpen.measurableSet
  have hp (i : I) : p i =ᵐ[(volume : Measure X).restrict ballOpens]
      fun x => ∑ j,a x i j*(TauCeti.W1p.gradient (smoothSobolev U) x) j := by
    filter_upwards [value_smoothSobolev_ae (Q i),gradient_smoothSobolev_ae U,
      hMem] with x hx hu hxBall
    rw [hx,hu]
    change F x i = _
    rw [hFlux x hxBall]
    exact MetricVolume.matrixOperator_coordinate (a x) (gradient U.1 x) i
  have hGradSum : (∑ i,unitBallCoordinateGradientL i (smoothSobolev (Q i))) =
      (0 : Lp ℝ 2 ((volume : Measure X).restrict ballOpens)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => unitBallCoordinateGradientL i (smoothSobolev (Q i))),
      Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=((volume : Measure X).restrict ballOpens)),
      ae_all_iff.mpr (fun i => unitBallCoordinateGradientL_ae i (smoothSobolev (Q i))),
      ae_all_iff.mpr (fun i => gradient_smoothSobolev_ae (Q i)),
      hMem] with x hsum hzero hcoord hgrad hx
    rw [hsum,hzero]
    simp only [Pi.zero_apply]
    have hPoint : (∑ i,(gradient (Q i).1 x) i) = coordinateFluxDivergence F x := by
      simp only [Q,MetricVolume.gradient_coordinate,coordinateFluxDivergence,
        MetricVolume.coordinateVector,NormalCoordinatesFrame.coordinateVector]
    calc
      _ = ∑ i,(gradient (Q i).1 x) i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoord i,hgrad i]
      _ = 0 := hPoint.trans (hDiv x hx)
  have hPart (i : I) : ⟪p i,unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ =
      -⟪unitBallCoordinateGradientL i (smoothSobolev (Q i)),TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
    have hh := unitBall_coordinate_inner_integration (smoothSobolev (Q i)) i v
    change ⟪TauCeti.W1p.value (smoothSobolev (Q i)),unitBallCoordinateGradientL i (v : BallH1)⟫_ℝ = _
    linarith only [hh]
  rw [energyFormH1_eq_sum_flux_inner a (smoothSobolev U) (v : BallH1) p hp]
  simp_rw [hPart]
  rw [Finset.sum_neg_distrib,← sum_inner,hGradSum,inner_zero_left,neg_zero]

end ShrinkingSpheres

module

public import Proof.CalderonN.BallRegularity.Spaces
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Zero
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Restriction
public import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.Wkp.Classical
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
/-! From Proof/Archive/NativeSmoothBallSobolev.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option maxHeartbeats 1200000
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal ContDiff Distributions Gradient Topology
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]


 
abbrev SmoothData (dim : ℕ) := {f : X dim → ℝ // ContDiff ℝ ∞ f}

def unitBallSmoothCutoff (dim : ℕ) : ContDiffBump (0 : (X dim)) where
  rIn := 2
  rOut := 3
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem unitBallSmoothCutoff_one_of_mem {x : (X dim)} (hx : x ∈ (fixedBallOpens dim)) :
    (unitBallSmoothCutoff dim) x = 1 := by
  apply (unitBallSmoothCutoff dim).one_of_mem_closedBall
  change dist x (0 : (X dim)) ≤ (2 : ℝ)
  change dist x (0 : (X dim)) < (1 : ℝ) at hx
  linarith

theorem unitBallSmoothCutoff_eventuallyEq_one {x : (X dim)}
    (hx : x ∈ Metric.closedBall (0 : (X dim)) 1) :
    ((unitBallSmoothCutoff dim) : (X dim) → ℝ) =ᶠ[nhds x] (fun _ => 1) := by
  apply (unitBallSmoothCutoff dim).eventuallyEq_one_of_mem_ball
  change dist x (0 : (X dim)) < (2 : ℝ)
  change dist x (0 : (X dim)) ≤ (1 : ℝ) at hx
  linarith

 
def smoothWholeSpaceTestFunction (f : (SmoothData dim)) : 𝓓((⊤ : Opens (X dim)), ℝ) where
  toFun := fun x => (unitBallSmoothCutoff dim) x * f.1 x
  contDiff' := (unitBallSmoothCutoff dim).contDiff.mul f.2
  hasCompactSupport' := by
    change HasCompactSupport (((unitBallSmoothCutoff dim) : (X dim) → ℝ) * f.1)
    exact (unitBallSmoothCutoff dim).hasCompactSupport.mul_right
  tsupport_subset' := by intro x hx; trivial

 
def smoothBallSobolev (k : ℕ) (f : (SmoothData dim)) : (BallSobolev dim) k :=
  TauCeti.Wkp.restrictL (mu := (volume : Measure (X dim))) (p := 2)
    (le_top : (fixedBallOpens dim) ≤ (⊤ : Opens (X dim))) k
    (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure (X dim)))
      (Omega := (⊤ : Opens (X dim))) (p := 2) k (smoothWholeSpaceTestFunction f))

theorem value_smoothBallSobolev_ae (k : ℕ) (f : (SmoothData dim)) :
    TauCeti.Wkp.value k (smoothBallSobolev k f)
      =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] f.1 := by
  let phi : 𝓓((⊤ : Opens (X dim)), ℝ) := smoothWholeSpaceTestFunction f
  let u : TauCeti.Wkp (volume : Measure (X dim)) (⊤ : Opens (X dim)) 2 k :=
    TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure (X dim)))
      (Omega := (⊤ : Opens (X dim))) (p := 2) k phi
  have hu : TauCeti.Wkp.value k u
      =ᵐ[(volume : Measure (X dim)).restrict (⊤ : Opens (X dim))] (phi : (X dim) → ℝ) := by
    dsimp only [u]
    rw [TauCeti.Wkp.value_ofTestFunctionₗ]
    exact TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 phi
  have hmeasure : (volume : Measure (X dim)).restrict (fixedBallOpens dim) ≤
      (volume : Measure (X dim)).restrict (⊤ : Opens (X dim)) :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (le_top : (fixedBallOpens dim) ≤ (⊤ : Opens (X dim))))
  have huB := hu.filter_mono (MeasureTheory.ae_mono hmeasure)
  have hr := TauCeti.Wkp.value_restrictL_ae
    (mu := (volume : Measure (X dim))) (p := 2)
    (le_top : (fixedBallOpens dim) ≤ (⊤ : Opens (X dim))) k u
  change TauCeti.Wkp.value k
    (TauCeti.Wkp.restrictL (mu := (volume : Measure (X dim))) (p := 2)
      (le_top : (fixedBallOpens dim) ≤ (⊤ : Opens (X dim))) k u)
    =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] f.1
  filter_upwards [hr, huB, ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet]
    with x hx hy hmem
  calc
    _ = phi x := hx.trans hy
    _ = f.1 x := by
      change (unitBallSmoothCutoff dim) x * f.1 x = f.1 x
      rw [unitBallSmoothCutoff_one_of_mem hmem, one_mul]

def smoothSobolev (f : SmoothData dim) : FixedBallH1 dim :=
  TauCeti.Wkp.firstOrder 0 (smoothBallSobolev 1 f)

theorem value_smoothSobolev_ae (f : SmoothData dim) :
    TauCeti.W1p.value (smoothSobolev f) =ᵐ[volume.restrict (fixedBallOpens dim)] f.1 := by
  rw [smoothSobolev, TauCeti.Wkp.value_firstOrder]
  exact value_smoothBallSobolev_ae 1 f

theorem firstOrder_smoothBallSobolev (k : ℕ) (f : SmoothData dim) :
    TauCeti.Wkp.firstOrder k (smoothBallSobolev (k + 1) f) = smoothSobolev f := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder]
  exact Lp.ext ((value_smoothBallSobolev_ae (k+1) f).trans (value_smoothSobolev_ae f).symm)

theorem lowerOrder_smoothBallSobolev (k : ℕ) (f : SmoothData dim) :
    TauCeti.Wkp.lowerOrder k (smoothBallSobolev (k + 1) f) = smoothBallSobolev k f := by
  apply TauCeti.Wkp.ext k
  rw [← TauCeti.Wkp.value_succ k (smoothBallSobolev (k + 1) f)]
  exact Lp.ext ((value_smoothBallSobolev_ae (k+1) f).trans (value_smoothBallSobolev_ae k f).symm)

theorem iteratedGradient_smoothBallSobolev_ae (k : ℕ) (f : (SmoothData dim)) :
    TauCeti.Wkp.iteratedGradient k (smoothBallSobolev (k + 1) f)
      =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      TauCeti.iteratedGradientChain f.1 k := by
  exact TauCeti.Wkp.iteratedGradient_ae_eq_of_contDiffOn k
    (smoothBallSobolev (k + 1) f) ((f.2.of_le (by simp)).contDiffOn)
    (value_smoothBallSobolev_ae (k + 1) f)

 
theorem gradient_smoothSobolev_ae (f : SmoothData dim) :
    TauCeti.W1p.gradient (smoothSobolev f) =ᵐ[volume.restrict (fixedBallOpens dim)]
      gradient f.1 := by
  simpa only [TauCeti.Wkp.iteratedGradient_zero, TauCeti.iteratedGradientChain_zero, smoothSobolev, TauCeti.Wkp.firstOrder_zero]
    using iteratedGradient_smoothBallSobolev_ae 0 f

theorem norm_smoothBallSobolev_le_wholeSpace (k : ℕ) (f : (SmoothData dim)) :
    ‖smoothBallSobolev k f‖ ≤
      ‖TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure (X dim)))
        (Omega := (⊤ : Opens (X dim))) (p := 2) k (smoothWholeSpaceTestFunction f)‖ := by
  exact TauCeti.Wkp.norm_restrictL_le
    (mu := (volume : Measure (X dim))) (p := 2)
    (le_top : (fixedBallOpens dim) ≤ (⊤ : Opens (X dim))) k
    (TauCeti.Wkp.ofTestFunctionₗ (mu := (volume : Measure (X dim)))
      (Omega := (⊤ : Opens (X dim))) (p := 2) k (smoothWholeSpaceTestFunction f))

theorem smoothSobolev_testFunction (φ : 𝓓(fixedBallOpens dim, ℝ)) :
    smoothSobolev ⟨φ,φ.contDiff⟩ = TauCeti.W1p.ofTestFunctionₗ volume (fixedBallOpens dim) 2 φ := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.W1p.value_ofTestFunctionₗ]
  exact Lp.ext ((value_smoothSobolev_ae ⟨φ,φ.contDiff⟩).trans
    (Filter.EventuallyEq.symm (TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure (X dim))) 2 φ)))

end CalderonN.BallDirichlet

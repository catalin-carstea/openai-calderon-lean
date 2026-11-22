module

public import Proof.CalderonPatch.DirichletWeak
public import Proof.CalderonPatch.GlobalStationarity
public import Proof.CalderonPatch.SmoothNativeLaplace

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace CalderonPatch.DirichletData

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m + 1)
local notation "R" => 𝓘(ℝ, ℝ)

variable (D : DirichletData m M)

omit [PreconnectedSpace M] in
/-- The positive Laplace–Beltrami operator applied to a smooth function,
regarded as an ordinary metric `L²` forcing term. -/
def positiveLaplaceLp (f : M → ℝ) (hf : ContMDiff J R ∞ f) : Lp ℝ 2 D.volume :=
  (nativeLaplace_memLp_two D.metric D.volume D.metric_volume hf).neg.toLp (-nativeLaplace D.metric f)

omit [PreconnectedSpace M] in
theorem positiveLaplaceLp_ae_eq (f : M → ℝ) (hf : ContMDiff J R ∞ f) :
    (D.positiveLaplaceLp f hf : M → ℝ) =ᵐ[D.volume] -nativeLaplace D.metric f :=
  (nativeLaplace_memLp_two D.metric D.volume D.metric_volume hf).neg.coeFn_toLp

/-- Test the completed gradient energy by a smooth zero-trace function
through its classical Laplace–Beltrami operator. -/
theorem inner_dirichletHilbert_test_eq_laplace
    (w : DirichletHilbert D) (v : DirichletTest D) :
    ⟪w, (v : DirichletHilbert D)⟫ = ⟪D.l2Value w, D.positiveLaplaceLp v v.smooth⟫ := by
  refine UniformSpace.Completion.induction_on w (isClosed_eq
    (continuous_id.inner continuous_const)
    (D.l2Value.continuous.inner continuous_const)) ?_
  intro u
  rw [inner_dirichletHilbert_coe, L2.inner_def]
  calc
    _ = ∫ x, energyPairingDensity D.metric v u x ∂D.volume :=
      integral_congr_ae (Eventually.of_forall (energyPairingDensity_symm D.metric u v))
    _ = ∫ x, (-nativeLaplace D.metric v x) * u x ∂D.volume :=
      integral_energyPairingDensity_eq_neg_laplace D.metric D.volume D.metric_volume
        v.smooth u.smooth u.zero_trace
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [D.l2Value_coe_ae_eq u,D.positiveLaplaceLp_ae_eq v v.smooth] with x hx hy
      rw [hx,hy]
      rfl

/-- The `L²` value of the weak inverse solves the corresponding
distributional equation against smooth native zero-trace tests. -/
theorem weakDirichletInverse_distribution (f : Lp ℝ 2 D.volume) (v : DirichletTest D) :
    (∫ x, D.l2Value (D.weakDirichletInverse f) x * (-nativeLaplace D.metric v x) ∂D.volume) =
      ∫ x, f x * v x ∂D.volume := by
  rw [← D.weakDirichletInverse_on_test f v, D.inner_dirichletHilbert_test_eq_laplace, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.positiveLaplaceLp_ae_eq v v.smooth] with x hx
  rw [hx]
  change _ * _ = (-nativeLaplace D.metric v x) * _
  exact mul_comm _ _

/-- For a smooth boundary representative, cancel its variation by
applying the weak inverse to its negative positive Laplacian. -/
def weakHarmonicCorrection (f : M → ℝ) (hf : ContMDiff J R ∞ f) : DirichletHilbert D :=
  D.weakDirichletInverse (- D.positiveLaplaceLp f hf)

/-- Energy bound for the correction of a smooth trial extension. -/
theorem norm_weakHarmonicCorrection_le (f : M → ℝ) (hf : ContMDiff J R ∞ f) :
    ‖D.weakHarmonicCorrection f hf‖ ≤ ‖D.l2Value‖ * ‖D.positiveLaplaceLp f hf‖ := by
  unfold weakHarmonicCorrection
  simpa only [norm_neg] using D.norm_weakDirichletInverse_le (-D.positiveLaplaceLp f hf)

theorem weakHarmonicCorrection_on_test (f : M → ℝ) (hf : ContMDiff J R ∞ f)
    (v : DirichletTest D) :
    ⟪D.weakHarmonicCorrection f hf, (v : DirichletHilbert D)⟫ +
      (∫ x, energyPairingDensity D.metric f v x ∂D.volume) = 0 := by
  rw [weakHarmonicCorrection,D.weakDirichletInverse_on_test,
    integral_energyPairingDensity_eq_neg_laplace D.metric D.volume D.metric_volume hf
      v.smooth v.zero_trace]
  have h : (∫ x, (- D.positiveLaplaceLp f hf) x * v x ∂D.volume) =
      -(∫ x, (-nativeLaplace D.metric f x) * v x ∂D.volume) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg (D.positiveLaplaceLp f hf),D.positiveLaplaceLp_ae_eq f hf]
      with x hx hy
    rw [hx,Pi.neg_apply,hy]
    exact neg_mul _ _
  rw [h,neg_add_cancel]

end CalderonPatch.DirichletData

module

public import Proof.CalderonN.NormalEndpointHessian
public import Proof.CalderonN.MetricConnection

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma hasDerivAt_metricPair_curve {Ω : Set (X dim)} (hΩ : IsOpen Ω) {K : ℝ} {g : (MetricField dim)}
    (hg : Elliptic Ω K g) {x U V : ℝ → (X dim)} {t : ℝ} {a b c : (X dim)}
    (hx : HasDerivAt x a t) (hU : HasDerivAt U b t) (hV : HasDerivAt V c t) (ht : x t ∈ Ω) :
    HasDerivAt (fun s => metricPair g (x s) (U s) (V s))
      (metricDifferential g (x t) a (U t) (V t)+
        metricPair g (x t) b (V t)+metricPair g (x t) (U t) c) t := by
  have hG (i j : (I dim)) := (((hg.1 i j).contDiffAt (hΩ.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hx
  have hU' (i : (I dim)) := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp_hasDerivAt t hU
  have hV' (i : (I dim)) := (EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp_hasDerivAt t hV
  have hsum := HasDerivAt.sum (u:=Finset.univ) (fun i _ =>
    HasDerivAt.sum (u:=Finset.univ) (fun j _ => ((hG i j).mul (hU' i)).mul (hV' j)))
  convert hsum using 1
  · funext s
    simp [metricPair]
  · simp only [metricDifferential_apply,metricPair,PiLp.proj_apply,Function.comp_apply,Pi.mul_apply,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The vertical differential of the admitted normal-coordinate map. -/
def normalVerticalJacobian (expMap : X dim × X dim → X dim) (y v : X dim) : X dim →L[ℝ] X dim :=
  (fderiv ℝ expMap (y,v)).comp (ContinuousLinearMap.inr ℝ (X dim) (X dim))

/-- The normal pullback metric after removing the square of the scaling radius.
    Both tangent arguments use the actual vertical derivative of expMap. -/
def normalPullbackMetricPair (g : (MetricField dim)) (expMap : (X dim) × (X dim) → (X dim))
    (y : (X dim)) (s : ℝ) (z u v : (X dim)) : ℝ :=
  metricPair g (expMap (y,s • z))
    (fderiv ℝ expMap (y,s • z) (0,u)) (fderiv ℝ expMap (y,s • z) (0,v))

lemma NormalCoordinates.normalPullbackMetricPair_zero {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) (e : (Frame dim))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (z u v : (X dim)) :
    normalPullbackMetricPair g expMap y 0 z u v = metricPair g y u v := by
  simp only [normalPullbackMetricPair,zero_smul,hN.exp_zero hy,hN.vertical_zero hy e hframe]

/-- The actual rescaled normal metric has zero first radius derivative at zero.
    This cancellation uses the geodesic Hessian and metric compatibility, and is
    independent of any special construction of the radius profile. -/
theorem NormalCoordinates.normalPullbackMetricPair_first_zero {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y) (hyΩ : y ∈ Ω) (e : (Frame dim))
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0) (z u v : (X dim)) :
    HasDerivAt (fun s : ℝ => normalPullbackMetricPair g expMap y s z u v) 0 0 := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hZero : (y,(0:(X dim))) ∈ U := hTube ⟨hy,zero_mem_disk g y (R y)⟩
  have hcurve : HasDerivAt (fun s : ℝ => (y,s • z)) ((0:(X dim)),z) 0 := by
    convert (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const z) using 1 <;>
      simp only [Function.id_def,one_smul]
  have hE : HasFDerivAt expMap (fderiv ℝ expMap (y,0)) (y,(0:ℝ) • z) := by
    simpa only [zero_smul] using (hN.differentiableAt_zero hy).hasFDerivAt
  have hx : HasDerivAt (fun s : ℝ => expMap (y,s • z)) z 0 := by
    simpa only [Function.comp_def,hN.vertical_zero hy e hframe] using hE.comp_hasDerivAt 0 hcurve
  have hD := ((hReg.fderiv_of_isOpen (m:=∞) hU (by simp)).contDiffAt (hU.mem_nhds hZero)).differentiableAt (by simp)
  have hD' : HasFDerivAt (fderiv ℝ expMap) (fderiv ℝ (fderiv ℝ expMap) (y,0)) (y,(0:ℝ) • z) := by
    simpa only [zero_smul] using hD.hasFDerivAt
  have hJac (w : (X dim)) : HasDerivAt (fun s : ℝ => fderiv ℝ expMap (y,s • z) (0,w))
      (-connection g y z w) 0 := by
    have hd := (hD'.comp_hasDerivAt 0 hcurve).clm_apply (hasDerivAt_const (0:ℝ) ((0:(X dim)),w))
    simpa only [Function.comp_def,zero_smul,map_zero,add_zero,
      hN.second_vertical hΩ hg hy hyΩ z w] using hd
  have hp : expMap (y,(0:ℝ) • z) ∈ Ω := by simpa only [zero_smul,hN.exp_zero hy] using hyΩ
  have hd := hasDerivAt_metricPair_curve hΩ hg hx (hJac u) (hJac v) hp
  simp only [zero_smul,hN.exp_zero hy,hN.vertical_zero hy e hframe] at hd
  have hm := connection_metric hΩ hg hK hyΩ z u v
  have hval : metricDifferential g y z u v+metricPair g y (-connection g y z u) v+
      metricPair g y u (-connection g y z v) = 0 := by
    simp only [← metricBilinear_apply,map_neg,_root_.neg_apply]
    simp only [metricBilinear_apply]
    linarith only [hm]
  rw [hval] at hd
  exact hd

end CalderonN

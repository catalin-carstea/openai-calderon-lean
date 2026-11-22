module

public import Proof.CalderonN.CoordinateTraceEnergyBound
public import Proof.CalderonN.PhysicalTraceLowerOrderMass
public import Proof.CalderonN.SmoothEnergyRegularity

import Proof.CalderonN.PhysicalAngularModelData
import Proof.CalderonN.SmoothTraceAngularCommutator
import Proof.CalderonN.ActualGaussConormalBounds
import Mathlib.Tactic

/-! The coordinate energies of the two real trace components use the
same compact physical test and are dominated by its frozen energy density. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}

theorem physical_coordinateTraceEnergy_le (hn : 3 ≤ dim) (hY : IsOpen Y)
    {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K) (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {r : X dim → ℝ} {φ : Field dim} (hφ : Test Y g e φ) (E : HarmonicTestExpansion Y g e φ)
    (M : AngularModelData E r) {x : X dim} (hx : x ∈ Y) (hβ : 1 ≤ beta g r x)
    (J : ℝ) (hJ : 0 ≤ J)
    (hEntry : ∀ a i,|traceFrameCoordinate g e a i x| ≤ J)
    (hΓ : ∀ i a b,|frameConnectionCoefficient g e x (axis i) a b| ≤ J) :
    let C := (dim:ℝ)*J+(dim:ℝ)^2*(J*(2*(dim:ℝ)))
    metricDensity g x*(coordinateTraceEnergy hn (beta g r) (E.traceComponent Complex.reCLM) x+
      coordinateTraceEnergy hn (beta g r) (E.traceComponent Complex.imCLM) x) ≤
        (2*(dim:ℝ)*C^2+1)*physicalEnergyDensity g e r φ x := by
  dsimp only
  let H (a : I dim) := supportedHorizontal hY hg hK he (fun y => e y a) (he a)
  let U := E.traceComponent Complex.reCLM
  let V := E.traceComponent Complex.imCLM
  let β := beta g r x
  let C := (dim:ℝ)*J+(dim:ℝ)^2*(J*(2*(dim:ℝ)))
  let N := 2*(dim:ℝ)*C^2+1
  let d (u : SmoothSupportedTraceSection Y) :=
    β⁻¹*(∑ a,traceOrderNorm hn 2 (smoothSupportedTraceFiberL x (H a u))^2)+
      β*traceOrderNorm hn 3 (smoothSupportedTraceFiberL x u)^2
  have hRot := smoothTraceRotation_angularBound hn
  have hU : coordinateTraceEnergy hn (beta g r) U x ≤ N*d U :=
    coordinateTraceEnergy_le_horizontal hn hY hg hK he hframe hx (beta g r) hβ J (2*(dim:ℝ))
      hJ (by positivity) hEntry hΓ hRot U
  have hV : coordinateTraceEnergy hn (beta g r) V x ≤ N*d V :=
    coordinateTraceEnergy_le_horizontal hn hY hg hK he hframe hx (beta g r) hβ J (2*(dim:ℝ))
      hJ (by positivity) hEntry hΓ hRot V
  have hMass : sobolevSq g e (3/2:ℝ) x (fun z => φ (x,z)) =
      traceOrderNorm hn 3 (smoothSupportedTraceFiberL x U)^2+
      traceOrderNorm hn 3 (smoothSupportedTraceFiberL x V)^2 := by
    rw [traceOrderNorm_threeHalf_eq,traceOrderNorm_threeHalf_eq]
    exact E.sobolevSq_eq_traceComponents hn hx (hframe x hx) _ (by norm_num)
  have hH (i : I dim) :
      sobolevSq g e (1/2:ℝ) x (fun z => horizontal g φ x z (e x i)) =
        traceOrderNorm hn 2 (smoothSupportedTraceFiberL x (H i U))^2+
        traceOrderNorm hn 2 (smoothSupportedTraceFiberL x (H i V))^2 := by
    have hu : H i U = M.realComponent.horizontalTraceComponent i :=
      supportedHorizontal_traceComponent hY hg hK he hframe hφ.1 M.realComponent i
    have hv : H i V = M.imagComponent.horizontalTraceComponent i :=
      supportedHorizontal_traceComponent hY hg hK he hframe hφ.1 M.imagComponent i
    rw [hu,hv,traceOrderNorm_half_eq,traceOrderNorm_half_eq]
    exact sobolevSq_eq_supportedTraceComponents hn (hframe x hx)
      (fun z => horizontal g φ x z (e x i)) _ _
      (M.realComponent.horizontalTraceComponent_apply i hx)
      (M.imagComponent.horizontalTraceComponent_apply i hx) _ (by norm_num)
  have hWeights : d U+d V =
      β⁻¹*(∑ i,sobolevSq g e (1/2:ℝ) x (fun z => horizontal g φ x z (e x i)))+
        β*sobolevSq g e (3/2:ℝ) x (fun z => φ (x,z)) := by
    simp only [d,hMass,hH,Finset.sum_add_distrib]
    ring
  have hBase : 0 ≤ (∑ i,fiberSq e x (fun z => horizontal g φ x z (e x i))) :=
    Finset.sum_nonneg fun i _ => fiberSq_nonneg _ _ _
  have hAngular : 0 ≤ sobolevSq g e 1 x (fun z => φ (x,z)) := sobolevSq_nonneg _ _ _ _ _
  have hN : 0 ≤ N := by dsimp only [N,C]; positivity
  have hμ : 0 ≤ metricDensity g x := Real.sqrt_nonneg _
  calc
    _ ≤ metricDensity g x*(N*d U+N*d V) := mul_le_mul_of_nonneg_left (add_le_add hU hV) hμ
    _ = N*(metricDensity g x*(d U+d V)) := by ring
    _ ≤ N*physicalEnergyDensity g e r φ x := by
      apply mul_le_mul_of_nonneg_left _ hN
      rw [hWeights]
      unfold physicalEnergyDensity
      apply mul_le_mul_of_nonneg_left _ hμ
      nlinarith only [hBase,mul_nonneg (sq_nonneg β) hAngular]

end CalderonN

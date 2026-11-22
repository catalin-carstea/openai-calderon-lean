module

public import Proof.CalderonN.SupportedTraceFiberBounds
public import Proof.CalderonN.TraceCoordinateHorizontalRaisingComm
public import Proof.CalderonN.FlatTraceRaisingBounds

import Mathlib.Tactic

/-! Quantify the two leading-translation terms of the physical
remainder after the radius cancellation. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}
variable (hn : 3 ≤ dim) (hY : IsOpen Y) {K : ℝ} {g : MetricField dim} {e : Frame dim}
  (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

theorem supportedRaising_fiber_bound {x : X dim} (hx : x ∈ Y) (C : ℝ)
    (hRaise : ∀ a : I dim,SmoothTraceAngularBound hn 1 C (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) a))
    (a : I dim) :
    SupportedTraceFiberBound hn x 1 C (supportedRaising hA hEll S hY a) := by
  let B := smoothTraceFlatDegree hA hEll S
  refine ⟨smoothTraceRaising B a,smoothTraceLowering B a,?_,hRaise a,?_⟩
  · exact smoothTraceRaising_adjoint hn B (smoothTraceFlatDegree_symmetric hn hA hEll S) a
  · intro u
    exact smoothSupportedTraceFiberAction_fiber hY _ _ u x

theorem supportedCoordinateRaising_fiber_bound {x : X dim} (hx : x ∈ Y) (C D : ℝ) (hC : 0 ≤ C)
    (hRaise : ∀ a : I dim,SmoothTraceAngularBound hn 1 C (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) a))
    (hEntry : ∀ i a, |traceFrameCoordinate g e a i x| ≤ D) (i : I dim) :
    SupportedTraceFiberBound hn x 1 ((dim:ℝ)*(D*C)) (supportedCoordinateRaising hY hg he hA hEll S i) := by
  unfold supportedCoordinateRaising
  have h (a : I dim) := (supportedRaising_fiber_bound hn hY hA hEll S hx C hRaise a).base_mul hY
    (traceFrameCoordinate g e a i) (contDiffOn_traceFrameCoordinate hg he a i)
  have hh := SupportedTraceFiberBound.sum Finset.univ _ (fun _ : I dim => D*C)
    (fun a _ => (h a).enlarge (mul_le_mul_of_nonneg_right (hEntry i a) hC))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh

theorem supportedCoordinateHorizontal_comm_raising_bound
    (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)
    {x : X dim} (hx : x ∈ Y) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hRaise : ∀ a : I dim,SmoothTraceAngularBound hn 1 C (smoothTraceRaising (smoothTraceFlatDegree hA hEll S) a))
    (hEntry : ∀ i a, |traceFrameCoordinate g e a i x| ≤ D)
    (hDEntry : ∀ i j a, |coordDeriv i (traceFrameCoordinate g e a j) x| ≤ D)
    (hΓ : ∀ i a b, |frameConnectionCoefficient g e x (axis i) a b| ≤ D) (i j : I dim) :
    let H := supportedCoordinateHorizontal hY hg hK he i
    let R := supportedCoordinateRaising hY hg he hA hEll S j
    SupportedTraceFiberBound hn x 1 ((dim:ℝ)*(D*C+D*((dim:ℝ)*(D*C)))) (H*R-R*H) := by
  dsimp only
  rw [supportedCoordinateHorizontal_comm_coordinateRaising hY hg hK he hframe hn hA hEll S i j]
  let R₀ := supportedRaising hA hEll S hY
  let f (a : I dim) := traceFrameCoordinate g e a j
  let hf (a : I dim) := contDiffOn_traceFrameCoordinate hg he a j
  let Γ (a b : I dim) (y : X dim) := frameConnectionCoefficient g e y (axis i) a b
  let hΓS (a b : I dim) : ContDiffOn ℝ ∞ (Γ a b) Y :=
    hg.contDiffOn_frameConnection hY hK e he (fun _ => axis i) contDiffOn_const a b
  let M (a b : I dim) := smoothSupportedTraceBaseMul hY (Γ a b) (hΓS a b)
  have h0 (a : I dim) := supportedRaising_fiber_bound hn hY hA hEll S hx C hRaise a
  have h1 (a : I dim) : SupportedTraceFiberBound hn x 1 ((dim:ℝ)*(D*C)) (∑ b : I dim,M a b*R₀ b) := by
    have h := SupportedTraceFiberBound.sum Finset.univ _ (fun _ : I dim => D*C) (fun b _ =>
      ((h0 b).base_mul hY (Γ a b) (hΓS a b)).enlarge (mul_le_mul_of_nonneg_right (hΓ i a b) hC))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have h2 (a : I dim) :=
    ((h1 a).base_mul hY (f a) (hf a)).enlarge (mul_le_mul_of_nonneg_right (hEntry j a) (by positivity))
  have h3 (a : I dim) := ((h0 a).base_mul hY (coordDeriv i (f a))
    (((hf a).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const)).enlarge
      (mul_le_mul_of_nonneg_right (hDEntry i j a) hC)
  have h := SupportedTraceFiberBound.sum Finset.univ _ (fun _ : I dim => D*C+D*((dim:ℝ)*(D*C)))
    (fun a _ => (h3 a).add (h2 a))
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end CalderonN

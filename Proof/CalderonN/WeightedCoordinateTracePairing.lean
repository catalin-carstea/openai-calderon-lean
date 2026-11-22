module

public import Proof.CalderonN.IntegratedCoordinateTraceError
public import Proof.CalderonN.SmoothSupportedFiberJetCalculus

import Mathlib.Tactic

/-! A pairing with at most one base derivative on either test
argument can distribute its angular order across both factors. -/

public section

noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem SmoothTraceAngularBound.abs_pair_apply_le (hn : 3 ≤ dim)
    {k l : ℕ} {C D : ℝ} {S T : Module.End ℝ (SmoothSphereTrace dim)}
    (hS : SmoothTraceAngularBound hn k C S) (hT : SmoothTraceAngularBound hn l D T) (hC : 0 ≤ C)
    (i j m : Fin 4) (hij : j.val = i.val+k) (him : m.val = i.rev.val+l)
    (u v : SmoothSphereTrace dim) :
    |⟪smoothSphereTraceL2 hn (S u),smoothSphereTraceL2 hn (T v)⟫_ℝ| ≤
      (C*D)*traceOrderNorm hn j u*traceOrderNorm hn m v := by
  have e : -traceOrderExponent i.rev = traceOrderExponent i := by rw [traceOrderExponent_rev,neg_neg]
  have h := abs_smoothTrace_inner_le_sobolev hn (traceOrderExponent i.rev) (traceOrderExponent_le i.rev)
    (by rw [e]; exact traceOrderExponent_le i) (S u) (T v)
  rw [smoothSphereTraceSobolev_order_eq hn e _ (traceOrderExponent_le _)] at h
  refine h.trans ((mul_le_mul (hS i j hij u) (hT i.rev m him v) (norm_nonneg _)
    (mul_nonneg hC (norm_nonneg _))).trans_eq ?_)
  ring

@[expose] def traceCoordinateTest (u : SmoothSupportedTraceSection Y) :
    Option (I dim) → SmoothSupportedTraceSection Y
  | none => u
  | some i => smoothSupportedTraceBaseDiff (axis i) u

@[expose] def traceCoordinateTestOrder {ι : Type*} : Option ι → Fin 4
  | none => 3
  | some _ => 2

@[expose] def traceCoordinatePairWeight {ι : Type*} (β : ℝ) : Option ι → Option ι → ℝ
  | none, none => β
  | some _, some _ => β⁻¹
  | _, _ => 1

private theorem coordinateTraceWeight_mul_norms (hn : 3 ≤ dim)
    (β : X dim → ℝ) (u : SmoothSupportedTraceSection Y) (x : X dim) (hβ : 0 < β x)
    (i j : Option (I dim)) :
    traceCoordinatePairWeight (β x) i j*
      traceOrderNorm hn (traceCoordinateTestOrder i) (smoothSupportedTraceFiberL x (traceCoordinateTest u i))*
      traceOrderNorm hn (traceCoordinateTestOrder j) (smoothSupportedTraceFiberL x (traceCoordinateTest u j)) ≤
        coordinateTraceEnergy hn β u x := by
  let b := β x
  let h (i : I dim) := traceOrderNorm hn 2
    (smoothSupportedTraceFiberL x (smoothSupportedTraceBaseDiff (axis i) u))
  let v := traceOrderNorm hn 3 (smoothSupportedTraceFiberL x u)
  let E := coordinateTraceEnergy hn β u x
  have hS : 0 ≤ ∑ i,h i^2 := Finset.sum_nonneg fun i _ => sq_nonneg (h i)
  have hV : b*v^2 ≤ E := le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr hβ.le) hS)
  have hH (i : I dim) : b⁻¹*h i^2 ≤ E := by
    have hi : h i^2 ≤ ∑ j,h j^2 := Finset.single_le_sum (fun j _ => sq_nonneg (h j)) (Finset.mem_univ i)
    exact (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hβ.le)).trans
      (le_add_of_nonneg_right (mul_nonneg hβ.le (sq_nonneg v)))
  have hCross (i : I dim) : h i*v ≤ E := by
    apply (mul_le_mul_iff_of_pos_left hβ).mp
    have h₁ := mul_le_mul_of_nonneg_left (hH i) hβ.le
    change b*(b⁻¹*h i^2) ≤ b*E at h₁
    rw [← mul_assoc,mul_inv_cancel₀ hβ.ne',one_mul] at h₁
    have h₂ := mul_le_mul_of_nonneg_left hV hβ.le
    change b*(h i*v) ≤ b*E
    nlinarith only [h₁,h₂,sq_nonneg (h i-b*v)]
  cases i with
  | none =>
    cases j with
    | none =>
      change b*v*v ≤ E
      rw [mul_assoc,← pow_two]
      exact hV
    | some j =>
      change 1*v*h j ≤ E
      rw [one_mul,mul_comm]
      exact hCross j
  | some i =>
    cases j with
    | none =>
      change 1*h i*v ≤ E
      rw [one_mul]
      exact hCross i
    | some j =>
      change b⁻¹*h i*h j ≤ E
      have h' := mul_nonneg (inv_nonneg.mpr hβ.le) (sq_nonneg (h i-h j))
      change 0 ≤ b⁻¹*(h i-h j)^2 at h'
      nlinarith only [hH i,hH j,h']

theorem abs_supported_coordinateTrace_pair_le (hn : 3 ≤ dim) (hY : IsOpen Y)
    (μ β e : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (hμ₀ : ∀ x ∈ Y,0 ≤ μ x) (hβ : ∀ x ∈ Y,0 < β x) (he : IntegrableOn e Y)
    (u : SmoothSupportedTraceSection Y) (hEnergy : ∀ x ∈ Y,μ x*coordinateTraceEnergy hn β u x ≤ e x)
    (F G : RegularTraceFiberFamily Y) (i j : Option (I dim)) (a : Fin 4)
    (k l : ℕ) (hi : (traceCoordinateTestOrder i).val = a.val+k)
    (hj : (traceCoordinateTestOrder j).val = a.rev.val+l) (C : ℝ) (hC : 0 ≤ C)
    (hBounds : ∀ x ∈ Y,∃ D E : ℝ,0 ≤ D ∧ 0 ≤ E ∧
      SmoothTraceAngularBound hn k D (F.1 x) ∧ SmoothTraceAngularBound hn l E (G.1 x) ∧
      D*E ≤ C*traceCoordinatePairWeight (β x) i j) :
    let B := smoothSupportedTracePairingL hn hY μ hμ
    |B (F.action hY (traceCoordinateTest u i)) (G.action hY (traceCoordinateTest u j))| ≤
      C*(∫ x in Y,e x) := by
  dsimp only
  let v := F.action hY (traceCoordinateTest u i)
  let w := G.action hY (traceCoordinateTest u j)
  let vol := (volume : Measure (X dim)).restrict Y
  change |smoothSupportedTracePairing hn μ v w| ≤ C*(∫ x,e x ∂vol)
  rw [smoothSupportedTracePairing_eq_setIntegral]
  apply abs_integral_weighted_trace_error_le vol
    ((integrable_smoothSupportedTracePairing_integrand_local hn hY μ hμ v w).integrableOn (s:=Y)) he
  filter_upwards [ae_restrict_mem hY.measurableSet] with x hx
  obtain ⟨D,E,hD,_,hF,hG,hDE⟩ := hBounds x hx
  let V := smoothSupportedTraceFiberL x (traceCoordinateTest u i)
  let W := smoothSupportedTraceFiberL x (traceCoordinateTest u j)
  let n := traceOrderNorm hn (traceCoordinateTestOrder i) V
  let m := traceOrderNorm hn (traceCoordinateTestOrder j) W
  have hn₀ : 0 ≤ n := norm_nonneg _
  have hm₀ : 0 ≤ m := norm_nonneg _
  have hPair := SmoothTraceAngularBound.abs_pair_apply_le hn hF hG hD a _ _ hi hj V W
  have hW := coordinateTraceWeight_mul_norms hn β u x (hβ x hx) i j
  simp only [abs_mul,abs_of_nonneg (hμ₀ x hx),v,w,smoothSupportedTraceL2,RegularTraceFiberFamily.action_fiber]
  calc
    _ ≤ μ x*((D*E)*n*m) := mul_le_mul_of_nonneg_left hPair (hμ₀ x hx)
    _ ≤ μ x*((C*traceCoordinatePairWeight (β x) i j)*n*m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDE hn₀) hm₀) (hμ₀ x hx)
    _ = C*(μ x*(traceCoordinatePairWeight (β x) i j*n*m)) := by ring
    _ ≤ C*(μ x*coordinateTraceEnergy hn β u x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (hμ₀ x hx)) hC
    _ ≤ C*e x := mul_le_mul_of_nonneg_left (hEnergy x hx) hC

end CalderonN

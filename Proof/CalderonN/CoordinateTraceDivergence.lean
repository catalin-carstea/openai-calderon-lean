module

public import Proof.CalderonN.PairedTraceFiberFamily
public import Proof.CalderonN.MovingTraceFirstOrderForms
public import Proof.CalderonN.SmoothSupportedHorizontalAdjoint

import Proof.CalderonN.ProductHarmonicDerivatives
import Proof.CalderonN.SmoothSupportedTraceBaseAdjoint
import Mathlib.Tactic

/-! Coordinate first-order and divergence-form operators on the
smooth supported trace core. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem smoothSupportedTraceBaseDiff_comm (a b : X dim) :
    smoothSupportedTraceBaseDiff (Y:=Y) a*smoothSupportedTraceBaseDiff b =
      smoothSupportedTraceBaseDiff b*smoothSupportedTraceBaseDiff a := by
  ext u : 1
  obtain ⟨G,hG,hu⟩ := smoothSupportedTraceSection_repr u
  apply Subtype.ext
  funext ⟨x,z⟩
  have hDir (a : X dim) (x : X dim) (z : ↥(standardSphere dim)) :
      (smoothSupportedTraceBaseDiff a u).1 (x,z) = productDirection G (a,0) (x,z) :=
    standardTraceBaseDiff_of_repr a hG hu x z
  simp only [Module.End.mul_apply,smoothSupportedTraceBaseDiff_apply]
  rw [standardTraceBaseDiff_of_repr a (contDiff_productDirection hG (b,0)) (hDir b),
    standardTraceBaseDiff_of_repr b (contDiff_productDirection hG (a,0)) (hDir a)]
  exact congrFun (productDirection_comm hG (b,0) (a,0)) (x,z)

@[expose] def coordinateTraceDensity (hY : IsOpen Y) (μ : X dim → ℝ)
    (hμ : ContDiffOn ℝ ∞ μ Y) (hμ₀ : ∀ x ∈ Y,0 < μ x) (i : I dim) :
    RegularTraceFiberFamily Y :=
  RegularTraceFiberFamily.scalar hY (traceDensityDivergence μ (fun _ => axis i))
    (contDiffOn_traceDensityDivergence hY μ hμ hμ₀ _ contDiffOn_const)

theorem coordinateTraceBaseAdjoint (hn : 3 ≤ dim) (hY : IsOpen Y) (μ : X dim → ℝ)
    (hμ : ContDiffOn ℝ ∞ μ Y) (hμ₀ : ∀ x ∈ Y,0 < μ x) (i : I dim) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (smoothSupportedTraceBaseDiff (axis i))
      (-smoothSupportedTraceBaseDiff (axis i)-(coordinateTraceDensity hY μ hμ hμ₀ i).action hY) := by
  let f (x : X dim) := coordDeriv i μ x/μ x
  have hf : ContDiffOn ℝ ∞ f Y :=
    ((hμ.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const).div hμ
      (fun x hx => (hμ₀ x hx).ne')
  have he : EqOn (traceDensityDivergence μ (fun _ => axis i)) f Y := by
    intro x hx
    rw [traceDensityDivergence_eq_coordinate_sum hY μ hμ hμ₀ _ contDiffOn_const hx]
    simp [f,coordDeriv,axis,PiLp.single_apply]
  rw [coordinateTraceDensity,RegularTraceFiberFamily.action_scalar,
    smoothSupportedTraceBaseMul_congr hY _ hf he]
  exact fun u v => smoothSupportedTrace_coordinate_adjoint hn hY μ hμ hμ₀ i u v

structure CoordinateTraceFirstOrder (Y : Set (X dim)) where
  first : I dim → RegularTraceFiberFamily Y
  zero : RegularTraceFiberFamily Y

namespace CoordinateTraceFirstOrder

@[expose] def action (hY : IsOpen Y) (S : CoordinateTraceFirstOrder Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  (∑ i,(S.first i).action hY*smoothSupportedTraceBaseDiff (axis i))+S.zero.action hY

@[expose] def zeroOrder (hY : IsOpen Y) (F : RegularTraceFiberFamily Y) :
    CoordinateTraceFirstOrder Y :=
  ⟨fun _ => RegularTraceFiberFamily.scalar hY (fun _ => 0) contDiffOn_const,F⟩

end CoordinateTraceFirstOrder

structure CoordinateTraceDivergence (hn : 3 ≤ dim) (Y : Set (X dim)) where
  density : I dim → RegularTraceFiberFamily Y
  second : I dim → I dim → PairedTraceFiberFamily hn Y
  first : I dim → PairedTraceFiberFamily hn Y
  zero : PairedTraceFiberFamily hn Y

namespace CoordinateTraceDivergence

variable {hn : 3 ≤ dim}

@[expose] def baseAdjoint (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) (i : I dim) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  -smoothSupportedTraceBaseDiff (axis i)-(U.density i).action hY

@[expose] def principal (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  ∑ i,∑ j,U.baseAdjoint hY i*(U.second i j).forward.action hY*smoothSupportedTraceBaseDiff (axis j)

@[expose] def action (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  U.principal hY+(∑ i,(U.first i).forward.action hY*smoothSupportedTraceBaseDiff (axis i))+U.zero.forward.action hY

@[expose] def adjointAction (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) :
    Module.End ℝ (SmoothSupportedTraceSection Y) :=
  U.principal hY+(∑ i,U.baseAdjoint hY i*(U.first i).reverse.action hY)+U.zero.reverse.action hY

theorem paired (hY : IsOpen Y) (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
    (U : CoordinateTraceDivergence hn Y)
    (hD : ∀ i,PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ)
      (smoothSupportedTraceBaseDiff (axis i)) (U.baseAdjoint hY i))
    (hA : ∀ i j,(U.second i j).reverse.action hY = (U.second j i).forward.action hY) :
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) (U.action hY) (U.adjointAction hY) := by
  let B := smoothSupportedTracePairingL hn hY μ hμ
  have hSym : ∀ u v,B u v = B v u := smoothSupportedTracePairing_symm hn μ
  have hPrincipal : PairedAdjoint B (U.principal hY) (U.principal hY) := by
    unfold principal
    conv_rhs => rw [Finset.sum_comm]
    refine PairedAdjoint.sum Finset.univ _ _ (fun i _ =>
      PairedAdjoint.sum Finset.univ _ _ (fun j _ => ?_))
    rw [← hA i j]
    simpa only [mul_assoc] using (((hD i).swap_of_symmetric hSym).mul ((U.second i j).pairedAction hY μ hμ)).mul (hD j)
  unfold action adjointAction
  exact (hPrincipal.add (PairedAdjoint.sum Finset.univ _ _ (fun i _ =>
    ((U.first i).pairedAction hY μ hμ).mul (hD i)))).add (U.zero.pairedAction hY μ hμ)

@[expose] def skewZeroSymbol (U : CoordinateTraceDivergence hn Y) : RegularTraceFiberFamily Y :=
  U.zero.reverse.sub U.zero.forward

@[expose] def skewZeroDerivative (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) :
    RegularTraceFiberFamily Y :=
  (RegularTraceFiberFamily.finiteSum Finset.univ (fun i =>
    ((U.first i).reverse.derivative hY (axis i)).add ((U.density i).mul hY (U.first i).reverse))).neg

@[expose] def skew (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) : CoordinateTraceFirstOrder Y :=
  ⟨fun i => (U.first i).reverse.neg.sub (U.first i).forward,
    U.skewZeroSymbol.add (U.skewZeroDerivative hY)⟩

theorem adjointAction_sub_action (hY : IsOpen Y) (U : CoordinateTraceDivergence hn Y) :
    U.adjointAction hY-U.action hY = (U.skew hY).action hY := by
  unfold adjointAction action CoordinateTraceFirstOrder.action skew skewZeroSymbol skewZeroDerivative
  have h (i : I dim) :
      U.baseAdjoint hY i*(U.first i).reverse.action hY-
        (U.first i).forward.action hY*smoothSupportedTraceBaseDiff (axis i) =
      ((U.first i).reverse.neg.sub (U.first i).forward).action hY*smoothSupportedTraceBaseDiff (axis i)-
        (((U.first i).reverse.derivative hY (axis i)).add ((U.density i).mul hY (U.first i).reverse)).action hY := by
    simp only [RegularTraceFiberFamily.action_derivative,RegularTraceFiberFamily.action_mul,
      RegularTraceFiberFamily.action_add,RegularTraceFiberFamily.action_sub,RegularTraceFiberFamily.action_neg]
    have hh := pairedAdjoint_difference_divergence_first ((U.first i).forward.action hY)
      ((U.first i).reverse.action hY) 0 0 (smoothSupportedTraceBaseDiff (axis i))
      (U.baseAdjoint hY i) ((U.density i).action hY) rfl
    simp only [add_zero,sub_self,zero_sub] at hh
    rw [hh]
    abel
  have hf := congrArg (∑ i : I dim, · i) (funext h)
  simp only [RegularTraceFiberFamily.action_finiteSum,RegularTraceFiberFamily.action_add,
    RegularTraceFiberFamily.action_neg,RegularTraceFiberFamily.action_sub] at hf ⊢
  let U₁ (i : I dim) := U.baseAdjoint hY i*(U.first i).reverse.action hY
  let U₂ (i : I dim) := (U.first i).forward.action hY*smoothSupportedTraceBaseDiff (axis i)
  let U₃ (i : I dim) := (-(U.first i).reverse.action hY-(U.first i).forward.action hY)*
    smoothSupportedTraceBaseDiff (axis i)
  let U₄ (i : I dim) := ((U.first i).reverse.derivative hY (axis i)).action hY+
    ((U.density i).mul hY (U.first i).reverse).action hY
  change (∑ i,(U₁ i-U₂ i)) = (∑ i,(U₃ i-U₄ i)) at hf
  have h₁ : (∑ i,(U₁ i-U₂ i)) = (∑ i,U₁ i)-(∑ i,U₂ i) := Finset.sum_sub_distrib U₁ U₂
  have h₂ : (∑ i,(U₃ i-U₄ i)) = (∑ i,U₃ i)-(∑ i,U₄ i) := Finset.sum_sub_distrib U₃ U₄
  rw [h₁,h₂] at hf
  change U.principal hY+(∑ i,U₁ i)+U.zero.reverse.action hY-
    (U.principal hY+(∑ i,U₂ i)+U.zero.forward.action hY) =
    (∑ i,U₃ i)+(U.zero.reverse.action hY-U.zero.forward.action hY+ -(∑ i,U₄ i))
  calc
    _ = ((∑ i,U₁ i)-(∑ i,U₂ i))+(U.zero.reverse.action hY-U.zero.forward.action hY) := by abel
    _ = ((∑ i,U₃ i)-(∑ i,U₄ i))+(U.zero.reverse.action hY-U.zero.forward.action hY) := by rw [hf]
    _ = _ := by abel

end CoordinateTraceDivergence

end CalderonN

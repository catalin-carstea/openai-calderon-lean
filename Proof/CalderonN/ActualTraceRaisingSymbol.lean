module

public import Proof.CalderonN.ActualTracePrimitivePairs

import Mathlib.Tactic

/-! The frozen raising and lowering operators belong to the same
angular calculus as the conormal and multiplication coefficients. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)} {hn : 3 ≤ dim}

namespace PairedTraceFiberFamily

variable {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
  {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
  {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f)

@[expose] def raising (hY : IsOpen Y) (i : I dim) : PairedTraceFiberFamily hn Y :=
  ⟨⟨fun _ => smoothTraceRaising (smoothTraceFlatDegree hA hEll S) i,
      smoothSupportedTraceFiberRegular_raising hA hEll S hY i⟩,
    ⟨fun _ => smoothTraceLowering (smoothTraceFlatDegree hA hEll S) i,
      smoothSupportedTraceFiberRegular_lowering hA hEll S hY i⟩,
    fun _ _ => smoothTraceRaising_adjoint hn _ (smoothTraceFlatDegree_symmetric hn hA hEll S) i⟩

theorem raising_bounds {R : Module.End ℝ (SmoothSphereTrace dim)} {J C : ℝ}
    (H : ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S) R J C) (hJ : 1 ≤ J)
    (hY : IsOpen Y) (x : X dim) (hx : x ∈ Y) (β : ℝ) (hβ : 0 ≤ β) (N : ℕ) (i : I dim) :
    PairedTraceFiberFamilyBounds H.atoms hY x β N 1 (2*C*C+(dim:ℝ)*(2*C*C)) (raising hA hEll S hY i) := by
  let B := smoothTraceFlatDegree hA hEll S
  let M (j : I dim) := H.multiplier (smoothCoordinateData j) (coordinateData_hasJets j J hJ)
  have ha : SmoothTraceSymbolBounds H.atoms 1 (2*C*C+(dim:ℝ)*(2*C*C)) (smoothTraceRaising B i) := by
    rw [smoothTraceRaising_eq_coordinate_rotation]
    refine (H.degree.mul (M i)).sub ?_
    have h := SmoothTraceSymbolBounds.finite_sum Finset.univ _ (fun _ : I dim => 2*C*C)
      (H.identity.zero_of_identity 1) (fun j _ => (H.rotation j i).mul (M j))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  have ha' : SmoothTraceSymbolBounds H.atoms 1 (2*C*C+(dim:ℝ)*(2*C*C)) (smoothTraceLowering B i) := by
    unfold smoothTraceLowering
    refine ((M i).mul H.degree).add ?_
    have h := SmoothTraceSymbolBounds.finite_sum Finset.univ _ (fun _ : I dim => 2*C*C)
      (H.identity.zero_of_identity 1) (fun j _ => (M j).mul (H.rotation j i))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h
  exact ⟨SmoothSupportedFiberJetBound.constFamily _ hx hβ ha.nonneg ha.angular,ha,ha'⟩

end PairedTraceFiberFamily

end CalderonN

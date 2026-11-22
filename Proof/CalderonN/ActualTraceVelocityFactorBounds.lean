module

public import Proof.CalderonN.ActualTraceVelocityFactors

import Mathlib.Tactic

/-! Quantitative closure of the actual affine and normalized
quadratic velocity formulas. -/

public section

noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace ActualTraceVelocityFactors

variable {hn : 3 ≤ dim}

structure Bounds (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim)
    (β : ℝ) (N : ℕ) (C : ℝ) (F : ActualTraceVelocityFactors hn Y) : Prop where
  degree : PairedTraceFiberFamilyBounds A hY x β N 1 C F.degree
  rotations : ∀ a b,PairedTraceFiberFamilyBounds A hY x β N 1 C (F.rotations a b)
  radius : PairedTraceFiberFamilyBounds A hY x β N 0 C F.radius
  half : PairedTraceFiberFamilyBounds A hY x β N 0 C F.half
  densityLinear : PairedTraceFiberFamilyBounds A hY x β N 0 C F.densityLinear
  reciprocal : PairedTraceFiberFamilyBounds A hY x β N 0 C F.reciprocal
  reciprocalLinear : PairedTraceFiberFamilyBounds A hY x β N 0 C F.reciprocalLinear
  reciprocalQuadratic : PairedTraceFiberFamilyBounds A hY x β N 0 C F.reciprocalQuadratic
  conormalQuadratic : PairedTraceFiberFamilyBounds A hY x β N 1 C F.conormalQuadratic
  translation : ∀ i,PairedTraceFiberFamilyBounds A hY x β N 0 C (F.translation i)
  centerNormal : ∀ i,PairedTraceFiberFamilyBounds A hY x β N 0 C (F.centerNormal i)
  centerAngular : ∀ i a b,PairedTraceFiberFamilyBounds A hY x β N 0 C (F.centerAngular i a b)

theorem bounds_of_factors (N : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (A : SmoothTraceSymbolAtoms hn) (hY : IsOpen Y) (x : X dim),x ∈ Y →
      ∀ β : ℝ,0 ≤ β → ∀ I : ℝ,
      SmoothTraceSymbolBounds A 0 I (1 : Module.End ℝ (SmoothSphereTrace dim)) →
      ∀ F : ActualTraceVelocityFactors hn Y,Bounds A hY x β N C F →
      (∀ i,PairedTraceFiberFamilyBounds A hY x β N 1 D (F.affine hY i)) ∧
      (∀ i,PairedTraceFiberFamilyBounds A hY x β N 1 D (F.velocityRemainder hY i)) ∧
      (∀ i,PairedTraceFiberFamilyBounds A hY x β N 1 D (F.lowerVelocity hY i)) := by
  let q := max 2 ((2:ℝ)^N)
  let c := q*(C*C)
  let t := q*(C*(c+c+C))
  let a := q*((t+c)*C)
  let z := C+q*(C*(c+q*((t+c)*C)))
  let p := c+q*(t*C)+c
  let u := q*(p*C)+q*(z*C)+(dim:ℝ)*((dim:ℝ)*c)
  let w := a+q*(C*u)
  let D := a+u+w
  have hc : 0 ≤ c := by dsimp only [c,q]; positivity
  have ht : 0 ≤ t := by dsimp only [t,q]; positivity
  have ha : 0 ≤ a := by dsimp only [a,q]; positivity
  have hz : 0 ≤ z := by dsimp only [z,q]; positivity
  have hp : 0 ≤ p := by dsimp only [p,q]; positivity
  have hu : 0 ≤ u := by dsimp only [u,q]; positivity
  have hw : 0 ≤ w := by dsimp only [w,q]; positivity
  refine ⟨D,by dsimp only [D]; positivity,?_⟩
  intro A hY x hx β hβ K hOne F h
  have h₁ := h.half.mul hx hβ (((h.densityLinear.mul hx hβ h.degree).add hx
    (h.degree.mul hx hβ h.densityLinear)).sub hx (h.densityLinear.weaken hβ (by decide : 0 ≤ 1)))
  have ht' : PairedTraceFiberFamilyBounds A hY x β N 1 t (F.firstConormal hY) := h₁
  have ha' (i : I dim) : PairedTraceFiberFamilyBounds A hY x β N 1 a (F.affine hY i) :=
    (ht'.sub hx (h.degree.mul hx hβ h.densityLinear)).mul hx hβ (h.translation i)
  have hz' : PairedTraceFiberFamilyBounds A hY x β N 1 z (F.normalResponse hY) :=
    h.degree.add hx (h.radius.mul hx hβ ((h.degree.mul hx hβ h.reciprocalLinear).add hx
      ((ht'.add hx (h.radius.mul hx hβ h.conormalQuadratic)).mul hx hβ h.reciprocal)))
  have hp' : PairedTraceFiberFamilyBounds A hY x β N 1 p (F.responseRemainder hY) :=
    ((h.degree.mul hx hβ h.reciprocalQuadratic).add hx (ht'.mul hx hβ h.reciprocalLinear)).add hx
      (h.conormalQuadratic.mul hx hβ h.reciprocal)
  have hSum (i : I dim) : PairedTraceFiberFamilyBounds A hY x β N 1 ((dim:ℝ)*((dim:ℝ)*c))
      (PairedTraceFiberFamily.finiteSum Finset.univ (fun a : I dim =>
        PairedTraceFiberFamily.finiteSum Finset.univ (fun b : I dim => (F.rotations a b).mul hY (F.centerAngular i a b)))) := by
    have hZero := hOne.zero_of_identity 1
    have hh := PairedTraceFiberFamilyBounds.finite_sum hx hβ Finset.univ _
      (fun _ : I dim => ∑ _ : I dim,c) hZero (fun a _ =>
        PairedTraceFiberFamilyBounds.finite_sum hx hβ Finset.univ _ (fun _ : I dim => c) hZero
          (fun b _ => (h.rotations a b).mul hx hβ (h.centerAngular i a b)))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hu' (i : I dim) : PairedTraceFiberFamilyBounds A hY x β N 1 u (F.velocityRemainder hY i) :=
    ((hp'.mul hx hβ (h.translation i)).add hx (hz'.mul hx hβ (h.centerNormal i))).sub hx (hSum i)
  have hw' (i : I dim) : PairedTraceFiberFamilyBounds A hY x β N 1 w (F.lowerVelocity hY i) :=
    (ha' i).add hx (h.radius.mul hx hβ (hu' i))
  exact ⟨fun i => (ha' i).enlarge hβ (by dsimp only [D]; linarith only [hu,hw]),
    fun i => (hu' i).enlarge hβ (by dsimp only [D]; linarith only [ha,hw]),
    fun i => (hw' i).enlarge hβ (by dsimp only [D]; linarith only [ha,hu])⟩

end ActualTraceVelocityFactors

end CalderonN

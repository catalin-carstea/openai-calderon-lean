module

public import Proof.CalderonN.MultiplierDefectTaylorEquation
public import Proof.CalderonN.AngularPoissonEquation

import Proof.CalderonN.MatrixFieldJetNorms
import Mathlib.Tactic

/-! A coefficient variation of the Dirichlet multiplication defect satisfies
a zero-boundary equation. Subtracting its leading variation keeps every
term of the source quadratic in the radius. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem ballRotationCoefficient_isSymm (i j : I dim)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) {V : Set (X dim)} (hV : IsOpen V)
    (hSym : ∀ z ∈ V, (A z).IsSymm) {z : X dim} (hz : z ∈ V) :
    (ballRotationCoefficient i j A z).IsSymm := by
  let J := ballRotationGeneratorL i j
  let S := coordinateMatrix J
  have hS : S.transpose = -S := by
    ext k l
    have h := inner_ballRotationGeneratorL_skew i j (axis l) (axis k)
    simp only [Matrix.transpose_apply,Matrix.neg_apply,S,coordinateMatrix_apply]
    simp only [axis,EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right,
      conj_trivial,one_mul] at h
    exact h
  have hDeriv : ((fderiv ℝ A z) (J z)).IsSymm := by
    ext k l
    have hG : (fun x => A x l k) =ᶠ[nhds z] (fun x => A x k l) := by
      filter_upwards [hV.mem_nhds hz] with x hx
      exact (hSym x hx).apply k l
    have he := congrArg (fun D : X dim →L[ℝ] ℝ => D (J z)) hG.fderiv_eq
    rw [fderiv_matrix_entry A z (hA.differentiable (by simp) z),
      fderiv_matrix_entry A z (hA.differentiable (by simp) z)] at he
    exact he
  change ((fderiv ℝ A z (J z)+A z*S-S*A z).transpose) = fderiv ℝ A z (J z)+A z*S-S*A z
  rw [Matrix.transpose_sub,Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_mul,hDeriv.eq,
    (hSym z hz).eq,hS,Matrix.neg_mul, Matrix.mul_neg]
  abel

theorem linearized_multiplier_defect_equation
    {A B : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (m u v p q : SmoothData dim) (z : X dim)
    (hAS : (A z).IsSymm) (hBS : (B z).IsSymm)
    (hp : negativeBallDivergence A p.1 z = -negativeBallDivergence B u.1 z)
    (hq : negativeBallDivergence A q.1 z = -negativeBallDivergence B v.1 z) :
    negativeBallDivergence A (smoothMultiplierDefect m p q).1 z =
      -negativeBallDivergence B (smoothMultiplierDefect m u v).1 z -
      greenSourceCutoffError B m.1 u.1 z - greenSourceCutoffError A m.1 p.1 z := by
  rw [smoothMultiplierDefect_divergence hA m p q z (fun i j => hAS.apply j i),
    smoothMultiplierDefect_divergence hB m u v z (fun i j => hBS.apply j i),hp,hq]
  ring

theorem linearized_multiplier_defect_remainder_equation
    {A B L : X dim → Mat dim}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hL : ContDiff ℝ ∞ L)
    (r : ℝ) (m u u₀ p p₁ w w₀ t t₁ : SmoothData dim) (z : X dim)
    (ht : negativeBallDivergence A t.1 z =
      -negativeBallDivergence B w.1 z -
      greenSourceCutoffError B m.1 u.1 z - greenSourceCutoffError A m.1 p.1 z)
    (ht₁ : negativeBallDivergence (fun _ => (1 : Mat dim)) t₁.1 z =
      -negativeBallDivergence L w₀.1 z - greenSourceCutoffError L m.1 u₀.1 z -
      greenSourceCutoffError (fun _ => (1 : Mat dim)) m.1 p₁.1 z) :
    let A₀ : X dim → Mat dim := fun _ => 1
    let D := A-A₀
    let R := B-r • L
    negativeBallDivergence A (t.1-r • t₁.1) z =
      -negativeBallDivergence R w.1 z - r*negativeBallDivergence L (w.1-w₀.1) z -
      greenSourceCutoffError R m.1 u.1 z - r*greenSourceCutoffError L m.1 (u.1-u₀.1) z -
      greenSourceCutoffError A m.1 (p.1-r • p₁.1) z -
      r*greenSourceCutoffError D m.1 p₁.1 z - r*negativeBallDivergence D t₁.1 z := by
  dsimp only
  let A₀ : X dim → Mat dim := fun _ => 1
  have hA₀ : ContDiff ℝ ∞ A₀ := contDiff_const
  have hL' : ContDiff ℝ ∞ (r • L) := hL.const_smul r
  let t' : SmoothData dim := ⟨r • t₁.1,t₁.2.const_smul r⟩
  let p' : SmoothData dim := ⟨r • p₁.1,p₁.2.const_smul r⟩
  change negativeBallDivergence A (t.1-t'.1) z = _
  have h₀ : negativeBallDivergence A₀ t₁.1 z =
      -negativeBallDivergence L w₀.1 z - greenSourceCutoffError L m.1 u₀.1 z -
      greenSourceCutoffError A₀ m.1 p₁.1 z := ht₁
  change _ = -negativeBallDivergence (B-r • L) w.1 z -
    r*negativeBallDivergence L (w.1-w₀.1) z -
    greenSourceCutoffError (B-r • L) m.1 u.1 z - r*greenSourceCutoffError L m.1 (u.1-u₀.1) z -
    greenSourceCutoffError A m.1 (p.1-p'.1) z -
    r*greenSourceCutoffError (A-A₀) m.1 p₁.1 z - r*negativeBallDivergence (A-A₀) t₁.1 z
  rw [negativeBallDivergence_sub_solution hA t t',ht,
    show t'.1 = r • t₁.1 from rfl,negativeBallDivergence_const_smul_solution hA t₁,
    negativeBallDivergence_sub_coefficient hB hL',
    negativeBallDivergence_const_smul_coefficient,
    negativeBallDivergence_sub_solution hL w w₀,
    multiplierForcing_sub_coefficients hB hL',multiplierForcing_scale_coefficient,
    multiplierForcing_sub_solution L m u u₀,multiplierForcing_sub_solution A m p p',
    show p'.1 = r • p₁.1 from rfl,multiplierForcing_scale_solution,
    multiplierForcing_sub_coefficients hA hA₀,
    negativeBallDivergence_sub_coefficient hA hA₀,h₀]
  ring

end CalderonN

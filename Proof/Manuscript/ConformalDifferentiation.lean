module

public import Proof.Manuscript.Lemma81Defs
public import Proof.Manuscript.ConformalAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology BigOperators

namespace CalderonPaper

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

@[expose] def directional (v : E) (f : E → V) (x : E) : V := fderiv ℝ f x v

private theorem directional_add {f g : E → V} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    directional v (fun y => f y + g y) x = directional v f x + directional v g x := by
  simp [directional, fderiv_fun_add hf hg]

private theorem directional_sub {f g : E → V} {x v : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    directional v (fun y => f y - g y) x = directional v f x - directional v g x := by
  simp [directional, fderiv_fun_sub hf hg]

private theorem directional_neg {f : E → V} {x v : E} :
    directional v (fun y => -f y) x = -directional v f x := by
  simp [directional, fderiv_fun_neg]

@[simp] private theorem directional_const (v x : E) (c : V) :
    directional v (fun _ => c) x = 0 := by
  simp [directional]

theorem directional_contDiffAt {f : E → V} {x v : E} (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (directional v f) x := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem directional_comm {f : E → V} {x : E} (hf : ContDiffAt ℝ ∞ f x) (u v : E) :
    directional u (directional v f) x = directional v (directional u f) x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  unfold directional
  rw [fderiv_clm_apply hfd (differentiableAt_const v),
    fderiv_clm_apply hfd (differentiableAt_const u)]
  simpa using hf.isSymmSndFDerivAt (by simp) u v

variable {n : ℕ}
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "axis" => (EuclideanSpace.basisFun (Fin n) ℝ)

theorem conformal_differentiated {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} {x : Eₙ} (hΩ : IsOpen Ω) (hx : x ∈ Ω)
    (hF : ContDiffAt ℝ ∞ F x) (hb : ContDiffAt ℝ ∞ b x)
    (hconf : EuclideanConformalOn Ω F b) (u v w : Eₙ) :
    inner ℝ (directional u (directional v F) x) (directional w F x) +
      inner ℝ (directional v F x) (directional u (directional w F) x) =
    (2 * directional u b x) * Real.exp (2 * b x) * inner ℝ v w := by
  have dj := (directional_contDiffAt (v := v) hF).differentiableAt (by simp)
  have dk := (directional_contDiffAt (v := w) hF).differentiableAt (by simp)
  have hleft := (dj.hasFDerivAt.inner (𝕜 := ℝ) dk.hasFDerivAt).fderiv
  have hright := (((hb.differentiableAt (by simp)).hasFDerivAt.const_mul 2).exp.mul_const
    (inner ℝ v w)).fderiv
  have heq : (fun y => inner ℝ (directional v F y) (directional w F y)) =ᶠ[𝓝 x]
      (fun y => Real.exp (2 * b y) * inner ℝ v w) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hconf y hy v w
  have h := congrArg (fun A : Eₙ →L[ℝ] ℝ => A u)
    (hleft.symm.trans (heq.fderiv_eq.trans hright))
  simpa [directional, mul_comm, mul_left_comm, add_comm] using h

private theorem conformal_frame_inner_ext {T : Eₙ →L[ℝ] Eₙ} {c : ℝ} (hc : 0 < c)
    (hT : ∀ v w, inner ℝ (T v) (T w) = c * inner ℝ v w) {a b : Eₙ}
    (h : ∀ k, inner ℝ a (T (axis k)) = inner ℝ b (T (axis k))) : a = b := by
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).mpr fun v hv => by
    have hnorm := hT v v
    rw [hv, inner_zero_left] at hnorm
    have hvzero : inner ℝ v v = 0 := (mul_eq_zero.mp hnorm.symm).resolve_left hc.ne'
    exact inner_self_eq_zero.mp hvzero
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp hinj
  obtain ⟨v, hv⟩ := hsurj (a - b)
  have hi : inner ℝ (a - b) (T v) = 0 := by
    rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v, map_sum, inner_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_smul, real_inner_smul_right, inner_sub_left, h, sub_self, mul_zero]
  rwa [hv, inner_self_eq_zero, sub_eq_zero] at hi

/-- The second derivatives of a conformal chart are its first derivative frame
contracted against the conformal Christoffel symbols. -/
theorem directional_directional_of_conformal {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} {x : Eₙ} (hΩ : IsOpen Ω) (hx : x ∈ Ω)
    (hF : ContDiffAt ℝ ∞ F x) (hb : ContDiffAt ℝ ∞ b x)
    (hconf : EuclideanConformalOn Ω F b) (i j : Fin n) :
    directional (axis i) (directional (axis j) F) x =
      ∑ l, conformalConnection (fun k => directional (axis k) b x) i j l •
        directional (axis l) F x := by
  let D (k : Fin n) := directional (axis k) F x
  let H (i j : Fin n) := directional (axis i) (directional (axis j) F) x
  let db (k : Fin n) := directional (axis k) b x
  let c := Real.exp (2 * b x)
  have hc : 0 < c := Real.exp_pos _
  have hsym (i j : Fin n) : H i j = H j i := directional_comm hF (axis i) (axis j)
  change H i j = ∑ l, conformalConnection db i j l • (fderiv ℝ F x) (axis l)
  apply conformal_frame_inner_ext hc (hconf x hx)
  intro k
  change inner ℝ (H i j) (D k) = inner ℝ (∑ l, conformalConnection db i j l • D l) (D k)
  have hd (a b d : Fin n) :
      inner ℝ (H a b) (D d) + inner ℝ (D b) (H a d) =
        (2 * db a) * c * inner ℝ (axis b) (axis d) :=
    conformal_differentiated hΩ hx hF hb hconf (axis a) (axis b) (axis d)
  have h₁ := hd i j k
  have h₂ := hd j i k
  have h₃ := hd k i j
  rw [real_inner_comm (H i k) (D j)] at h₁
  rw [hsym j i, real_inner_comm (H j k) (D i)] at h₂
  rw [hsym k i, hsym k j, real_inner_comm (H j k) (D i)] at h₃
  have hframe (l k : Fin n) : inner ℝ (D l) (D k) = c * (if l = k then 1 else 0) := by
    exact (hconf x hx (axis l) (axis k)).trans
      (congrArg (c * ·) ((EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite l k))
  simp only [sum_inner, real_inner_smul_left, hframe, mul_ite, mul_zero, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [OrthonormalBasis.inner_eq_ite] at h₁ h₂ h₃
  dsimp [conformalConnection]
  simp only [eq_comm (a := k)]
  split_ifs at h₁ h₂ h₃ ⊢ <;> first | contradiction | linarith

private theorem conformal_connection_differentiable {b : Eₙ → ℝ} {x : Eₙ}
    (hb : ContDiffAt ℝ ∞ b x) (j k a : Fin n) :
    DifferentiableAt ℝ (fun y => conformalConnection (fun l => directional (axis l) b y)
      j k a) x := by
  have hd (l : Fin n) : DifferentiableAt ℝ (directional (axis l) b) x :=
    (directional_contDiffAt hb).differentiableAt (by simp)
  unfold conformalConnection
  split_ifs <;> fun_prop

private theorem directional_conformal_connection {b : Eₙ → ℝ} {x : Eₙ}
    (hb : ContDiffAt ℝ ∞ b x) (i j k a : Fin n) :
    directional (axis i)
      (fun y => conformalConnection (fun l => directional (axis l) b y) j k a) x =
      conformalConnection (fun l => directional (axis i) (directional (axis l) b) x)
        j k a := by
  have hd (l : Fin n) : DifferentiableAt ℝ (directional (axis l) b) x :=
    (directional_contDiffAt hb).differentiableAt (by simp)
  unfold conformalConnection
  split_ifs <;>
    simp (disch := first | exact hd _ | exact (hd _).add (hd _) | fun_prop)
      only [directional_add, directional_sub, directional_neg, directional_const,
        zero_add, add_zero, sub_zero, zero_sub]

private theorem conformal_third_derivative {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} {x : Eₙ} (hΩ : IsOpen Ω) (hx : x ∈ Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hconf : EuclideanConformalOn Ω F b) (i j k : Fin n) :
    directional (axis i) (directional (axis j) (directional (axis k) F)) x =
      ∑ a, (conformalConnection
          (fun l => directional (axis i) (directional (axis l) b) x) j k a •
        directional (axis a) F x +
        conformalConnection (fun l => directional (axis l) b x) j k a •
          directional (axis i) (directional (axis a) F) x) := by
  have hFₓ := hF.contDiffAt (hΩ.mem_nhds hx)
  have hbₓ := hb.contDiffAt (hΩ.mem_nhds hx)
  let γ (a : Fin n) (y : Eₙ) :=
    conformalConnection (fun l => directional (axis l) b y) j k a
  have hEq : directional (axis j) (directional (axis k) F) =ᶠ[𝓝 x]
      (fun y => ∑ a, γ a y • directional (axis a) F y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact directional_directional_of_conformal hΩ hy (hF.contDiffAt (hΩ.mem_nhds hy))
      (hb.contDiffAt (hΩ.mem_nhds hy)) hconf j k
  have hγ (a : Fin n) : DifferentiableAt ℝ (γ a) x :=
    conformal_connection_differentiable hbₓ j k a
  have hD (a : Fin n) : DifferentiableAt ℝ (directional (axis a) F) x :=
    (directional_contDiffAt hFₓ).differentiableAt (by simp)
  change (fderiv ℝ (directional (axis j) (directional (axis k) F)) x) (axis i) = _
  rw [hEq.fderiv_eq, fderiv_fun_sum
    (A := fun (a : Fin n) (y : Eₙ) => γ a y • directional (axis a) F y)
    (u := Finset.univ) (fun a _ => (hγ a).smul (hD a))]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [fderiv_fun_smul (hγ a) (hD a)]
  have hγ' := directional_conformal_connection hbₓ i j k a
  change (fderiv ℝ (γ a) x) (axis i) = _ at hγ'
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, hγ']
  simp only [γ, directional, add_comm]

/-- Commutation in the differentiated frame forces the conformal connection
of the pullback metric to have vanishing coordinate curvature. -/
theorem conformal_curvature_zero {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} {x : Eₙ} (hΩ : IsOpen Ω) (hx : x ∈ Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hconf : EuclideanConformalOn Ω F b) (i j k a : Fin n) :
    conformalCurvature (fun l => directional (axis l) b x)
      (fun i j => directional (axis i) (directional (axis j) b) x) i j k a = 0 := by
  let D (a : Fin n) := directional (axis a) F x
  let H (i j : Fin n) := directional (axis i) (directional (axis j) F) x
  let b₁ (l : Fin n) := directional (axis l) b x
  let b₂ (i j : Fin n) := directional (axis i) (directional (axis j) b) x
  let c := Real.exp (2 * b x)
  have hc : 0 < c := Real.exp_pos _
  have hframe (l a : Fin n) : inner ℝ (D l) (D a) = c * (if l = a then 1 else 0) :=
    (hconf x hx (axis l) (axis a)).trans
      (congrArg (c * ·) ((EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite l a))
  have h₂ (i j a : Fin n) :
      inner ℝ (H i j) (D a) = conformalConnection b₁ i j a * c := by
    have hH : H i j = ∑ l, conformalConnection b₁ i j l • D l :=
      directional_directional_of_conformal hΩ hx (hF.contDiffAt (hΩ.mem_nhds hx))
        (hb.contDiffAt (hΩ.mem_nhds hx)) hconf i j
    simp only [hH, sum_inner, real_inner_smul_left, hframe, mul_ite, mul_zero, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h₃ (i j k a : Fin n) :
      inner ℝ (directional (axis i) (directional (axis j) (directional (axis k) F)) x)
        (D a) = (conformalConnection (b₂ i) j k a +
          ∑ l, conformalConnection b₁ j k l * conformalConnection b₁ i l a) * c := by
    have hstep : directional (axis i) (directional (axis j) (directional (axis k) F)) x =
        ∑ l, (conformalConnection (b₂ i) j k l • D l +
          conformalConnection b₁ j k l • H i l) :=
      conformal_third_derivative hΩ hx hF hb hconf i j k
    simp only [hstep, sum_inner, inner_add_left, real_inner_smul_left, hframe, h₂,
      mul_ite, mul_zero, mul_one, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, add_mul, Finset.sum_mul, mul_assoc]
  have hcomm := congrArg (fun v => inner ℝ v (D a))
    (directional_comm (directional_contDiffAt (v := axis k) (hF.contDiffAt (hΩ.mem_nhds hx)))
      (axis i) (axis j))
  simp only [h₃] at hcomm
  have hcancel := mul_right_cancel₀ hc.ne' hcomm
  change conformalCurvature b₁ b₂ i j k a = 0
  unfold conformalCurvature
  linarith only [hcancel]

omit [NormedSpace ℝ E] in
theorem euclidean_fderiv_eq_zero_of_directional {f : Eₙ → V} {x : Eₙ}
    (h : ∀ i, directional (axis i) f x = 0) : fderiv ℝ f x = 0 := by
  ext v
  rw [zero_apply, ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v,
    map_sum]
  exact Finset.sum_eq_zero fun i _ => by rw [map_smul]; exact smul_eq_zero_of_right _ (h i)

theorem exists_const_of_directional_eq_zero_on {f : Eₙ → V} {Ω : Set Eₙ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hf : DifferentiableOn ℝ f Ω)
    (h : ∀ x ∈ Ω, ∀ i, directional (axis i) f x = 0) :
    ∃ c, EqOn f (fun _ => c) Ω :=
  hΩ.exists_is_const_of_fderiv_eq_zero hconn hf
    fun x hx => euclidean_fderiv_eq_zero_of_directional (h x hx)

private theorem directional_exp_neg {b : Eₙ → ℝ} {x : Eₙ} (hb : DifferentiableAt ℝ b x)
    (i : Fin n) :
    directional (axis i) (fun y => Real.exp (-b y)) x =
      Real.exp (-b x) * (-directional (axis i) b x) := by
  have h := congrArg (fun L : Eₙ →L[ℝ] ℝ => L (axis i)) hb.hasFDerivAt.neg.exp.fderiv
  simpa only [directional, Pi.neg_apply, smul_apply, smul_eq_mul,
    neg_apply] using h

private theorem exp_neg_hessian_of_conformal {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} {x : Eₙ} (hn : 3 ≤ n) (hΩ : IsOpen Ω) (hx : x ∈ Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hb : ContDiffOn ℝ ∞ b Ω)
    (hconf : EuclideanConformalOn Ω F b) (i j : Fin n) :
    directional (axis i) (directional (axis j) (fun y => Real.exp (-b y))) x =
      if i = j then Real.exp (-b x) * (∑ k, directional (axis k) b x ^ 2) / 2 else 0 := by
  let q (x : Eₙ) := Real.exp (-b x)
  have hq : DifferentiableAt ℝ q x := (hb.contDiffAt (hΩ.mem_nhds hx)).neg.exp.differentiableAt (by simp)
  have hbₓ := hb.contDiffAt (hΩ.mem_nhds hx)
  have hdiff := (directional_contDiffAt (v := axis j) hbₓ).differentiableAt (by simp)
  have heq : directional (axis j) q =ᶠ[𝓝 x]
      (fun y => q y * (-directional (axis j) b y)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact directional_exp_neg ((hb.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)) j
  have hH := conformalHessian_eq_of_flat (by simpa using hn)
    (fun l => directional (axis l) b x)
    (fun l m => directional (axis l) (directional (axis m) b) x)
    (conformal_curvature_zero hΩ hx hF hb hconf) i j
  change (fderiv ℝ (directional (axis j) q) x) (axis i) = _
  rw [heq.fderiv_eq]
  have hd := (hq.hasFDerivAt.mul hdiff.hasFDerivAt.neg).fderiv
  have hq' : (fderiv ℝ q x) (axis i) = q x * (-directional (axis i) b x) :=
    directional_exp_neg (hbₓ.differentiableAt (by simp)) i
  change (fderiv ℝ (q * -directional (axis j) b) x) (axis i) = _
  rw [hd]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, hq']
  change q x * (-directional (axis i) (directional (axis j) b) x) +
    (-directional (axis j) b x) * (q x * (-directional (axis i) b x)) = _
  rw [hH]
  split_ifs <;> dsimp [q] <;> ring

theorem exists_const_exp_neg_hessian_of_conformal {F : Eₙ → Eₙ} {b : Eₙ → ℝ}
    {Ω : Set Eₙ} (hn : 3 ≤ n) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hb : ContDiffOn ℝ ∞ b Ω) (hconf : EuclideanConformalOn Ω F b) :
    ∃ c : ℝ, (∀ x ∈ Ω, Real.exp (-b x) * (∑ k, directional (axis k) b x ^ 2) / 2 = c) ∧
      ∀ x ∈ Ω, ∀ i j : Fin n,
        directional (axis i) (directional (axis j) (fun y => Real.exp (-b y))) x =
          if i = j then c else 0 := by
  let q (x : Eₙ) := Real.exp (-b x)
  let a (x : Eₙ) := q x * (∑ k, directional (axis k) b x ^ 2) / 2
  have hq₀ (x : Eₙ) (hx : x ∈ Ω) : ContDiffAt ℝ ∞ q x :=
    (hb.contDiffAt (hΩ.mem_nhds hx)).neg.exp
  have hd (x : Eₙ) (hx : x ∈ Ω) (i : Fin n) :
      ContDiffAt ℝ ∞ (directional (axis i) b) x :=
    directional_contDiffAt (hb.contDiffAt (hΩ.mem_nhds hx))
  have hda : DifferentiableOn ℝ a Ω := by
    intro x hx
    have hq := (hq₀ x hx).differentiableAt (by simp)
    have hs (i : Fin n) := (hd x hx i).differentiableAt (by simp)
    have hsum : DifferentiableAt ℝ (fun y : Eₙ => ∑ k, directional (axis k) b y ^ 2) x :=
      DifferentiableAt.fun_sum fun i _ => (hs i).pow 2
    change DifferentiableWithinAt ℝ (fun y : Eₙ => q y *
      (∑ k, directional (axis k) b y ^ 2) / 2) Ω x
    have hprod : DifferentiableAt ℝ (fun y : Eₙ => q y *
        (∑ k, directional (axis k) b y ^ 2)) x := hq.mul hsum
    simp_rw [div_eq_mul_inv]
    exact (hprod.mul_const ((2 : ℝ)⁻¹)).differentiableWithinAt
  have hh (x : Eₙ) (hx : x ∈ Ω) (i j : Fin n) :
      directional (axis i) (directional (axis j) q) x = if i = j then a x else 0 :=
    exp_neg_hessian_of_conformal hn hΩ hx hF hb hconf i j
  have hzero (x : Eₙ) (hx : x ∈ Ω) (i : Fin n) : directional (axis i) a x = 0 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨j, hj⟩ := exists_ne i
    have hae : directional (axis j) (directional (axis j) q) =ᶠ[𝓝 x] a := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using by simpa using hh y hy j j
    have hbe : directional (axis i) (directional (axis j) q) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy using by simpa [hj.symm] using hh y hy i j
    have hcomm := directional_comm (directional_contDiffAt (v := axis j) (hq₀ x hx))
      (axis i) (axis j)
    have ha := congrArg (fun L : Eₙ →L[ℝ] ℝ => L (axis i)) (hae.fderiv_eq (𝕜 := ℝ))
    have hb := congrArg (fun L : Eₙ →L[ℝ] ℝ => L (axis j)) (hbe.fderiv_eq (𝕜 := ℝ))
    have hb₀ : directional (axis j) (directional (axis i) (directional (axis j) q)) x = 0 := by
      change (fderiv ℝ (directional (axis i) (directional (axis j) q)) x) (axis j) = 0
      simpa only [fderiv_const_apply, zero_apply] using hb
    exact ha.symm.trans (hcomm.trans hb₀)
  obtain ⟨c, hc⟩ := exists_const_of_directional_eq_zero_on hΩ hconn hda hzero
  exact ⟨c, hc, fun x hx i j => by rw [hh x hx, hc hx]⟩

end CalderonPaper

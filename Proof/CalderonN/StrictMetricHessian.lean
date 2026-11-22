module

public import Proof.CalderonN.StrictCarlemanMargins
public import Proof.CalderonN.CarlemanWeight
import Mathlib.Tactic

/-! Adapted from `Calderon/MixedKernelConstruction/MixedKernelConstructionC3SupportV015.lean`
at d6704c49395a38eb07e0249afeb8ea83d67971cc. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ContDiff Topology

namespace CalderonN.Carleman.Strict

variable {dim : ℕ} [NeZero dim]

section MetricHessianCoordinates
variable {A G : Fin dim → Fin dim → (CalderonN.X dim) → ℝ} {ϑ : (CalderonN.X dim) → ℝ}

/-- J1: the coordinate metric Hessian `∂_i∂_jϑ − Σ_k Γ^k_ij ∂_kϑ`, with the Christoffel symbols
`Γ^k_ij = ½ Σ_l A_kl (∂_i G_jl + ∂_j G_il − ∂_l G_ij)` of `G` and its inverse `A`. -/
def christoffelHess (G A : Fin dim → Fin dim → (CalderonN.X dim) → ℝ) (ϑ : (CalderonN.X dim) → ℝ) (x : (CalderonN.X dim)) (i j : Fin dim) : ℝ :=
  pd i (pd j ϑ) x - ∑ k, (∑ l, (1 / 2) * A k l x *
    (pd i (G j l) x + pd j (G i l) x - pd l (G i j) x)) * pd k ϑ x

/-- J1.2: the same Hessian through the phase field `W = A∇ϑ` (`A` symmetric). -/
theorem christoffelHess_eq (hsymm : ∀ i k, A i k = A k i) (x : (CalderonN.X dim)) (i j : Fin dim) :
    christoffelHess G A ϑ x i j = pd i (pd j ϑ) x - (1 / 2) * ∑ l, phaseField A ϑ l x *
      (pd i (G j l) x + pd j (G i l) x - pd l (G i j) x) := by
  simp only [christoffelHess, phaseField, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [congrFun (hsymm k l) x]
  ring

theorem pd_phaseField (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ) (i j : Fin dim)
    (x : (CalderonN.X dim)) :
    pd i (phaseField A ϑ j) x =
      ∑ k, (pd i (A j k) x * pd k ϑ x + A j k x * pd i (pd k ϑ) x) := by
  show pd i (fun y => ∑ k, A j k y * pd k ϑ y) x = _
  rw [pd_sum (fun k => (hA j k).mul (contDiff_pd hϑ))]
  exact Finset.sum_congr rfl fun k _ => pd_mul (hA j k) (contDiff_pd hϑ) x

private theorem contract_inverseDerivative
    (a D : Fin dim → Fin dim → ℝ) (ha : ∀ i j, a i j = a j i) (u v : Fin dim → ℝ) :
    (∑ i, ∑ k, (∑ s, ∑ t, a i s * D s t * a t k) * u i * v k) =
      ∑ s, ∑ t, D s t * (∑ i, a s i * u i) * (∑ k, a t k * v k) := by
  classical
  calc
    _ = ∑ p : Fin dim × Fin dim, ∑ q : Fin dim × Fin dim,
        a p.1 q.1 * D q.1 q.2 * a q.2 p.2 * u p.1 * v p.2 := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul]
    _ = ∑ q : Fin dim × Fin dim, ∑ p : Fin dim × Fin dim,
        a p.1 q.1 * D q.1 q.2 * a q.2 p.2 * u p.1 * v p.2 := Finset.sum_comm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [ha i s]
      ring

/-- Contracting the Christoffel correction against a repeated vector. -/
private theorem christoffelHess_contraction (hsymm : ∀ i k, A i k = A k i)
    (x : CalderonN.X dim) (Y : Fin dim → ℝ) :
    (∑ i, ∑ j, christoffelHess G A ϑ x i j * Y i * Y j) =
      (∑ i, ∑ j, pd i (pd j ϑ) x * Y i * Y j) -
      (∑ i, ∑ j, ∑ l, Y i * Y j * phaseField A ϑ l x * pd i (G j l) x) +
      (1/2 : ℝ) * (∑ l, ∑ i, ∑ j, phaseField A ϑ l x * Y i * Y j * pd l (G i j) x) := by
  let S (i j l : Fin dim) := Y i * Y j * phaseField A ϑ l x * pd i (G j l) x
  let T (i j l : Fin dim) := phaseField A ϑ l x * Y i * Y j * pd l (G i j) x
  have hswap : (∑ i, ∑ j, ∑ l, S j i l) = ∑ i, ∑ j, ∑ l, S i j l := Finset.sum_comm
  have hswap' : (∑ i, ∑ j, ∑ l, T i j l) = ∑ l, ∑ i, ∑ j, T i j l := by
    calc
      _ = ∑ i, ∑ l, ∑ j, T i j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hpoint (i j : Fin dim) :
      christoffelHess G A ϑ x i j * Y i * Y j = pd i (pd j ϑ) x * Y i * Y j -
        (1/2 : ℝ) * (∑ l, S i j l) - (1/2 : ℝ) * (∑ l, S j i l) +
        (1/2 : ℝ) * ∑ l, T i j l := by
    rw [christoffelHess_eq hsymm]
    have he :
        (1/2 : ℝ) * (∑ l, phaseField A ϑ l x *
          (pd i (G j l) x + pd j (G i l) x - pd l (G i j) x)) * Y i * Y j =
        (1/2 : ℝ) * (∑ l, S i j l) + (1/2 : ℝ) * (∑ l, S j i l) -
        (1/2 : ℝ) * ∑ l, T i j l := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by
        simp only [S, T]
        ring
    simp only [sub_mul, he]
    ring
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hswap, hswap']
  change _ =
    (∑ i, ∑ j, pd i (pd j ϑ) x * Y i * Y j) -
      (∑ i, ∑ j, ∑ l, S i j l) + (1/2 : ℝ) * (∑ l, ∑ i, ∑ j, T i j l)
  ring

/-- J1.1: derivative of the phase field under the inverse differentiation rule at `x`. -/
theorem pd_phaseField_inverse (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (x : (CalderonN.X dim)) (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (i j : Fin dim) :
    pd i (phaseField A ϑ j) x = ∑ k, A j k x * pd i (pd k ϑ) x -
      ∑ s, A j s x * ∑ t, pd i (G s t) x * phaseField A ϑ t x := by
  rw [pd_phaseField hA hϑ]
  simp only [hinvd, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have he :
      (∑ k, (∑ s, ∑ t, A j s x * pd i (G s t) x * A t k x) * pd k ϑ x) =
        ∑ s, A j s x * ∑ t, pd i (G s t) x * phaseField A ϑ t x := by
    simp only [phaseField, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun k _ => by ring
  rw [he]
  ring

/-- J1.4a: derivative of the phase norm under the inverse differentiation rule at `x`. -/
theorem pd_phaseNorm_inverse (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : (CalderonN.X dim))
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (j : Fin dim) :
    pd j (phaseNorm A ϑ) x = 2 * ∑ i, phaseField A ϑ i x * pd j (pd i ϑ) x -
      ∑ s, ∑ t, phaseField A ϑ s x * phaseField A ϑ t x * pd j (G s t) x := by
  have hf : ∀ i k, ContDiff ℝ ∞ (fun y => A i k y * pd i ϑ y * pd k ϑ y) := fun i k =>
    ((hA i k).mul (contDiff_pd hϑ)).mul (contDiff_pd hϑ)
  have e1 : pd j (phaseNorm A ϑ) x = ∑ i, ∑ k, (pd j (A i k) x * pd i ϑ x * pd k ϑ x +
      A i k x * pd j (pd i ϑ) x * pd k ϑ x + A i k x * pd i ϑ x * pd j (pd k ϑ) x) := by
    show pd j (fun y => ∑ i, ∑ k, A i k y * pd i ϑ y * pd k ϑ y) x = _
    rw [pd_sum (fun i => ContDiff.sum fun k _ => hf i k)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pd_sum (fun k => hf i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pd_mul ((hA i k).mul (contDiff_pd hϑ)) (contDiff_pd hϑ), pd_mul (hA i k) (contDiff_pd hϑ)]
    ring
  rw [e1]
  simp only [hinvd, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  let w := fun i => phaseField A ϑ i x
  have hFirst :
      (∑ i, ∑ k, (∑ s, ∑ t, A i s x * pd j (G s t) x * A t k x) * pd i ϑ x * pd k ϑ x) =
        ∑ s, ∑ t, w s * w t * pd j (G s t) x := by
    rw [contract_inverseDerivative (fun i k => A i k x) _ (fun i k => congrFun (hsymm i k) x)]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by
      change pd j (G s t) x * w s * w t = _
      ring
  have hSecond :
      (∑ i, ∑ k, A i k x * pd j (pd i ϑ) x * pd k ϑ x) =
        ∑ i, w i * pd j (pd i ϑ) x := by
    simp only [w, phaseField, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hThird :
      (∑ i, ∑ k, A i k x * pd i ϑ x * pd j (pd k ϑ) x) =
        ∑ i, w i * pd j (pd i ϑ) x := by
    rw [Finset.sum_comm]
    simp only [w, phaseField, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [congrFun (hsymm k i) x]
  rw [hFirst,hSecond,hThird]
  ring

/-- J1.4: `W·∇N = 2 H(W,W)` for the actual coordinate metric Hessian. -/
theorem phaseField_dot_pd_phaseNorm (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : (CalderonN.X dim))
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x) :
    ∑ j, phaseField A ϑ j x * pd j (phaseNorm A ϑ) x =
      2 * ∑ i, ∑ j, christoffelHess G A ϑ x i j * phaseField A ϑ i x * phaseField A ϑ j x := by
  let w := fun i => phaseField A ϑ i x
  let D := ∑ i, ∑ j, pd i (pd j ϑ) x * w i * w j
  let E := ∑ i, ∑ j, ∑ l, w i * w j * w l * pd i (G j l) x
  have hD : (∑ i, w i * (2 * ∑ j, w j * pd i (pd j ϑ) x)) = 2 * D := by
    simp only [D, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hE : (∑ i, w i * ∑ j, ∑ l, w j * w l * pd i (G j l) x) = E := by
    simp only [E, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have hE' : (∑ l, ∑ i, ∑ j, w l * w i * w j * pd l (G i j) x) = E := rfl
  rw [christoffelHess_contraction hsymm]
  simp only [pd_phaseNorm_inverse hA hϑ hsymm x hinvd, mul_sub, Finset.sum_sub_distrib]
  change (∑ i, w i * (2 * ∑ j, w j * pd i (pd j ϑ) x)) -
    (∑ i, w i * ∑ j, ∑ l, w j * w l * pd i (G j l) x) = 2 * (D - E + (1/2 : ℝ) * _)
  rw [hD, hE, hE']
  ring

set_option maxHeartbeats 1600000 in
/-- J1.3: `Mgrad(A, A∇ϑ)(ξ) = 4 H(Y,Y)` with `Y = Aξ`, for the actual coordinate metric Hessian. -/
theorem Mgrad_inverse_eq_hess (hA : ∀ i k, ContDiff ℝ ∞ (A i k)) (hϑ : ContDiff ℝ ∞ ϑ)
    (hsymm : ∀ i k, A i k = A k i) (x : (CalderonN.X dim))
    (hinvd : ∀ r i j, pd r (A i j) x = -∑ s, ∑ t, A i s x * pd r (G s t) x * A t j x)
    (ξ Y : Fin dim → ℝ) (hY : ∀ i, Y i = ∑ l, A i l x * ξ l) :
    Mgrad A (phaseField A ϑ) x ξ = 4 * ∑ i, ∑ j, christoffelHess G A ϑ x i j * Y i * Y j := by
  let w := fun i => phaseField A ϑ i x
  let D := ∑ i, ∑ j, pd i (pd j ϑ) x * Y i * Y j
  let E := ∑ i, ∑ j, ∑ l, Y i * Y j * w l * pd i (G j l) x
  let F := ∑ l, ∑ i, ∑ j, w l * Y i * Y j * pd l (G i j) x
  have hX (i : Fin dim) : ∑ j, ξ j * pd i (phaseField A ϑ j) x =
      (∑ k, Y k * pd i (pd k ϑ) x) -
        ∑ s, Y s * ∑ t, pd i (G s t) x * w t := by
    simp_rw [pd_phaseField_inverse hA hϑ x hinvd, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · simp only [hY, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      rw [congrFun (hsymm j k) x]
      ring
    · simp only [hY, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
      rw [congrFun (hsymm j s) x]
      dsimp only [w]
      ring
  have hT (i : Fin dim) :
      (∑ j, ∑ l, A i l x * ξ l * pd i (phaseField A ϑ j) x * ξ j) =
        Y i * (∑ j, ξ j * pd i (phaseField A ϑ j) x) := by
    simp only [hY, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hPos :
      (∑ i, ∑ j, ∑ l, A i l x * ξ l * pd i (phaseField A ϑ j) x * ξ j) = D - E := by
    simp only [hT, hX, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · simp only [D, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    · simp only [E, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun l _ => by ring
  have hNeg (l : Fin dim) :
      (∑ i, ∑ k, pd l (A i k) x * ξ i * ξ k) =
      -(∑ i, ∑ j, pd l (G i j) x * Y i * Y j) := by
    simp only [hinvd, neg_mul, Finset.sum_neg_distrib]
    rw [contract_inverseDerivative (fun i k => A i k x) _ (fun i k => congrFun (hsymm i k) x)]
    simp only [hY]
  have hF : (∑ l, w l * (-(∑ i, ∑ j, pd l (G i j) x * Y i * Y j))) = -F := by
    simp only [F, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [christoffelHess_contraction hsymm]
  simp only [Mgrad, hPos, hNeg]
  change 4 * (D - E) - 2 * _ = 4 * (D - E + (1/2 : ℝ) * F)
  rw [hF]
  ring

theorem bil_div (M : Fin dim → Fin dim → ℝ) (u w : Fin dim → ℝ) (s : ℝ) :
    ∑ i, ∑ j, M i j * (u i / s) * (w j / s) = (∑ i, ∑ j, M i j * u i * w j) / s ^ 2 := by
  simp only [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem lin_div (M : Fin dim → Fin dim → ℝ) (u w : Fin dim → ℝ) (s : ℝ) :
    ∑ i, ∑ j, M i j * u i * (w j / s) = (∑ i, ∑ j, M i j * u i * w j) / s := by
  simp only [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- J2: source metric strictness at ONE point (unit form `H(e,e) + H(v,v) > 0` for every
`g`-unit `v ⊥_g W`, `H(e,e) = H(W,W)/N`), with `G(p)A(p) = I`, `G(p) > 0`, `∇ϑ(p) ≠ 0` and the
inverse differentiation rule at `p`, PROVES `N(p) > 0` and the T9 point criterion for `A`. -/
theorem point_criterion_of_metric_strictness (hA : ∀ i k, ContDiff ℝ ∞ (A i k))
    (hϑ : ContDiff ℝ ∞ ϑ) (hsymm : ∀ i k, A i k = A k i) (p : (CalderonN.X dim))
    (hinvd : ∀ r i j, pd r (A i j) p = -∑ s, ∑ t, A i s p * pd r (G s t) p * A t j p)
    (hGA : ∀ i k, ∑ j, G i j p * A j k p = if i = k then 1 else 0)
    (hGpos : ∀ v : Fin dim → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, G i j p * v i * v j)
    (hdϑ : (fun k => pd k ϑ p) ≠ 0)
    (hsrc : ∀ v : Fin dim → ℝ, ∑ i, ∑ j, G i j p * v i * v j = 1 →
      ∑ i, ∑ j, G i j p * phaseField A ϑ i p * v j = 0 →
      0 < (∑ i, ∑ j, christoffelHess G A ϑ p i j * phaseField A ϑ i p * phaseField A ϑ j p) /
          phaseNorm A ϑ p + ∑ i, ∑ j, christoffelHess G A ϑ p i j * v i * v j) :
    0 < phaseNorm A ϑ p ∧
    ∀ ξ : Fin dim → ℝ, ξ ≠ 0 → ∑ j, phaseField A ϑ j p * ξ j = 0 →
      0 < Mgrad A (phaseField A ϑ) p ξ +
        4 * ((∑ j, phaseField A ϑ j p * pd j (phaseNorm A ϑ) p) / (2 * phaseNorm A ϑ p)) *
          quad A p ξ := by
  -- `Y = Aξ` solves `GY = ξ`
  have hGY : ∀ ξ Y : Fin dim → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) →
      ∀ i, ∑ j, G i j p * Y j = ξ i := by
    intro ξ Y hY i
    simp only [hY]
    have e : ∑ j, G i j p * ∑ l, A j l p * ξ l = ∑ l, (∑ j, G i j p * A j l p) * ξ l := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp [hGA]
  have hgYY : ∀ ξ Y : Fin dim → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) →
      ∑ i, ∑ j, G i j p * Y i * Y j = quad A p ξ := by
    intro ξ Y hY
    have e : ∑ i, ∑ j, G i j p * Y i * Y j = ∑ i, Y i * ∑ j, G i j p * Y j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp only [hGY ξ Y hY]
    simp only [hY, quad, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hYne : ∀ ξ Y : Fin dim → ℝ, (∀ i, Y i = ∑ l, A i l p * ξ l) → ξ ≠ 0 → Y ≠ 0 := by
    intro ξ Y hY hξ h0
    apply hξ
    funext i
    rw [← hGY ξ Y hY i, h0]
    simp
  have hQpos : ∀ ξ : Fin dim → ℝ, ξ ≠ 0 → 0 < quad A p ξ := by
    intro ξ hξ
    have hY : ∀ i, (fun i => ∑ l, A i l p * ξ l) i = ∑ l, A i l p * ξ l := fun i => rfl
    rw [← hgYY ξ _ hY]
    exact hGpos _ (hYne ξ _ hY hξ)
  have hN : 0 < phaseNorm A ϑ p := hQpos _ hdϑ
  refine ⟨hN, fun ξ hξ hker => ?_⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin dim → ℝ, ∀ i, Y i = ∑ l, A i l p * ξ l := ⟨_, fun i => rfl⟩
  rw [Mgrad_inverse_eq_hess hA hϑ hsymm p hinvd ξ Y hY,
    phaseField_dot_pd_phaseNorm hA hϑ hsymm p hinvd]
  have hc : 0 < quad A p ξ := hQpos ξ hξ
  set c := quad A p ξ with hcdef
  set s := Real.sqrt c with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hc
  have hs2 : s ^ 2 = c := Real.sq_sqrt hc.le
  have hvv : ∑ i, ∑ j, G i j p * (Y i / s) * (Y j / s) = 1 := by
    rw [bil_div (fun i j => G i j p) Y Y s, hgYY ξ Y hY, hs2]
    exact div_self hc.ne'
  have hWv : ∑ i, ∑ j, G i j p * phaseField A ϑ i p * (Y j / s) = 0 := by
    rw [lin_div (fun i j => G i j p) (fun i => phaseField A ϑ i p) Y s]
    have e : ∑ i, ∑ j, G i j p * phaseField A ϑ i p * Y j =
        ∑ i, phaseField A ϑ i p * ∑ j, G i j p * Y j := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp only [hGY ξ Y hY]
    rw [hker, zero_div]
  have h := hsrc (fun i => Y i / s) hvv hWv
  rw [bil_div (fun i j => christoffelHess G A ϑ p i j) Y Y s, hs2] at h
  set HWW := ∑ i, ∑ j, christoffelHess G A ϑ p i j * phaseField A ϑ i p * phaseField A ϑ j p
  set HYY := ∑ i, ∑ j, christoffelHess G A ϑ p i j * Y i * Y j
  have e : 4 * HYY + 4 * (2 * HWW / (2 * phaseNorm A ϑ p)) * c =
      4 * c * (HWW / phaseNorm A ϑ p + HYY / c) := by
    field_simp <;> ring
  rw [e]
  exact mul_pos (mul_pos four_pos hc) h

end MetricHessianCoordinates

end CalderonN.Carleman.Strict

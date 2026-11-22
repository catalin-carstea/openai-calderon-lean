module

public import Proof.CalderonN.MetricPair
public import Mathlib.Analysis.Matrix.Normed

import Proof.CalderonN.ChartBilinear
import Mathlib.Tactic

public section

noncomputable section

open Set Matrix
open scoped ContDiff Matrix.Norms.Elementwise

namespace CalderonN

variable {n : ℕ} [NeZero n]

private abbrev pair (M : Mat n) (v w : X n) : ℝ :=
  metricPair (fun _ => M) 0 v w

private lemma pair_eq (M : Mat n) (v w : X n) : pair M v w = chartBilinear M v w :=
  (metricPair_eq_dotProduct (fun _ => M) (0 : X n) v w).trans (chartBilinear_apply M v w).symm

private theorem pair_smul_left (M : Mat n) (a : ℝ) (v w : X n) :
    pair M (a • v) w = a * pair M v w := by
  simp only [pair_eq, map_smul, _root_.smul_apply, smul_eq_mul]

private theorem pair_smul_right (M : Mat n) (a : ℝ) (v w : X n) :
    pair M v (a • w) = a * pair M v w := by
  simp only [pair_eq, map_smul, smul_eq_mul]

private theorem pair_sub_right (M : Mat n) (v w z : X n) :
    pair M v (w - z) = pair M v w - pair M v z := by
  simp only [pair_eq, map_sub]

private def metricOrthogonalize (M : Mat n) (u : I n → X n) (p i : I n) : X n :=
  if i = p then (Real.sqrt (pair M (u p) (u p)))⁻¹ • u p
  else if p < i then u i - (pair M (u p) (u i) / pair M (u p) (u p)) • u p
  else u i

private def gramSchmidtColumn (M : Mat n) : ℕ → I n → X n
  | 0 => axis
  | k+1 =>
    if hk : k < n then metricOrthogonalize M (gramSchmidtColumn M k) ⟨k,hk⟩
    else gramSchmidtColumn M k

/-- The coordinate Gram–Schmidt frame for an arbitrary positive definite
matrix, in the given order of its coordinate axes. -/
def smoothMetricFrame (M : Mat n) : I n → X n :=
  gramSchmidtColumn M n

private lemma gramSchmidtColumn_upper (M : Mat n) (k : ℕ) (i j : I n) (hij : i < j) :
    gramSchmidtColumn M k i j = 0 := by
  induction k generalizing i j with
  | zero => simp [gramSchmidtColumn, axis, ne_of_lt hij]
  | succ k ih =>
    by_cases hk : k < n
    · let p : I n := ⟨k,hk⟩
      rw [gramSchmidtColumn, dif_pos hk]
      change metricOrthogonalize M (gramSchmidtColumn M k) p i j = 0
      by_cases h : i = p
      · subst i
        simp [metricOrthogonalize, ih _ _ hij]
      · by_cases hpi : p < i
        · simp [metricOrthogonalize, h, hpi, ih _ _ hij, ih _ _ (hpi.trans hij)]
        · simp [metricOrthogonalize, h, hpi, ih _ _ hij]
    · rw [gramSchmidtColumn, dif_neg hk]
      exact ih i j hij

private lemma gramSchmidtColumn_diagonal (M : Mat n) (k : ℕ) (i : I n) (hi : k ≤ i.val) :
    gramSchmidtColumn M k i i = 1 := by
  induction k with
  | zero => simp [gramSchmidtColumn, axis]
  | succ k ih =>
    have hk : k < n := lt_of_lt_of_le (Nat.lt_of_succ_le hi) i.isLt.le
    let p : I n := ⟨k,hk⟩
    have hpi : p < i := Nat.lt_of_succ_le hi
    rw [gramSchmidtColumn, dif_pos hk]
    change metricOrthogonalize M (gramSchmidtColumn M k) p i i = 1
    simp [metricOrthogonalize, (ne_of_lt hpi).symm, hpi, ih (by omega),
      gramSchmidtColumn_upper M k p i hpi]

private lemma pair_pivot_pos {M : Mat n} (hM : M.PosDef) (k : ℕ) (hk : k < n) :
    0 < pair M (gramSchmidtColumn M k ⟨k,hk⟩) (gramSchmidtColumn M k ⟨k,hk⟩) := by
  apply metricPair_pos_of_posDef hM
  intro h
  have hp := gramSchmidtColumn_diagonal M k ⟨k,hk⟩ le_rfl
  simp [h] at hp

private lemma pair_normalize (M : Mat n) (u : X n) (h : 0 < pair M u u) :
    pair M ((Real.sqrt (pair M u u))⁻¹ • u) ((Real.sqrt (pair M u u))⁻¹ • u) = 1 := by
  let b := Real.sqrt (pair M u u)
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  have hc : pair M u u = b ^ 2 := (Real.sq_sqrt h.le).symm
  change pair M (b⁻¹ • u) (b⁻¹ • u) = 1
  rw [pair_smul_left, pair_smul_right, hc]
  field_simp

private lemma gramSchmidtColumn_orthonormal {M : Mat n} (hM : M.PosDef)
    (k : ℕ) (i j : I n) (hi : i.val < k) :
    pair M (gramSchmidtColumn M k i) (gramSchmidtColumn M k j) = if i = j then 1 else 0 := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
    by_cases hk : k < n
    · let p : I n := ⟨k,hk⟩
      let u := gramSchmidtColumn M k
      have hp : 0 < pair M (u p) (u p) := pair_pivot_pos hM k hk
      have hc (a b : I n) (ha : a < p) :
          pair M (u a) (u b) = if a = b then 1 else 0 := by
        exact ih a b ha
      rw [gramSchmidtColumn, dif_pos hk]
      change pair M (metricOrthogonalize M u p i) (metricOrthogonalize M u p j) = _
      have hip : i ≤ p := Nat.le_of_lt_succ hi
      rcases lt_or_eq_of_le hip with hip | rfl
      · rw [show metricOrthogonalize M u p i = u i by
          simp [metricOrthogonalize, ne_of_lt hip, not_lt_of_ge hip.le]]
        rcases lt_trichotomy j p with hjp | rfl | hpj
        · simpa [metricOrthogonalize, ne_of_lt hjp, not_lt_of_ge hjp.le] using hc i j hip
        · have hz : pair M (u i) (u p) = 0 := by simpa [ne_of_lt hip] using hc i p hip
          simp [metricOrthogonalize, pair_smul_left, pair_smul_right, hz, ne_of_lt hip]
        · have hz : pair M (u i) (u p) = 0 := by simpa [ne_of_lt hip] using hc i p hip
          rw [show metricOrthogonalize M u p j =
            u j - (pair M (u p) (u j) / pair M (u p) (u p)) • u p by
              simp [metricOrthogonalize, hpj, (ne_of_lt hpj).symm]]
          simp only [pair_sub_right, pair_smul_right, hz, mul_zero, sub_zero]
          exact hc i j hip
      · rcases lt_trichotomy j p with hjp | rfl | hpj
        · have hz : pair M (u p) (u j) = 0 := by
            rw [show pair M (u p) (u j) = pair M (u j) (u p) from
              metricPair_comm (g := fun _ => M) (x := 0) hM _ _]
            simpa [ne_of_lt hjp] using hc j p hjp
          simp [metricOrthogonalize, ne_of_lt hjp, not_lt_of_ge hjp.le,
            (ne_of_lt hjp).symm, pair_smul_left, pair_smul_right, hz]
        · simpa [metricOrthogonalize] using pair_normalize M (u p) hp
        · simp only [metricOrthogonalize, if_pos rfl, (ne_of_lt hpj).symm, if_false, hpj,
            if_true, ne_of_lt hpj, pair_sub_right, pair_smul_right, pair_smul_left]
          have hRoot := (Real.sqrt_pos.mpr hp).ne'
          field_simp [hp.ne', hRoot] <;> ring
    · rw [gramSchmidtColumn, dif_neg hk]
      exact ih i j (by omega)

theorem smoothMetricFrame_orthonormal {M : Mat n} (hM : M.PosDef) (i j : I n) :
    metricPair (fun _ => M) 0 (smoothMetricFrame M i) (smoothMetricFrame M j) =
      if i = j then 1 else 0 :=
  gramSchmidtColumn_orthonormal hM n i j i.isLt

private theorem contDiffOn_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {M : E → Mat n} (hM : ∀ i j, ContDiffOn ℝ ∞ (fun x => M x i j) U)
    {v w : E → X n} (hv : ContDiffOn ℝ ∞ v U) (hw : ContDiffOn ℝ ∞ w U) :
    ContDiffOn ℝ ∞ (fun x => pair (M x) (v x) (w x)) U := by
  have hproj (i : I n) : ContDiff ℝ ∞ (EuclideanSpace.proj i : X n →L[ℝ] ℝ) :=
    (EuclideanSpace.proj i : X n →L[ℝ] ℝ).contDiff
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ((hM i j).mul ((hproj i).comp_contDiffOn hv)).mul ((hproj j).comp_contDiffOn hw)

theorem contDiffOn_smoothMetricFrame {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {M : E → Mat n} (hM : ∀ i j, ContDiffOn ℝ ∞ (fun x => M x i j) U)
    (hPos : ∀ x ∈ U, (M x).PosDef) (i : I n) :
    ContDiffOn ℝ ∞ (fun x => smoothMetricFrame (M x) i) U := by
  have h (k : ℕ) (i : I n) : ContDiffOn ℝ ∞ (fun x => gramSchmidtColumn (M x) k i) U := by
    induction k generalizing i with
    | zero => exact contDiffOn_const
    | succ k ih =>
      by_cases hk : k < n
      · let p : I n := ⟨k,hk⟩
        let u (i : I n) (x : E) := gramSchmidtColumn (M x) k i
        have hp (x : E) (hx : x ∈ U) : 0 < pair (M x) (u p x) (u p x) :=
          pair_pivot_pos (hPos x hx) k hk
        have hPP := contDiffOn_pair hM (ih p) (ih p)
        simp only [gramSchmidtColumn, dif_pos hk]
        change ContDiffOn ℝ ∞ (fun x => metricOrthogonalize (M x) (fun j => u j x) p i) U
        rcases lt_trichotomy i p with hip | rfl | hpi
        · simpa [metricOrthogonalize, ne_of_lt hip, not_lt_of_ge hip.le] using ih i
        · have hs := hPP.sqrt (fun x hx => (hp x hx).ne')
          have hInv := hs.inv (fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne')
          apply (hInv.smul (ih p)).congr
          intro x hx
          simp [metricOrthogonalize, u, Pi.smul_apply, Pi.inv_apply]
        · have hPI := contDiffOn_pair hM (ih p) (ih i)
          have hRatio := hPI.div hPP (fun x hx => (hp x hx).ne')
          simpa [metricOrthogonalize, hpi, (ne_of_lt hpi).symm] using (ih i).sub (hRatio.smul (ih p))
      · simp only [gramSchmidtColumn, dif_neg hk]
        exact ih i
  exact h n i

/-- The Gram–Schmidt frame is smooth on a neighborhood of each positive
definite matrix, with the neighborhood taken in the full matrix space. -/
theorem contDiffAt_smoothMetricFrame {M : Mat n} (hM : M.PosDef) (i : I n) :
    ContDiffAt ℝ ∞ (fun A => smoothMetricFrame A i) M := by
  have hPair {v w : Mat n → X n} (hv : ContDiffAt ℝ ∞ v M) (hw : ContDiffAt ℝ ∞ w M) :
      ContDiffAt ℝ ∞ (fun A => pair A (v A) (w A)) M := by
    unfold pair metricPair
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.sum
    intro b _
    have hA : ContDiff ℝ ∞ (fun A : Mat n => A a b) :=
      contDiff_pi.mp (contDiff_pi.mp (contDiff_id : ContDiff ℝ ∞ (id : Mat n → Mat n)) a) b
    exact (hA.contDiffAt.mul ((EuclideanSpace.proj a).contDiff.contDiffAt.comp M hv)).mul
      ((EuclideanSpace.proj b).contDiff.contDiffAt.comp M hw)
  have h (k : ℕ) (i : I n) : ContDiffAt ℝ ∞ (fun A => gramSchmidtColumn A k i) M := by
    induction k generalizing i with
    | zero => exact contDiffAt_const
    | succ k ih =>
      by_cases hk : k < n
      · let p : I n := ⟨k,hk⟩
        let u (j : I n) (A : Mat n) := gramSchmidtColumn A k j
        have hp : 0 < pair M (u p M) (u p M) := pair_pivot_pos hM k hk
        have hPP := hPair (ih p) (ih p)
        simp only [gramSchmidtColumn,dif_pos hk]
        change ContDiffAt ℝ ∞ (fun A => metricOrthogonalize A (fun j => u j A) p i) M
        rcases lt_trichotomy i p with hip | rfl | hpi
        · simpa [metricOrthogonalize,ne_of_lt hip,not_lt_of_ge hip.le,u] using ih i
        · have hInv := (hPP.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne'
          simp only [metricOrthogonalize,ite_true]
          exact hInv.smul (ih p)
        · have hRatio := (hPair (ih p) (ih i)).div hPP hp.ne'
          simpa [metricOrthogonalize,u,hpi,(ne_of_lt hpi).symm] using (ih i).sub (hRatio.smul (ih p))
      · simpa only [gramSchmidtColumn,dif_neg hk] using ih i
  exact h n i

end CalderonN

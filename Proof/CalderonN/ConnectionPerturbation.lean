module

public import Proof.CalderonN.MetricVolumeDifferential

import Proof.CalderonN.FrameOperators
import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ParameterJets
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

public section

noncomputable section
open Set Matrix
open scoped ContDiff Matrix.Norms.Operator NNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

private theorem abs_matrix_entry_le_operatorNorm (M : (Mat dim)) (i j : (I dim)) : |M i j| ≤ ‖M‖ := by
  rw [← Real.norm_eq_abs,Matrix.linfty_opNorm_def]
  change (‖M i j‖₊ : ℝ) ≤ _
  apply NNReal.coe_le_coe.mpr
  exact (Finset.single_le_sum (f := fun j' => ‖M i j'‖₊) (fun j' _ => by positivity) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i' => ∑ j' : (I dim), ‖M i' j'‖₊) (Finset.mem_univ i))

private theorem operatorNorm_le_dim_of_entries (M : (Mat dim)) {a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ i j, |M i j| ≤ a) : ‖M‖ ≤ (dim : ℝ)*a := by
  rw [Matrix.linfty_opNorm_def]
  have h : (Finset.univ : Finset (I dim)).sup (fun i => ∑ j : (I dim), ‖M i j‖₊) ≤
      (⟨(dim : ℝ)*a,by positivity⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i _
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_sum]
    simp only [coe_nnnorm,Real.norm_eq_abs]
    calc
      _ ≤ ∑ _ : (I dim), a := Finset.sum_le_sum fun j _ => hM i j
      _ = (dim : ℝ)*a := by simp
  exact NNReal.coe_le_coe.mpr h

private theorem norm_mul3_le (A B C : (Mat dim)) : ‖A*B*C‖ ≤ ‖A‖*‖B‖*‖C‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

private theorem norm_metric_sub_le_inverse_sub {A B : (Mat dim)}
    (hA : A.PosDef) (hB : B.PosDef) {L : ℝ} (hL : 0 ≤ L)
    (hLA : ‖A‖ ≤ L) (hLB : ‖B‖ ≤ L) :
    ‖A-B‖ ≤ L^2 * ‖A⁻¹-B⁻¹‖ := by
  have h : A-B = A*(B⁻¹-A⁻¹)*B := by
    rw [Matrix.mul_sub,Matrix.sub_mul,mul_assoc A B⁻¹ B,
      Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB.det_pos.ne'),
      Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),mul_one,one_mul]
  calc
    ‖A-B‖ = ‖A*(B⁻¹-A⁻¹)*B‖ := congrArg norm h
    _ ≤ ‖A‖*‖B⁻¹-A⁻¹‖*‖B‖ := norm_mul3_le _ _ _
    _ ≤ L*‖B⁻¹-A⁻¹‖*L := by gcongr
    _ = L^2 * ‖A⁻¹-B⁻¹‖ := by rw [norm_sub_rev]; ring

private theorem inverse_derivative_recovers_metric
    {g : (MetricField dim)} (hg : SmoothMetric univ g) (x : (X dim)) (k : (I dim)) :
    matrixFieldDerivative g x (axis k) =
      -(g x * matrixFieldDerivative (fun y => (g y)⁻¹) x (axis k) * g x) := by
  have hInv (i j : (I dim)) : DifferentiableAt ℝ (fun y => (g y)⁻¹ i j) x :=
    (contDiffOn_univ.mp (contDiffOn_metric_inv_entry hg i j)).differentiable (by simp) x
  have hD := fderiv_inverseMetric_matrix_apply (fun y => (g y)⁻¹) x (axis k) hInv
    (hg.2 x (mem_univ _)).inv
  have he (y : (X dim)) : (g y)⁻¹⁻¹ = g y :=
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg.2 y (mem_univ _)).det_pos.ne')
  simp only [he] at hD
  rw [(hasFDerivAt_matrixField_of_entries g x (fun i j =>
    (contDiffOn_univ.mp (hg.1 i j)).differentiable (by simp) x)).fderiv] at hD
  exact hD

/-- Uniform first inverse-metric jet bounds control the difference of
the two literal Christoffel connections at a point. -/
theorem exists_connection_sub_bound_of_inverseJets {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {γ g : (MetricField dim)}, SmoothMetric univ γ → SmoothMetric univ g →
      ∀ (x : (X dim)) {η : ℝ}, 0 ≤ η →
      ‖γ x‖ ≤ L → ‖g x‖ ≤ L → ‖(γ x)⁻¹‖ ≤ L →
      (∀ k : (I dim), ‖matrixFieldDerivative (fun y => (γ y)⁻¹) x (axis k)‖ ≤ L ∧
        ‖matrixFieldDerivative (fun y => (g y)⁻¹) x (axis k)‖ ≤ L) →
      (∀ i j, |((g x)⁻¹ - (γ x)⁻¹) i j| ≤ η) →
      (∀ k i j, |coordDeriv k (fun y => ((g y)⁻¹ - (γ y)⁻¹) i j) x| ≤ η) →
      ∀ u v : (X dim), ‖connection g x u v - connection γ x u v‖ ≤ C * η * ‖u‖ * ‖v‖ := by
  let D := (dim : ℝ)*(2*L^4+L^2)
  let G := (dim : ℝ)*(3*L^3+3*L*D)/2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨(dim : ℝ)^3*G,by positivity,?_⟩
  intro γ g hγ hg x η hη hγN hgN hγInv hJets hVal hDiff u v
  let A := g x
  let B := γ x
  let U (k : (I dim)) := matrixFieldDerivative (fun y => (g y)⁻¹) x (axis k)
  let V (k : (I dim)) := matrixFieldDerivative (fun y => (γ y)⁻¹) x (axis k)
  have hdAB : ‖A-B‖ ≤ (dim : ℝ)*L^2*η := by
    have hh := norm_metric_sub_le_inverse_sub (hg.2 x (mem_univ _)) (hγ.2 x (mem_univ _)) hL hgN hγN
    exact hh.trans ((mul_le_mul_of_nonneg_left (operatorNorm_le_dim_of_entries _ hη hVal)
      (sq_nonneg L)).trans_eq (by ring))
  have hds (k : (I dim)) : ‖U k-V k‖ ≤ (dim : ℝ)*η := by
    refine operatorNorm_le_dim_of_entries _ hη fun i j => ?_
    change |matrixFieldDerivative (fun y => (g y)⁻¹) x (axis k) i j -
      matrixFieldDerivative (fun y => (γ y)⁻¹) x (axis k) i j| ≤ η
    rw [matrixFieldDerivative_apply_entry,matrixFieldDerivative_apply_entry]
    have h₁ := (contDiffOn_univ.mp (contDiffOn_metric_inv_entry hg i j)).differentiable (by simp) x
    have h₂ := (contDiffOn_univ.mp (contDiffOn_metric_inv_entry hγ i j)).differentiable (by simp) x
    simpa only [coordDeriv,Matrix.sub_apply,fderiv_fun_sub h₁ h₂,_root_.sub_apply] using hDiff k i j
  have hDerivDiff (k : (I dim)) : ‖matrixFieldDerivative g x (axis k) -
      matrixFieldDerivative γ x (axis k)‖ ≤ D*η := by
    rw [inverse_derivative_recovers_metric hg,inverse_derivative_recovers_metric hγ]
    change ‖-(A*U k*A) - -(B*V k*B)‖ ≤ D*η
    rw [neg_sub_neg,norm_sub_rev]
    have he : A*U k*A-B*V k*B =
        (A-B)*U k*A + B*(U k-V k)*A + B*V k*(A-B) := by noncomm_ring
    rw [he]
    have h1 : ‖(A-B)*U k*A‖ ≤ ((dim : ℝ)*L^2*η)*L*L :=
      (norm_mul3_le _ _ _).trans (by gcongr; exact (hJets k).2)
    have h2 : ‖B*(U k-V k)*A‖ ≤ L*((dim : ℝ)*η)*L :=
      (norm_mul3_le _ _ _).trans (by gcongr; exact hds k)
    have h3 : ‖B*V k*(A-B)‖ ≤ L*L*((dim : ℝ)*L^2*η) :=
      (norm_mul3_le _ _ _).trans (by gcongr; exact (hJets k).1)
    exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3).trans_eq
      (by dsimp [D]; ring))
  have hentry (k i j : (I dim)) : |coordDeriv k (fun y => g y i j) x -
      coordDeriv k (fun y => γ y i j) x| ≤ D*η := by
    simpa only [Matrix.sub_apply,matrixFieldDerivative_apply_entry,coordDeriv] using
      (abs_matrix_entry_le_operatorNorm (matrixFieldDerivative g x (axis k) -
        matrixFieldDerivative γ x (axis k)) i j).trans (hDerivDiff k)
  have hentryg (k i j : (I dim)) : |coordDeriv k (fun y => g y i j) x| ≤ L^3 := by
    rw [coordDeriv,← matrixFieldDerivative_apply_entry g x (axis k)]
    exact (abs_matrix_entry_le_operatorNorm _ _ _).trans (by
      rw [inverse_derivative_recovers_metric hg,norm_neg]
      exact (norm_mul3_le _ _ _).trans (show ‖A‖*‖U k‖*‖A‖ ≤ L^3 by
        rw [pow_succ,pow_two]; gcongr; exact (hJets k).2))
  have hGamma (k i j : (I dim)) : |christoffel g x k i j - christoffel γ x k i j| ≤ G*η := by
    let P (l : (I dim)) := coordDeriv i (fun y => g y l j) x +
      coordDeriv j (fun y => g y i l) x - coordDeriv l (fun y => g y i j) x
    let Q (l : (I dim)) := coordDeriv i (fun y => γ y l j) x +
      coordDeriv j (fun y => γ y i l) x - coordDeriv l (fun y => γ y i j) x
    have hP (l : (I dim)) : |P l| ≤ 3*L^3 := by
      refine (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add
        (hentryg i l j) (hentryg j i l))) (hentryg l i j)).trans_eq (by ring))
    have hPQ (l : (I dim)) : |P l-Q l| ≤ 3*D*η := by
      have he : P l-Q l =
          (coordDeriv i (fun y => g y l j) x - coordDeriv i (fun y => γ y l j) x) +
          (coordDeriv j (fun y => g y i l) x - coordDeriv j (fun y => γ y i l) x) -
          (coordDeriv l (fun y => g y i j) x - coordDeriv l (fun y => γ y i j) x) := by
        dsimp [P,Q]; ring
      rw [he]
      exact (abs_sub _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add
        (hentry i l j) (hentry j i l))) (hentry l i j)).trans_eq (by ring))
    have hprod (l : (I dim)) : |A⁻¹ k l * P l - B⁻¹ k l * Q l| ≤ (3*L^3+3*L*D)*η := by
      rw [show A⁻¹ k l * P l - B⁻¹ k l * Q l =
        (A⁻¹ k l-B⁻¹ k l)*P l + B⁻¹ k l*(P l-Q l) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul,abs_mul]
      have hh : |B⁻¹ k l| ≤ L := (abs_matrix_entry_le_operatorNorm _ _ _).trans hγInv
      exact (add_le_add (mul_le_mul (hVal k l) (hP l) (abs_nonneg _) hη)
        (mul_le_mul hh (hPQ l) (abs_nonneg _) hL)).trans_eq (by ring)
    change |(∑ l, A⁻¹ k l * P l)/2-(∑ l, B⁻¹ k l * Q l)/2| ≤ _
    rw [← sub_div,← Finset.sum_sub_distrib,abs_div,abs_of_pos (by norm_num : 0 < (2 : ℝ))]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
    calc
      _ ≤ ∑ l, |A⁻¹ k l * P l-B⁻¹ k l * Q l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : (I dim), (3*L^3+3*L*D)*η := Finset.sum_le_sum fun l _ => hprod l
      _ = (G*η)*2 := by simp [G]; ring
  have hcoord (k : (I dim)) :
      |(connection g x u v-connection γ x u v) k| ≤ (dim : ℝ)^2*(G*η)*‖u‖*‖v‖ := by
    have he : (connection g x u v-connection γ x u v) k =
        ∑ i, ∑ j, (christoffel g x k i j-christoffel γ x k i j)*u i*v j := by
      simp only [connection, PiLp.sub_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : (I dim), ∑ _j : (I dim), (G*η)*‖u‖*‖v‖ := by
        refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul,abs_mul]
        have hu : |u i| ≤ ‖u‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le u i
        have hv : |v j| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le v j
        exact mul_le_mul (mul_le_mul (hGamma k i j) hu (abs_nonneg _) (by positivity)) hv
          (by positivity) (by positivity)
      _ = _ := by simp; ring
  exact (norm_le_dim_mul_of_abs_coord_le (by positivity) hcoord).trans_eq (by ring)

private theorem exists_uniform_inverseJets_bound {g : ℝ → (MetricField dim)}
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j))
    (hpos : ∀ a y, (g a y).PosDef) {K : Set (ℝ × (X dim))} (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ K, ‖g q.1 q.2‖ ≤ L ∧ ‖(g q.1 q.2)⁻¹‖ ≤ L ∧
      ∀ k : (I dim), ‖matrixFieldDerivative (fun y => (g q.1 y)⁻¹) q.2 (axis k)‖ ≤ L := by
  let P (q : ℝ × (X dim)) := g q.1 q.2
  let D (q : ℝ × (X dim)) (k : (I dim)) := matrixFieldDerivative (fun y => (g q.1 y)⁻¹) q.2 (axis k)
  have hP (i j : (I dim)) : ContDiffOn ℝ ∞ (fun q => (P q)⁻¹ i j) univ :=
    contDiffOn_inv_entry_of_entries (fun i j => (hg i j).contDiffOn)
      (fun q _ => (hpos q.1 q.2).det_pos.ne') i j
  have hD (k : (I dim)) : Continuous (fun q : ℝ × (X dim) => D q k) := by
    apply continuous_matrix
    intro i j
    have he : (fun q : ℝ × (X dim) => D q k i j) = baseCoordDeriv k (fun q => (P q)⁻¹ i j) := by
      funext q
      rw [baseCoordDeriv_eq isOpen_univ (hP i j) (mem_univ (q.1,q.2)) k]
      exact matrixFieldDerivative_apply_entry _ _ _ _ _
    rw [he]
    exact (contDiffOn_univ.mp (contDiffOn_baseCoordDeriv isOpen_univ (hP i j) k)).continuous
  let F (q : ℝ × (X dim)) : (Mat dim) × (Mat dim) × ((I dim) → (Mat dim)) := (P q,(P q)⁻¹,D q)
  have hF : Continuous F :=
    (continuous_matrix fun i j => (hg i j).continuous).prodMk
      ((continuous_matrix fun i j => (contDiffOn_univ.mp (hP i j)).continuous).prodMk (continuous_pi hD))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max B 0,le_max_right _ _,fun q hq => ?_⟩
  have h := (hB q hq).trans (le_max_left B 0)
  change ‖(P q,(P q)⁻¹,D q)‖ ≤ max B 0 at h
  simp only [Prod.norm_def,max_le_iff] at h
  exact ⟨h.1,h.2.1,fun k => (norm_le_pi_norm _ k).trans h.2.2⟩

/-- Uniformly on a compact parameter and base room, entrywise bounds on
the inverse metric jets control the difference of the actual connections. -/
theorem exists_uniform_connection_sub_bound_of_inverseJets {γ g : ℝ → (MetricField dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => γ q.1 q.2 i j))
    (hg : ∀ i j, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => g q.1 q.2 i j))
    (hpγ : ∀ a y, (γ a y).PosDef) (hpg : ∀ a y, (g a y).PosDef)
    {K : Set (ℝ × (X dim))} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ η : ℝ, 0 ≤ η →
      (∀ i j, |((g q.1 q.2)⁻¹ - (γ q.1 q.2)⁻¹) i j| ≤ η) →
      (∀ k i j, |coordDeriv k (fun y => ((g q.1 y)⁻¹ - (γ q.1 y)⁻¹) i j) q.2| ≤ η) →
      ∀ u v : (X dim), ‖connection (g q.1) q.2 u v - connection (γ q.1) q.2 u v‖ ≤ C*η*‖u‖*‖v‖ := by
  obtain ⟨B,hB,hBnd⟩ := exists_uniform_inverseJets_bound hγ hpγ hK
  obtain ⟨D,_,hDnd⟩ := exists_uniform_inverseJets_bound hg hpg hK
  let L := max B D
  obtain ⟨C,hC,hEst⟩ := exists_connection_sub_bound_of_inverseJets (dim := dim) (hB.trans (le_max_left B D))
  refine ⟨C,hC,fun q hq η hη h0 h1 => ?_⟩
  have hγS : SmoothMetric univ (γ q.1) :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,
      fun y _ => hpγ q.1 y⟩
  have hgS : SmoothMetric univ (g q.1) :=
    ⟨fun i j => ((hg i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,
      fun y _ => hpg q.1 y⟩
  obtain ⟨b0,b1,b2⟩ := hBnd q hq
  obtain ⟨d0,_,d2⟩ := hDnd q hq
  exact hEst hγS hgS q.2 hη (b0.trans (le_max_left B D)) (d0.trans (le_max_right B D))
    (b1.trans (le_max_left B D))
    (fun k => ⟨(b2 k).trans (le_max_left B D),(d2 k).trans (le_max_right B D)⟩) h0 h1

end CalderonN

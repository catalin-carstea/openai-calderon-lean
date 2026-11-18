import Proof.DirectionalProductCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
namespace ShrinkingSpheres
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma second_fderiv_add_apply (f g : P → ℝ) (p a b : P)
    (hf : ContDiffAt ℝ ∞ f p) (hg : ContDiffAt ℝ ∞ g p) :
    fderiv ℝ (fderiv ℝ (fun q => f q+g q)) p b a =
      fderiv ℝ (fderiv ℝ f) p b a+fderiv ℝ (fderiv ℝ g) p b a := by
  have h := congrArg (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => P) ℝ => D ![b,a])
    (iteratedFDeriv_add_apply (i:=2) (hf.of_le (by simp)) (hg.of_le (by simp)))
  change fderiv ℝ (fderiv ℝ (f+g)) p b a = _
  simpa only [iteratedFDeriv_two_apply,ContinuousMultilinearMap.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one] using h

/-- Product assembly for a normalized scalar remainder and a reference
    coefficient perturbation, retaining both center and mixed quadratic gains. -/
theorem quadratic_product_remainder_directional_bound (N R H : P → ℝ) (p a b : P) (δ r A B : ℝ)
    (hN : ContDiffAt ℝ ∞ N p) (hR : ContDiffAt ℝ ∞ R p) (hH : ContDiffAt ℝ ∞ H p)
    (hδ : |δ| ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (N0 NC NZ NM RC RM H0 HC HZ HM : ℝ)
    (hN0 : 0 ≤ N0) (hNC : 0 ≤ NC) (hNZ : 0 ≤ NZ) (hNM : 0 ≤ NM)
    (hRC : 0 ≤ RC) (hRM : 0 ≤ RM) (hH0 : 0 ≤ H0) (hHC : 0 ≤ HC) (hHZ : 0 ≤ HZ) (hHM : 0 ≤ HM)
    (hNv : |N p| ≤ N0) (hNc : |fderiv ℝ N p a| ≤ NC*A) (hNz : |fderiv ℝ N p b| ≤ NZ*B)
    (hNm : |fderiv ℝ (fderiv ℝ N) p b a| ≤ NM*A*B)
    (hRc : |fderiv ℝ R p a| ≤ RC*r^2*A) (hRm : |fderiv ℝ (fderiv ℝ R) p b a| ≤ RM*r^2*A*B)
    (hHv : |H p-δ| ≤ H0*r^2) (hHc : |fderiv ℝ H p a| ≤ HC*r^2*A)
    (hHz : |fderiv ℝ H p b| ≤ HZ*r^2*B) (hHm : |fderiv ℝ (fderiv ℝ H) p b a| ≤ HM*r^2*A*B) :
    let J := fun q => δ*R q+N q*(H q-δ)
    |fderiv ℝ J p a| ≤ (RC+NC*H0+N0*HC)*r^2*A ∧
    |fderiv ℝ (fderiv ℝ J) p b a| ≤ (RM+NM*H0+NC*HZ+NZ*HC+N0*HM)*r^2*A*B := by
  dsimp only
  have hD := ((hR.differentiableAt (by simp)).hasFDerivAt.const_mul δ).add
    ((hN.differentiableAt (by simp)).hasFDerivAt.mul ((hH.differentiableAt (by simp)).hasFDerivAt.sub_const δ))
  have hFirst := congrArg (fun D : P →L[ℝ] ℝ => D a) hD.fderiv
  change fderiv ℝ (fun q => δ*R q+N q*(H q-δ)) p a = _ at hFirst
  simp only [_root_.add_apply,_root_.smul_apply,smul_eq_mul] at hFirst
  have hSecond := second_fderiv_add_apply (fun q => δ*R q) (fun q => N q*(H q-δ)) p a b
    (contDiffAt_const.mul hR) (hN.mul (hH.sub contDiffAt_const))
  rw [second_fderiv_mul_apply (fun _ => δ) R p a b contDiffAt_const hR,
    second_fderiv_mul_apply N (fun q => H q-δ) p a b hN (hH.sub contDiffAt_const)] at hSecond
  have hDConst : fderiv ℝ (fun _ : P => δ) = fun _ : P => (0 : P →L[ℝ] ℝ) := by funext q;exact (hasFDerivAt_const δ q).fderiv
  have hDShift : fderiv ℝ (fun q => H q-δ) = fderiv ℝ H := by funext q;exact fderiv_sub_const δ
  rw [hDConst,hDShift] at hSecond
  simp only [fderiv_const_apply,zero_apply,zero_mul,mul_zero,zero_add,add_zero] at hSecond
  constructor
  · rw [hFirst]
    have hb : |δ*fderiv ℝ R p a+(N p*fderiv ℝ H p a+(H p-δ)*fderiv ℝ N p a)| ≤
        |δ| * |fderiv ℝ R p a|+(|N p| * |fderiv ℝ H p a|+|H p-δ| * |fderiv ℝ N p a|) := by
      simpa only [abs_mul] using (abs_add_le (δ*fderiv ℝ R p a) (N p*fderiv ℝ H p a+(H p-δ)*fderiv ℝ N p a)).trans
        (add_le_add le_rfl (abs_add_le (N p*fderiv ℝ H p a) ((H p-δ)*fderiv ℝ N p a)))
    exact hb.trans ((show |δ| * |fderiv ℝ R p a|+(|N p| * |fderiv ℝ H p a|+
      |H p-δ| * |fderiv ℝ N p a|) ≤ 1*(RC*r^2*A)+(N0*(HC*r^2*A)+(H0*r^2)*(NC*A)) by gcongr).trans_eq (by ring))
  · rw [hSecond]
    have hb : |δ*fderiv ℝ (fderiv ℝ R) p b a+
        (fderiv ℝ (fderiv ℝ N) p b a*(H p-δ)+fderiv ℝ N p a*fderiv ℝ H p b+
        fderiv ℝ N p b*fderiv ℝ H p a+N p*fderiv ℝ (fderiv ℝ H) p b a)| ≤
        |δ*fderiv ℝ (fderiv ℝ R) p b a|+
        (|fderiv ℝ (fderiv ℝ N) p b a*(H p-δ)|+|fderiv ℝ N p a*fderiv ℝ H p b|+
        |fderiv ℝ N p b*fderiv ℝ H p a|+|N p*fderiv ℝ (fderiv ℝ H) p b a|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl
        ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)))
    simp only [abs_mul] at hb
    exact hb.trans ((show |δ| *|fderiv ℝ (fderiv ℝ R) p b a|+
      (|fderiv ℝ (fderiv ℝ N) p b a| *|H p-δ|+|fderiv ℝ N p a| *|fderiv ℝ H p b|+
      |fderiv ℝ N p b| *|fderiv ℝ H p a|+|N p| *|fderiv ℝ (fderiv ℝ H) p b a|) ≤
      1*(RM*r^2*A*B)+((NM*A*B)*(H0*r^2)+(NC*A)*(HZ*r^2*B)+
      (NZ*B)*(HC*r^2*A)+N0*(HM*r^2*A*B)) by gcongr).trans_eq (by ring))

end ShrinkingSpheres

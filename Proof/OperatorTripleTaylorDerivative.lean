import Proof.CompositionTaylorDerivative
import Proof.OperatorTripleTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ShrinkingSpheres

/-- The same three-factor affine remainder retains its quadratic scale
under differentiation, with explicit common first variations. -/
theorem norm_operator_triple_taylor_remainder_derivative_le
    {P H U V W : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A A1 : P → V →L[ℝ] W) (A0 : V →L[ℝ] W)
    (K K1 : P → U →L[ℝ] V) (K0 : U →L[ℝ] V)
    (B B1 : P → H →L[ℝ] U) (B0 : H →L[ℝ] U) (x : P)
    (r CA AA BA DA CK AK BK VK1 DK1 CKR DKR VB1 DB1 CBR DBR : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCA : 0 ≤ CA) (hAA : 0 ≤ AA) (hBA : 0 ≤ BA) (hDA : 0 ≤ DA)
    (hCK : 0 ≤ CK) (hAK : 0 ≤ AK) (hBK : 0 ≤ BK) (hVK1 : 0 ≤ VK1) (hDK1 : 0 ≤ DK1)
    (hCKR : 0 ≤ CKR) (hDKR : 0 ≤ DKR) (hVB1 : 0 ≤ VB1) (hDB1 : 0 ≤ DB1) (hCBR : 0 ≤ CBR) (hDBR : 0 ≤ DBR)
    (hA : DifferentiableAt ℝ A x) (hA1 : DifferentiableAt ℝ A1 x)
    (hK : DifferentiableAt ℝ K x) (hK1 : DifferentiableAt ℝ K1 x)
    (hB : DifferentiableAt ℝ B x) (hB1 : DifferentiableAt ℝ B1 x)
    (hNA : ‖A x‖ ≤ CA) (hDA' : ‖fderiv ℝ A x‖ ≤ AA*r) (hA0 : ‖A x-A0‖ ≤ BA*r)
    (hDAR : ‖fderiv ℝ (fun p => A p-A0-r • A1 p) x‖ ≤ DA*r^2)
    (hNK : ‖K x‖ ≤ CK) (hDK : ‖fderiv ℝ K x‖ ≤ AK*r) (hK0 : ‖K x-K0‖ ≤ BK*r)
    (hNK1 : ‖K1 x‖ ≤ VK1) (hDK1' : ‖fderiv ℝ K1 x‖ ≤ DK1)
    (hNKR : ‖K x-K0-r • K1 x‖ ≤ CKR*r^2)
    (hDKR' : ‖fderiv ℝ (fun p => K p-K0-r • K1 p) x‖ ≤ DKR*r^2)
    (hNB1 : ‖B1 x‖ ≤ VB1) (hDB1' : ‖fderiv ℝ B1 x‖ ≤ DB1)
    (hNBR : ‖B x-B0-r • B1 x‖ ≤ CBR*r^2)
    (hDBR' : ‖fderiv ℝ (fun p => B p-B0-r • B1 p) x‖ ≤ DBR*r^2) :
    ‖fderiv ℝ (fun p => (A p).comp ((K p).comp (B p))-A0.comp (K0.comp B0)-
      r • (A0.comp (K0.comp (B1 p)+(K1 p).comp B0)+(A1 p).comp (K0.comp B0))) x‖ ≤
    (AA*(CK*CBR+(BK+CKR)*VB1+CKR*‖B0‖)+
      CA*(AK*CBR+CK*DBR+AK*VB1+BK*DB1+DKR*‖B0‖)+
      AA*(‖K0‖*VB1+VK1*‖B0‖)+BA*(‖K0‖*DB1+DK1*‖B0‖)+DA*‖K0.comp B0‖)*r^2 := by
  let Z := fun p => (K p).comp (B p)
  let Z1 := fun p => K0.comp (B1 p)+(K1 p).comp B0
  have hZ : DifferentiableAt ℝ Z x := hK.clm_comp hB
  have hZ1a := (differentiableAt_const K0).clm_comp hB1
  have hZ1b := hK1.clm_comp (differentiableAt_const B0)
  have hZ1 : DifferentiableAt ℝ Z1 x := hZ1a.add hZ1b
  have hKDiff : ‖K x-K0‖ ≤ (BK+CKR)*r := hK0.trans (by gcongr;exact le_add_of_nonneg_right hCKR)
  have hZR := norm_operator_poisson_taylor_le (K x) K0 (K1 x) (B x) B0 (B1 x) r CK BK CKR VB1 CBR
    hr hCK hBK hCKR hVB1 hCBR hNK hKDiff hNKR hNBR hNB1
  have hDZR := norm_composition_taylor_remainder_derivative_le K K1 K0 B B1 B0 x r CK AK BK VB1 DB1 CBR DBR DKR
    hK hK1 hB hB1 hr hr1 hCK hAK hBK hVB1 hDB1 hCBR hDBR hDKR hNK hDK hK0 hNB1 hDB1' hNBR hDBR' hDKR'
  have hNZ1 : ‖Z1 x‖ ≤ ‖K0‖*VB1+VK1*‖B0‖ :=
    (norm_add_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hNB1 (norm_nonneg _)))
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hNK1 (norm_nonneg _))))
  have hLeft := norm_fderiv_clm_comp_le (fun _ : P => K0) B1 x (differentiableAt_const K0) hB1
  have hRight := norm_fderiv_clm_comp_le K1 (fun _ : P => B0) x hK1 (differentiableAt_const B0)
  simp only [fderiv_const_apply,norm_zero,zero_mul,mul_zero,zero_add,add_zero] at hLeft hRight
  have hDZ1 : ‖fderiv ℝ Z1 x‖ ≤ ‖K0‖*DB1+DK1*‖B0‖ := by
    have hDer := (hZ1a.hasFDerivAt.add hZ1b.hasFDerivAt).fderiv
    change fderiv ℝ Z1 x = _ at hDer
    rw [hDer]
    exact (norm_add_le _ _).trans (add_le_add
      (hLeft.trans (mul_le_mul_of_nonneg_left hDB1' (norm_nonneg _)))
      (hRight.trans (mul_le_mul_of_nonneg_right hDK1' (norm_nonneg _))))
  exact norm_composition_taylor_remainder_derivative_le A A1 A0 Z Z1 (K0.comp B0) x r
    CA AA BA (‖K0‖*VB1+VK1*‖B0‖) (‖K0‖*DB1+DK1*‖B0‖)
    (CK*CBR+(BK+CKR)*VB1+CKR*‖B0‖) (AK*CBR+CK*DBR+AK*VB1+BK*DB1+DKR*‖B0‖) DA
    hA hA1 hZ hZ1 hr hr1 hCA hAA hBA (by positivity) (by positivity) (by positivity) (by positivity) hDA
    hNA hDA' hA0 hNZ1 hDZ1 hZR hDZR hDAR

end ShrinkingSpheres

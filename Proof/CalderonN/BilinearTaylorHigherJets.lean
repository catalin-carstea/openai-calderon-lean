module

public import Proof.CalderonN.BilinearFamilyJetBounds
public import Proof.CalderonN.FiniteJetBudgetAlgebra
public import Proof.CalderonN.OperatorFamilyJetCalculus

/-! From BilinearTaylorHigherJets in Proposition 5.3 release f308cb9d. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinear_affine_taylor_remainder_identity
    (B : E →L[ℝ] F →L[ℝ] G) (f f0 f1 : E) (g g0 g1 : F) (r : ℝ) :
    B f g-B f0 g0-r • (B f0 g1+B f1 g0) =
      B f (g-g0-r • g1)+B (f-f0-r • f1) g0+r • B (f-f0) g1 := by
  simp only [map_sub,map_smul,_root_.sub_apply,_root_.smul_apply]
  module

@[expose] def bilinearTaylorJetBudget (N : ℕ) (B : E →L[ℝ] F →L[ℝ] G)
    (CF CD CQf CQg Cg1 : ℝ) (g0 : F) : ℝ :=
  ‖B‖*2^N*(CF*CQg+CQf*‖g0‖+CD*Cg1)

/-- A genuine affine Taylor product preserves the quadratic gain in all
    finite mixed parameter directions, with the same first variations. -/
theorem norm_iteratedFDeriv_bilinear_affine_remainder_le
    (B : E →L[ℝ] F →L[ℝ] G) (f f1 : P → E) (f0 : E) (g g1 : P → F) (g0 : F) (x : P)
    (hf : ContDiffAt ℝ ∞ f x) (hf1 : ContDiffAt ℝ ∞ f1 x)
    (hg : ContDiffAt ℝ ∞ g x) (hg1 : ContDiffAt ℝ ∞ g1 x)
    (N : ℕ) (r CF CD CQf CQg Cg1 : ℝ) (hr : 0 ≤ r)
    (hCF : 0 ≤ CF) (hCD : 0 ≤ CD) (hCQf : 0 ≤ CQf) (hCQg : 0 ≤ CQg) (hCg1 : 0 ≤ Cg1)
    (hfJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j f x‖ ≤ CF)
    (hdfJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => f p-f0) x‖ ≤ CD*r)
    (hfRemJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => f p-f0-r • f1 p) x‖ ≤ CQf*r^2)
    (hgRemJets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j (fun p => g p-g0-r • g1 p) x‖ ≤ CQg*r^2)
    (hg1Jets : ∀ j : ℕ,j ≤ N → ‖iteratedFDeriv ℝ j g1 x‖ ≤ Cg1)
    (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun p => B (f p) (g p)-B f0 g0-
      r • (B f0 (g1 p)+B (f1 p) g0)) x‖ ≤
      bilinearTaylorJetBudget N B CF CD CQf CQg Cg1 g0*r^2 := by
  let fR := fun p => f p-f0-r • f1 p
  let gR := fun p => g p-g0-r • g1 p
  let df := fun p => f p-f0
  let P1 := fun p => B (f p) (gR p)
  let P2 := fun p => B (fR p) g0
  let P3 := fun p => B (df p) (g1 p)
  have hfR : ContDiffAt ℝ ∞ fR x := (hf.sub contDiffAt_const).sub (hf1.const_smul r)
  have hgR : ContDiffAt ℝ ∞ gR x := (hg.sub contDiffAt_const).sub (hg1.const_smul r)
  have hdf : ContDiffAt ℝ ∞ df x := hf.sub contDiffAt_const
  have hP1 : ContDiffAt ℝ ∞ P1 x := (B.contDiff.contDiffAt.comp x hf).clm_apply hgR
  have hP2 : ContDiffAt ℝ ∞ P2 x := (B.contDiff.contDiffAt.comp x hfR).clm_apply contDiffAt_const
  have hP3 : ContDiffAt ℝ ∞ P3 x := (B.contDiff.contDiffAt.comp x hdf).clm_apply hg1
  have hN1 : ‖iteratedFDeriv ℝ n P1 x‖ ≤ (‖B‖*2^N*CF*CQg)*r^2 :=
    (norm_iteratedFDeriv_bilinear_common_bound B f gR x hf hgR N CF (CQg*r^2) hCF (by positivity)
      hfJets hgRemJets n hn).trans_eq (by ring)
  have hN2 : ‖iteratedFDeriv ℝ n P2 x‖ ≤ (‖B‖*2^N*CQf*‖g0‖)*r^2 :=
    (norm_iteratedFDeriv_bilinear_common_bound B fR (fun _ : P => g0) x hfR contDiffAt_const N
      (CQf*r^2) ‖g0‖ (by positivity) (norm_nonneg _) hfRemJets
      (fun j _ => norm_iteratedFDeriv_const_le g0 x j) n hn).trans_eq (by ring)
  have hN3 : ‖iteratedFDeriv ℝ n P3 x‖ ≤ (‖B‖*2^N*CD*Cg1)*r :=
    (norm_iteratedFDeriv_bilinear_common_bound B df g1 x hdf hg1 N (CD*r) Cg1 (mul_nonneg hCD hr) hCg1
      hdfJets hg1Jets n hn).trans_eq (by ring)
  have hEq : (fun p => B (f p) (g p)-B f0 g0-r • (B f0 (g1 p)+B (f1 p) g0)) =
      fun p => (P1 p+P2 p)+r • P3 p := by
    funext p
    exact bilinear_affine_taylor_remainder_identity B (f p) f0 (f1 p) (g p) g0 (g1 p) r
  rw [hEq]
  have hOuter := norm_iteratedFDeriv_add_at_le (fun p => P1 p+P2 p) (fun p => r • P3 p) x
    (hP1.add hP2) (hP3.const_smul r) n
  rw [norm_iteratedFDeriv_const_smul_at P3 x hP3 r n,abs_of_nonneg hr] at hOuter
  have hInner := norm_iteratedFDeriv_add_at_le P1 P2 x hP1 hP2 n
  exact hOuter.trans ((add_le_add (hInner.trans (add_le_add hN1 hN2))
    (mul_le_mul_of_nonneg_left hN3 hr)).trans_eq (by unfold bilinearTaylorJetBudget;ring))

end ShrinkingSpheres

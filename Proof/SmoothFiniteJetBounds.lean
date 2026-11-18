import Proof.RadialTaylorHigherJets
import Proof.OperatorFamilyJetCalculus
import Proof.BilinearFamilyJetBounds
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 30
open scoped ContDiff BigOperators
namespace ShrinkingSpheres
variable {P E F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A common bound for a finite list of ordinary mixed jets of one smooth
    family; the zeroth jet is included. -/
structure SmoothFiniteJetBound (f : P → E) (p : P) (N : ℕ) (B : ℝ) : Prop where
  nonneg : 0 ≤ B
  smooth : ContDiffAt ℝ ∞ f p
  bound : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n f p‖ ≤ B

namespace SmoothFiniteJetBound

lemma weaken {f : P → E} {p : P} {N : ℕ} {B C : ℝ}
    (h : SmoothFiniteJetBound f p N B) (hBC : B ≤ C) : SmoothFiniteJetBound f p N C :=
  ⟨h.nonneg.trans hBC,h.smooth,fun n hn => (h.bound n hn).trans hBC⟩

lemma constant (e : E) (p : P) (N : ℕ) : SmoothFiniteJetBound (fun _ : P => e) p N ‖e‖ := by
  refine ⟨norm_nonneg _,contDiffAt_const,?_⟩
  intro n hn
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero,le_refl]
  | succ n => simpa only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n),Pi.zero_apply,norm_zero] using norm_nonneg e

lemma add {f g : P → E} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : SmoothFiniteJetBound g p N C) :
    SmoothFiniteJetBound (fun x => f x+g x) p N (B+C) :=
  ⟨add_nonneg hf.nonneg hg.nonneg,hf.smooth.add hg.smooth,fun n hn =>
    (norm_iteratedFDeriv_add_at_le f g p hf.smooth hg.smooth n).trans (add_le_add (hf.bound n hn) (hg.bound n hn))⟩

lemma const_smul {f : P → E} {p : P} {N : ℕ} {B : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (c : ℝ) :
    SmoothFiniteJetBound (fun x => c • f x) p N (|c| * B) := by
  refine ⟨mul_nonneg (abs_nonneg _) hf.nonneg,hf.smooth.const_smul c,?_⟩
  intro n hn
  rw [norm_iteratedFDeriv_const_smul_at f p hf.smooth c n]
  exact mul_le_mul_of_nonneg_left (hf.bound n hn) (abs_nonneg _)

lemma clm {f : P → E} {p : P} {N : ℕ} {B : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (L : E →L[ℝ] F) :
    SmoothFiniteJetBound (fun x => L (f x)) p N (‖L‖*B) :=
  ⟨mul_nonneg (norm_nonneg _) hf.nonneg,L.contDiff.contDiffAt.comp p hf.smooth,fun n hn =>
    (norm_iteratedFDeriv_clm_comp_le L f p hf.smooth n).trans
      (mul_le_mul_of_nonneg_left (hf.bound n hn) (norm_nonneg _))⟩

lemma sum {κ : Type*} [Fintype κ] (f : κ → P → E) (p : P) (N : ℕ) (B : κ → ℝ)
    (hf : ∀ k,SmoothFiniteJetBound (f k) p N (B k)) :
    SmoothFiniteJetBound (fun x => ∑ k,f k x) p N (∑ k,B k) := by
  refine ⟨Finset.sum_nonneg (fun k _ => (hf k).nonneg),ContDiffAt.sum (fun k _ => (hf k).smooth),?_⟩
  intro n hn
  exact (norm_iteratedFDeriv_fintype_sum_at_le f p (fun k => (hf k).smooth) n).trans
    (Finset.sum_le_sum (fun k _ => (hf k).bound n hn))

lemma comp {f : P → F →L[ℝ] G} {g : P → E →L[ℝ] F} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : SmoothFiniteJetBound g p N C) :
    SmoothFiniteJetBound (fun x => (f x).comp (g x)) p N (2^N*B*C) :=
  ⟨mul_nonneg (mul_nonneg (by positivity) hf.nonneg) hg.nonneg,hf.smooth.clm_comp hg.smooth,fun n hn =>
    norm_iteratedFDeriv_operator_comp_common_bound f g p hf.smooth hg.smooth N B C
      hf.nonneg hg.nonneg hf.bound hg.bound n hn⟩

lemma scalar {f : P → ℝ} {g : P → E} {p : P} {N : ℕ} {B C : ℝ}
    (hf : SmoothFiniteJetBound f p N B) (hg : SmoothFiniteJetBound g p N C) :
    SmoothFiniteJetBound (fun x => f x • g x) p N (2^N*B*C) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  refine ⟨by positivity,hf.smooth.smul hg.smooth,?_⟩
  intro n hn
  have hh := norm_iteratedFDeriv_bilinear_common_bound (ContinuousLinearMap.lsmul ℝ ℝ (E:=E))
    f g p hf.smooth hg.smooth N B C hf.nonneg hg.nonneg hf.bound hg.bound n hn
  exact hh.trans (by
    calc
      _ = ‖(ContinuousLinearMap.lsmul ℝ ℝ (E:=E))‖*(2^N*B*C) := by ring
      _ ≤ 1*(2^N*B*C) := mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le (by positivity)
      _ = _ := one_mul _)

end SmoothFiniteJetBound
end ShrinkingSpheres

module

public import Proof.Manuscript.MovingTrace.ScaledNormalProfileJets
public import Proof.CalderonN.CompactLocalJetBounds
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section

open CalderonN CalderonPatch.BoundaryLayer Set Polynomial
open scoped ContDiff

namespace CalderonPaper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact smooth amplitude times any depth-rescaled transport polynomial
retains its prescribed scale power after differentiation, up to one inverse
scale per derivative. The estimate includes the strip of depth at least -h. -/
theorem exists_scaled_profile_amplitude_jet_bound
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {A : Set (E × ℝ)} (hA : IsOpen A) {J : Set (E × ℝ)} (hJ : IsCompact J) (hJA : J ⊆ A)
    (hJK : ∀ q ∈ J, q.1 ∈ K)
    {f : E × ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f A)
    {κ : E → ℝ} (hκ : ContDiffOn ℝ ∞ κ U) {c : ℝ} (hc : 0 < c) (hcκ : ∀ p ∈ K, c ≤ κ p)
    {P : E → ℂ[X]} (hP : CoeffContDiffOn P U) (D : ℕ) (hD : ∀ p ∈ U, (P p).natDegree < D)
    (M N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ J, ∀ (h : ℝ), 0 < h → h ≤ 1 → -1 ≤ q.2 / h →
      ∀ j ≤ N,
      ‖iteratedFDeriv ℝ j (fun p : E × ℝ =>
        (h : ℂ) ^ M * (f p * polynomialProfileFamily κ P (p.1,p.2/h))) q‖ ≤
      C * h ^ M * h⁻¹ ^ N * Real.exp (-(c/4) * (q.2/h)) := by
  obtain ⟨F,hF,hFJ⟩ := exists_uniform_local_finite_jet_bound hJ
    (fun q hq => hf.contDiffAt (hA.mem_nhds (hJA hq))) N
  obtain ⟨Q,hQ,hQJ⟩ := exists_uniform_polynomial_profile_joint_jet_bound hU hK hKU
    hκ hc hcκ hP D hD N
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hF₀ : 0 ≤ F := zero_le_one.trans hF
  refine ⟨‖L‖ * 2 ^ N * F * Q, by positivity, ?_⟩
  intro q hq h hh hh₁ ht j hj
  let V : Set (E × ℝ) := U ×ˢ univ
  have hV : IsOpen V := hU.prod isOpen_univ
  have hqV : q ∈ V := ⟨hKU (hJK q hq),mem_univ _⟩
  let g := polynomialProfileFamily κ P
  let S : E × ℝ →L[ℝ] E × ℝ := scaleNormal h
  have hS : MapsTo S V V := fun p hp => ⟨hp.1,mem_univ _⟩
  have hg : ContDiffOn ℝ ∞ g V := hP.profile hκ D hD
  have hgS : ContDiffAt ℝ ∞ (g ∘ S) q :=
    (hg.comp S.contDiff.contDiffOn hS).contDiffAt (hV.mem_nhds hqV)
  have hEq : g ∘ S = (fun p : E × ℝ => g (p.1,p.2/h)) := funext fun p =>
    congrArg g (scaleNormal_apply h p)
  let G := Q * Real.exp (-(c/4) * (q.2/h)) * h⁻¹ ^ N
  have hG₀ : 0 ≤ G := by dsimp [G]; positivity
  have hGJet (i : ℕ) (hi : i ≤ N) : ‖iteratedFDeriv ℝ i (g ∘ S) q‖ ≤ G := by
    rw [hEq]
    have hG' : ‖iteratedFDeriv ℝ i g (q.1,q.2/h)‖ ≤ Q * Real.exp (-(c/4) * (q.2/h)) :=
      hQJ (q.1,q.2/h) (hJK q hq) ht i hi
    exact (norm_iteratedFDeriv_scaleNormal_le hh hh₁ hU hg q hqV.1 i).trans
      (mul_le_mul hG' (pow_le_pow_right₀ ((one_le_inv₀ hh).mpr hh₁) hi)
        (pow_nonneg (inv_nonneg.mpr hh.le) _) (mul_nonneg hQ (Real.exp_nonneg _)))
  have hfAt := hf.contDiffAt (hA.mem_nhds (hJA hq))
  have hfg : ContDiffAt ℝ j (fun p : E × ℝ => f p * (g ∘ S) p) q :=
    (hfAt.mul hgS).of_le (by simp)
  have hprod : ‖iteratedFDeriv ℝ j (fun p : E × ℝ => f p * (g ∘ S) p) q‖ ≤
      ‖L‖ * 2 ^ N * F * G :=
    ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound L f (g ∘ S) q
      hfAt hgS N F G hF₀ hG₀ (hFJ q hq) hGJet j hj
  have hSM :
      (fun p : E × ℝ => (h : ℂ) ^ M * (f p * polynomialProfileFamily κ P (p.1,p.2/h))) =
      (h : ℂ) ^ M • (fun p : E × ℝ => f p * (g ∘ S) p) := by
    rw [hEq]
    rfl
  rw [hSM,iteratedFDeriv_const_smul_apply hfg,norm_smul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hh.le]
  calc
    _ ≤ h ^ M * (‖L‖ * 2 ^ N * F * G) := mul_le_mul_of_nonneg_left hprod (pow_nonneg hh.le _)
    _ = _ := by dsimp [G]; ring

/-- At a positive fixed depth the profile exponential absorbs any fixed
inverse power of the semiclassical scale. -/
theorem scaled_exp_tail {c d h t : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hh : 0 < h) (ht : d ≤ t) (M : ℕ) :
    Real.exp (-c * (t/h)) ≤ (M.factorial / (c*d)^M) * h^M := by
  have hcd : 0 < c*d := mul_pos hc hd
  have hMoment := pow_mul_exp_neg_mul_le hcd (by positivity : 0 ≤ h⁻¹) M
  have hE : Real.exp (-c * (t/h)) ≤ Real.exp (-(c*d) * h⁻¹) := by
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv,← mul_assoc,show -(c*d) = (-c)*d by ring]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr hc.le)
  have h' := mul_le_mul_of_nonneg_right hMoment (pow_nonneg hh.le M)
  rw [mul_comm ((h⁻¹)^M),mul_assoc,← mul_pow,inv_mul_cancel₀ hh.ne',one_pow,mul_one] at h'
  exact hE.trans h'

end CalderonPaper

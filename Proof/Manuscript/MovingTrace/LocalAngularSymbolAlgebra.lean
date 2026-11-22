module

public import Proof.Manuscript.MovingTrace.ClassicalAngularAnnulus
public import Proof.CalderonN.BilinearFamilyJetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Topology

namespace CalderonPaper

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem uniform_finite_jet_bound_on_compact {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U J : Set A} (hU : IsOpen U) (hJ : IsCompact J) (hJU : J ⊆ U)
    {f : A → F} (hf : ContDiffOn ℝ ∞ f U) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ J, ∀ j ≤ N, ‖iteratedFDeriv ℝ j f q‖ ≤ B := by
  have hB (j : Fin (N+1)) : ∃ B ≥ 0, ∀ p ∈ J, ‖iteratedFDeriv ℝ j.val f p‖ ≤ B := by
    have hC : ContinuousOn (fun q => ‖iteratedFDeriv ℝ j.val f q‖) J := by
      intro q hq
      exact ((hf.contDiffAt (hU.mem_nhds (hJU hq))).continuousAt_iteratedFDeriv
        (by simp : (j.val:ℕ∞ω) ≤ ∞)).norm.continuousWithinAt
    obtain ⟨B,hBd⟩ := hJ.bddAbove_image hC
    exact ⟨max 0 B,le_max_left _ _,fun q hq => (hBd ⟨q,hq,rfl⟩).trans (le_max_right _ _)⟩
  choose B hB hBd using hB
  refine ⟨∑ j : Fin (N+1), B j,Finset.sum_nonneg (fun j _ => hB j),?_⟩
  intro q hq j hj
  let k : Fin (N+1) := ⟨j,Nat.lt_succ_of_le hj⟩
  exact (hBd k q hq).trans (Finset.single_le_sum (fun l _ => hB l) (Finset.mem_univ k))

def baseMulAddAffineSymbol (s : P × E → E → ℂ) (c d : P × E → ℂ)
    (L : P × E → E → ℂ) (p : P × E) (ξ : E) : ℂ :=
  c p * s p ξ + L p ξ + d p

def baseMulAddAffineCoefficients (b : ℕ → P × E → E → ℂ) (c d : P × E → ℂ)
    (L : P × E → E → ℂ) (k : ℕ) (p : P × E) (ξ : E) : ℂ :=
  c p * b k p ξ + if k = 0 then L p ξ else if k = 1 then d p else 0

private theorem affineCoefficientSum (d L : ℂ) (h : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (h:ℂ)^k * (if k=0 then L else if k=1 then d else 0)) =
      if N=0 then 0 else if N=1 then L else L+(h:ℂ)*d := by
  cases N with
  | zero => simp
  | succ N =>
    cases N with
    | zero => simp [Finset.sum_range_succ]
    | succ N =>
      induction N with
      | zero => simp [Finset.sum_range_succ]
      | succ N ih =>
        rw [Finset.sum_range_succ,ih]
        simp

theorem normalizedAnnulusRemainder_baseMulAddAffine
    (s : P × E → E → ℂ) (b : ℕ → P × E → E → ℂ) (c d : P × E → ℂ)
    (L : P × E → E → ℂ) (hL : ∀ p ξ k, L p (k • ξ) = (k:ℝ) • L p ξ)
    (N : ℕ) {h : ℝ} (hh : h ≠ 0) (p : P × E) (ν : E) :
    normalizedAnnulusRemainder (baseMulAddAffineSymbol s c d L)
      (baseMulAddAffineCoefficients b c d L) N h p ν =
      c p * normalizedAnnulusRemainder s b N h p ν +
        (if N=0 then L p ν + h • d p else if N=1 then h • d p else 0) := by
  simp only [normalizedAnnulusRemainder,baseMulAddAffineSymbol,baseMulAddAffineCoefficients,
    hL,Complex.real_smul,Complex.ofReal_pow,mul_add,Finset.sum_add_distrib]
  have hMul : (∑ k ∈ Finset.range N, (h:ℂ)^k * (c p * b k p ν)) =
      c p * ∑ k ∈ Finset.range N, (h:ℂ)^k * b k p ν := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hMul,affineCoefficientSum]
  have hi : (h:ℂ) * ((h⁻¹:ℝ):ℂ) = 1 := by rw [Complex.ofReal_inv,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hh)]
  rw [← mul_assoc (h:ℂ) ((h⁻¹:ℝ):ℂ),hi,one_mul]
  by_cases hN : N = 0
  · simp only [hN,if_true]; ring
  · by_cases hN₁ : N = 1
    · simp [hN₁]; ring
    · simp only [hN,hN₁,if_false]; ring

/-- Multiplication by a smooth base-and-angle factor and addition of a
first-order differential symbol preserve the exact normalized estimates. -/
theorem localAnnulus_baseMulAddAffine [FiniteDimensional ℝ E]
    {U : Set P} {D : Set E} (hU : IsOpen U) (hD : IsOpen D) (hDD : unitAnnulus E ⊆ D)
    {s : P × E → E → ℂ} {b : ℕ → P × E → E → ℂ}
    (hs : ContDiffOn ℝ ∞ (Function.uncurry s) ((U ×ˢ (univ : Set E)) ×ˢ univ))
    (hb : ∀ k, ContDiffOn ℝ ∞ (Function.uncurry (b k)) ((U ×ˢ univ) ×ˢ D))
    (hNB : LocalNormalizedAnnulusJetBounds U s b)
    {c d : P × E → ℂ} (hc : ContDiffOn ℝ ∞ c (U ×ˢ univ))
    (hd : ContDiffOn ℝ ∞ d (U ×ˢ univ))
    {L : P × E → E → ℂ} (hL : ContDiffOn ℝ ∞ (Function.uncurry L) ((U ×ˢ univ) ×ˢ univ))
    (hLin : ∀ p ξ k, L p (k • ξ) = (k:ℝ) • L p ξ) :
    ContDiffOn ℝ ∞ (Function.uncurry (baseMulAddAffineSymbol s c d L)) ((U ×ˢ univ) ×ˢ univ) ∧
      (∀ k, ContDiffOn ℝ ∞ (Function.uncurry (baseMulAddAffineCoefficients b c d L k))
        ((U ×ˢ univ) ×ˢ D)) ∧
      LocalNormalizedAnnulusJetBounds U (baseMulAddAffineSymbol s c d L)
        (baseMulAddAffineCoefficients b c d L) := by
  constructor
  · exact (((hc.comp contDiffOn_fst (fun _ h => h.1)).mul hs).add hL).add
      (hd.comp contDiffOn_fst (fun _ h => h.1))
  constructor
  · intro k
    have hM := (hc.comp contDiffOn_fst (fun q (hq : q ∈ (U ×ˢ univ) ×ˢ D) => hq.1)).mul (hb k)
    by_cases h0 : k=0
    · refine (hM.add (hL.mono (Set.prod_mono Subset.rfl (subset_univ _)))).congr ?_
      intro q _
      simp [Function.uncurry,baseMulAddAffineCoefficients,h0]
    · by_cases h1 : k=1
      · refine (hM.add (hd.comp contDiffOn_fst (fun _ h => h.1))).congr ?_
        intro q _
        simp [Function.uncurry,baseMulAddAffineCoefficients,h0,h1]
      · refine hM.congr ?_
        intro q _
        simp [Function.uncurry,baseMulAddAffineCoefficients,h0,h1]
  intro J hJ hJU Kout hOut N k
  let O : Set ((P × E) × E) := (U ×ˢ D) ×ˢ univ
  let T := (J ×ˢ unitAnnulus E) ×ˢ Kout
  let c' (q : (P × E) × E) := c (q.1.1,q.2)
  let d' (q : (P × E) × E) := d (q.1.1,q.2)
  let L' (q : (P × E) × E) := L (q.1.1,q.2) q.1.2
  have hO : IsOpen O := (hU.prod hD).prod isOpen_univ
  have hT : IsCompact T := (hJ.prod unitAnnulus_isCompact).prod hOut
  have hTO : T ⊆ O := fun q hq => ⟨⟨hJU hq.1.1,hDD hq.1.2⟩,mem_univ _⟩
  have hd' : ContDiffOn ℝ ∞ d' O := hd.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (fun q hq => ⟨hq.1.1,mem_univ _⟩)
  have hc' : ContDiffOn ℝ ∞ c' O := hc.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
    (fun q hq => ⟨hq.1.1,mem_univ _⟩)
  have hL' : ContDiffOn ℝ ∞ L' O := hL.comp
    ((contDiffOn_fst.fst.prodMk contDiffOn_snd).prodMk contDiffOn_fst.snd)
    (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩)
  obtain ⟨B₁,hB₁,hC⟩ := uniform_finite_jet_bound_on_compact hO hT hTO hc' k
  obtain ⟨B₂,hB₂,hDbd⟩ := uniform_finite_jet_bound_on_compact hO hT hTO hd' k
  obtain ⟨B₃,hB₃,hLbd⟩ := uniform_finite_jet_bound_on_compact hO hT hTO hL' k
  obtain ⟨B₄,hB₄,hBase⟩ := hNB hJ hJU hOut N k
  let M := ContinuousLinearMap.mul ℝ ℂ
  refine ⟨1+‖M‖*2^k*B₁*B₄+B₂+B₃,by positivity,?_⟩
  intro h hh p hp x hx ν hν j hj
  let q : (P × E) × E := ((p,ν),x)
  have hq : q ∈ T := ⟨⟨hp,hν⟩,hx⟩
  let r (q : (P × E) × E) := normalizedAnnulusRemainder s b N h (q.1.1,q.2) q.1.2
  let i (q : (P × E) × E) := if N=0 then L' q + h • d' q else if N=1 then h • d' q else 0
  have hr : ContDiffOn ℝ ∞ r O :=
    ((hs.comp (((contDiffOn_fst.fst.prodMk contDiffOn_snd).prodMk
      (contDiffOn_fst.snd.const_smul h⁻¹))) (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,mem_univ _⟩)).const_smul h).sub
      (ContDiffOn.sum fun k _ => ((hb k).comp
        ((contDiffOn_fst.fst.prodMk contDiffOn_snd).prodMk contDiffOn_fst.snd)
        (fun q hq => ⟨⟨hq.1.1,mem_univ _⟩,hq.1.2⟩)).const_smul (h^k))
  have hAt := fun {F : (P × E) × E → ℂ} (hF : ContDiffOn ℝ ∞ F O) => hF.contDiffAt (hO.mem_nhds (hTO hq))
  have hI : ContDiffAt ℝ ∞ i q := by
    by_cases h0 : N=0
    · simpa only [i,h0,if_true] using (hAt hL').add ((hAt hd').const_smul h)
    · by_cases h1 : N=1
      · simpa [i,h0,h1] using (hAt hd').const_smul h
      · simpa only [i,h0,h1,if_false] using (contDiffAt_const (c := (0:ℂ)) (x := q) (n := ∞))
  have hIbd : ‖iteratedFDeriv ℝ j i q‖ ≤ (B₂+B₃)*h^N := by
    have hDjet : ‖iteratedFDeriv ℝ j (fun z => h • d' z) q‖ ≤ h*B₂ := by
      change ‖iteratedFDeriv ℝ j (h • d') q‖ ≤ h*B₂
      rw [iteratedFDeriv_const_smul_apply ((hAt hd').of_le (by simp)),norm_smul,Real.norm_of_nonneg hh.1.le]
      exact mul_le_mul_of_nonneg_left (hDbd q hq j hj) hh.1.le
    by_cases h0 : N=0
    · have hi : i = L' + (fun z => h • d' z) := by
        funext z
        simp [i,h0]
      rw [hi,h0,pow_zero,mul_one,iteratedFDeriv_add_apply ((hAt hL').of_le (by simp))
        (((hAt hd').const_smul h).of_le (by simp))]
      have hDle : h*B₂ ≤ B₂ := mul_le_of_le_one_left hB₂ hh.2
      exact (norm_add_le _ _).trans ((add_le_add (hLbd q hq j hj)
        (hDjet.trans hDle)).trans_eq (add_comm B₃ B₂))
    · by_cases h1 : N=1
      · have hi : i = fun z => h • d' z := by
          funext z
          simp [i,h0,h1]
        rw [hi,h1,pow_one]
        have hle : h*B₂ ≤ (B₂+B₃)*h := by
          rw [mul_comm h B₂]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB₃) hh.1.le
        exact hDjet.trans hle
      · have hZ : iteratedFDeriv ℝ j i q = 0 := by simp [i,h0,h1]
        rw [hZ,norm_zero]
        exact mul_nonneg (add_nonneg hB₂ hB₃) (pow_nonneg hh.1.le N)
  change ‖iteratedFDeriv ℝ j (fun q => normalizedAnnulusRemainder (baseMulAddAffineSymbol s c d L)
    (baseMulAddAffineCoefficients b c d L) N h (q.1.1,q.2) q.1.2) q‖ ≤ _
  simp only [normalizedAnnulusRemainder_baseMulAddAffine s b c d L hLin N hh.1.ne']
  change ‖iteratedFDeriv ℝ j ((fun q => c' q * r q) + i) q‖ ≤ _
  rw [iteratedFDeriv_add_apply (((hAt hc').mul (hAt hr)).of_le (by simp)) (hI.of_le (by simp))]
  have hProd : ‖iteratedFDeriv ℝ j (fun q => c' q * r q) q‖ ≤ ‖M‖ * 2^k * B₁ * (B₄*h^N) :=
    ShrinkingSpheres.norm_iteratedFDeriv_bilinear_common_bound M c' r q (hAt hc') (hAt hr)
      k B₁ (B₄*h^N) hB₁ (mul_nonneg hB₄.le (pow_nonneg hh.1.le N)) (hC q hq)
      (fun i hi => hBase h hh p hp x hx ν hν i hi) j hj
  refine (norm_add_le _ _).trans ((add_le_add hProd hIbd).trans ?_)
  calc
    _ = (‖M‖ * 2^k * B₁ * B₄ + B₂ + B₃) * h^N := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hh.1.le N)

end CalderonPaper

module

public import Proof.CalderonN.LocalJetIntegral
public import Proof.CalderonN.Coordinates

import Proof.CalderonN.CompactFiniteJets
import Mathlib.Tactic

/-! Uniform finite jets of an integral remainder along a signed normal ray. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ}

abbrev NormalCoefficientRadialParameter (dim : ℕ) := X dim × (ℝ × X dim)

@[expose] def normalCoefficientRadialInput (a : ℝ × NormalCoefficientRadialParameter dim) : X dim × X dim :=
  (a.2.1,(a.1*a.2.2.1) • a.2.2.2)

@[expose] def normalCoefficientRadialDirection (a : NormalCoefficientRadialParameter dim) : X dim × X dim :=
  (0,a.2.2)

@[expose] def normalRadialTaylorKernel {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : X dim × X dim → E)
    (a : ℝ × NormalCoefficientRadialParameter dim) : E :=
  (1-a.1) •
    fderiv ℝ (fderiv ℝ F) (normalCoefficientRadialInput a)
      (normalCoefficientRadialDirection a.2) (normalCoefficientRadialDirection a.2)

@[expose] def normalRadialTaylorRemainder {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : X dim × X dim → E) (a : NormalCoefficientRadialParameter dim) :
    E := ∫ t in (0:ℝ)..1, normalRadialTaylorKernel F (t,a)

theorem smoothNear_normalRadialTaylorRemainder
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set (X dim × X dim)} (hU : IsOpen U) {F : X dim × X dim → E}
    (hF : ContDiffOn ℝ ∞ F U) :
    ∃ V : Set (NormalCoefficientRadialParameter dim), IsOpen V ∧
      {q | ∀ t ∈ Icc (0:ℝ) 1, normalCoefficientRadialInput (t,q) ∈ U} ⊆ V ∧
      ContDiffOn ℝ ∞ (normalRadialTaylorRemainder F) V := by
  let S := normalCoefficientRadialInput (dim:=dim) ⁻¹' U
  have hInput : ContDiff ℝ ∞ (normalCoefficientRadialInput (dim:=dim)) :=
    contDiff_snd.fst.prodMk ((contDiff_fst.mul contDiff_snd.snd.fst).smul contDiff_snd.snd.snd)
  have hDir : ContDiff ℝ ∞ (fun a : ℝ × NormalCoefficientRadialParameter dim =>
      normalCoefficientRadialDirection a.2) := contDiff_const.prodMk contDiff_snd.snd.snd
  have hD := (hF.fderiv_of_isOpen (m:=∞) hU (by simp)).fderiv_of_isOpen (m:=∞) hU (by simp)
  have hD' := hD.comp hInput.contDiffOn (fun q hq => hq)
  have hK : ContDiffOn ℝ ∞ (normalRadialTaylorKernel F) S :=
    ((contDiff_const.sub contDiff_fst).contDiffOn).smul
      ((hD'.clm_apply hDir.contDiffOn).clm_apply hDir.contDiffOn)
  obtain ⟨hV,hKV⟩ := contDiffOn_intervalIntegral_unit_of_tube (hU.preimage hInput.continuous) hK
  refine ⟨_,hV,?_,hKV⟩
  rintro q hq ⟨t,p⟩ ⟨ht,hp⟩
  have hpq : p = q := hp
  subst p
  exact hq t ht

theorem exists_uniform_normalRadialTaylorRemainder_jets
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Set (X dim)} (hBase : IsCompact S) (W : ℝ) (N : ℕ) (CA : ℝ) (hCA : 0 ≤ CA) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : X dim × X dim → E) (U : Set (X dim × X dim)), IsOpen U →
      ContDiffOn ℝ ∞ F U → ∀ y ∈ S, ∀ s ∈ Icc (-1:ℝ) 1, ∀ w ∈ closedBall (0:X dim) W,
      (∀ t ∈ Icc (0:ℝ) 1, (y,(t*s) • w) ∈ U) →
      (∀ t ∈ Icc (0:ℝ) 1, LocalSmoothJetBudget F (y,(t*s) • w) (N+2) CA) →
      LocalSmoothJetBudget (normalRadialTaylorRemainder F) (y,(s,w)) N C ∧
        F (y,s • w) = F (y,0)+s • fderiv ℝ F (y,0) (0,w)+
          s^2 • normalRadialTaylorRemainder F (y,(s,w)) := by
  let P := X dim × X dim
  let Q := NormalCoefficientRadialParameter dim
  let J : Set (ℝ × Q) := Icc 0 1 ×ˢ (S ×ˢ (Icc (-1) 1 ×ˢ closedBall (0:X dim) W))
  have hJ : IsCompact J := isCompact_Icc.prod (hBase.prod (isCompact_Icc.prod (isCompact_closedBall _ _)))
  have hInputSmooth : ContDiff ℝ ∞ (normalCoefficientRadialInput (dim:=dim)) :=
    contDiff_snd.fst.prodMk ((contDiff_fst.mul contDiff_snd.snd.fst).smul contDiff_snd.snd.snd)
  have hDirSmooth : ContDiff ℝ ∞ (normalCoefficientRadialDirection (dim:=dim)) :=
    contDiff_const.prodMk contDiff_snd.snd
  obtain ⟨C_I,hC_I,hI⟩ := exists_uniform_finite_jet_bound hJ hInputSmooth N
  obtain ⟨C_W,hC_W,hW⟩ := exists_uniform_finite_jet_bound
    (hBase.prod ((isCompact_Icc (a:=(-1:ℝ)) (b:=1)).prod (isCompact_closedBall (0:X dim) W))) hDirSmooth N
  let B₁ : (P →L[ℝ] P →L[ℝ] E) →L[ℝ] P →L[ℝ] P →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ (P →L[ℝ] E)).flip
  let B₂ : (P →L[ℝ] E) →L[ℝ] P →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ (E)).flip
  let C₀ := N.factorial*CA*C_I^N
  let C₁ := (2:ℝ)^N*‖B₁‖*C₀*C_W
  let C₂ := (2:ℝ)^N*‖B₂‖*C₁*C_W
  have hCW₀ : 0 ≤ C_W := zero_le_one.trans hC_W
  have hC₀ : 0 ≤ C₀ := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCA)
    (pow_nonneg (zero_le_one.trans hC_I) _)
  have hPow : 0 ≤ (2:ℝ)^N := pow_nonneg (by norm_num) _
  have hC₁ : 0 ≤ C₁ := mul_nonneg (mul_nonneg (mul_nonneg hPow (norm_nonneg _)) hC₀) hCW₀
  have hC₂ : 0 ≤ C₂ := mul_nonneg (mul_nonneg (mul_nonneg hPow (norm_nonneg _)) hC₁) hCW₀
  refine ⟨C₂,hC₂,?_⟩
  intro F U hU hFSmooth y hy s hs w hw hContains hJets
  let p : Q := (y,(s,w))
  let A := normalRadialTaylorKernel F
  have hpBase : p ∈ S ×ˢ (Icc (-1:ℝ) 1 ×ˢ closedBall (0:X dim) W) := ⟨hy,hs,hw⟩
  let V := normalCoefficientRadialInput (dim:=dim) ⁻¹' U
  have hVS : IsOpen V := hU.preimage hInputSmooth.continuous
  have hKernel : ContDiffOn ℝ ∞ A V := by
    have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ F)) U :=
      ((hFSmooth.fderiv_of_isOpen (m:=∞) hU (by simp)).fderiv_of_isOpen (m:=∞) hU (by simp))
    have hD' := hD.comp hInputSmooth.contDiffOn (fun _ h => h)
    have hW' : ContDiffOn ℝ ∞ (fun a : ℝ × Q => normalCoefficientRadialDirection a.2) V :=
      (hDirSmooth.comp contDiff_snd).contDiffOn
    exact ((contDiff_const.sub contDiff_fst).contDiffOn).smul ((hD'.clm_apply hW').clm_apply hW')
  have hpV : Icc (0:ℝ) 1 ×ˢ {p} ⊆ V := by
    rintro ⟨t,q⟩ ⟨ht,hq⟩
    have hq' : q = p := mem_singleton_iff.mp hq
    subst q
    exact hContains t ht
  have hBound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (j : ℕ) (hj : j ≤ N) :
      ‖iteratedFDeriv ℝ j (fun q => A (t,q)) p‖ ≤ C₂ := by
    let Input (q : Q) := normalCoefficientRadialInput (t,q)
    have hJp : (t,p) ∈ J := ⟨ht,hpBase⟩
    have hI' : LocalSmoothJetBudget Input p N C_I :=
      ⟨(hInputSmooth.comp (contDiff_const.prodMk contDiff_id)).contDiffAt,
        fun k hk => (norm_iteratedFDeriv_slice_right_le hInputSmooth t p k).trans (hI (t,p) hJp k hk)⟩
    have hWD : LocalSmoothJetBudget (normalCoefficientRadialDirection (dim:=dim)) p N C_W :=
      ⟨hDirSmooth.contDiffAt,hW p hpBase⟩
    have hF : LocalSmoothJetBudget F (Input p) (N+2) CA :=
      hJets t ht
    have hD : LocalSmoothJetBudget (fderiv ℝ (fderiv ℝ F) ∘ Input) p N C₀ :=
      hI'.comp (hF.fderiv.fderiv) hC_I
    have hB : LocalSmoothJetBudget (fun q => fderiv ℝ (fderiv ℝ F) (Input q)
        (normalCoefficientRadialDirection q) (normalCoefficientRadialDirection q)) p N C₂ := by
      have h := (hD.bilinear hWD B₁).bilinear hWD B₂
      have hFun : (fun q : Q => B₂ (B₁ ((fderiv ℝ (fderiv ℝ F) ∘ Input) q)
          (normalCoefficientRadialDirection q)) (normalCoefficientRadialDirection q)) =
          fun q => fderiv ℝ (fderiv ℝ F) (Input q)
            (normalCoefficientRadialDirection q) (normalCoefficientRadialDirection q) := by
        funext q
        rfl
      rw [hFun] at h
      exact h
    let D : E →L[ℝ] E := (1-t) • ContinuousLinearMap.id ℝ (E)
    have hDnorm : ‖D‖ ≤ 1 := by
      dsimp only [D]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2)]
      exact (mul_le_of_le_one_right (sub_nonneg.mpr ht.2) ContinuousLinearMap.norm_id_le).trans
        (sub_le_self 1 ht.1)
    have hFinal := (hB.linear_postcomp D).enlarge (mul_le_of_le_one_left hC₂ hDnorm)
    exact hFinal.bound j hj
  refine ⟨localSmoothJetBudget_intervalIntegral_unit hVS hKernel hpV N C₂ hBound,?_⟩
  have hLine (t : ℝ) : (y,0) + (t*s) • (0,w) = (y,(t*s) • w) := by
    apply Prod.ext <;> change _ = _ <;> simp
  have hStep : (y,0) + s • (0,w) = (y,s • w) := by
    simpa only [one_mul] using hLine 1
  have hTaylor := affineLine_second_taylor_integral_unit hU
    hFSmooth (p:=(y,0)) (w:=(0,w)) s
    (fun t ht => (hLine t).symm ▸ hContains t ht)
  simpa only [hStep,hLine,normalRadialTaylorRemainder,normalRadialTaylorKernel,
    normalCoefficientRadialInput,normalCoefficientRadialDirection] using hTaylor

end CalderonN

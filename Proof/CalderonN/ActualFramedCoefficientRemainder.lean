module

public import Proof.CalderonN.ActualNormalCoefficientRemainder
public import Proof.CalderonN.FirstMetricNormalJets

import Proof.CalderonN.FirstDensityJetBounds
import Proof.CalderonN.MatrixFieldJetNorms
import Proof.CalderonN.CompactFiniteJets
import Mathlib.Tactic

/-! The actual fixed-ball coefficient has a quadratic remainder which
is smooth jointly in the center, signed radius and ball coordinates. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

abbrev FramedRadialParameter (dim : ℕ) := (X dim × ℝ) × X dim

@[expose] def actualFramedCoefficientField (d : Data dim) (p : FramedRadialParameter dim) : Mat dim :=
  firstNormalVelocityCoefficient d p.1.1 (p.1.2 • frameVector d.frame p.1.1 p.2)

@[expose] def actualFramedCoefficientRadialRemainder (d : Data dim) (p : FramedRadialParameter dim) : Mat dim :=
  actualNormalCoefficientRadialRemainder d (p.1.1,(p.1.2,frameVector d.frame p.1.1 p.2))

theorem actualFirstNormalCoefficient_at_zero (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X dim} (hy : y ∈ Y) :
    actualNormalVelocityField d (y,0) = 1 := by
  ext i j
  have h := firstNormalVelocityCoefficient_rescaled d y 0 0 i j
  rw [zero_smul] at h
  exact h.trans (hd.normalizedFirstNormalCoeff_center hn hK hy 0 i j)

theorem actualFirstNormalCoefficient_verticalDerivative (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) {y : X dim} (hy : y ∈ Y)
    (z : X dim) (hF : DifferentiableAt ℝ (actualNormalVelocityField d) (y,0)) :
    fderiv ℝ (actualNormalVelocityField d) (y,0) (0,frameVector d.frame y z) =
      (firstDensityCenterLinear d y z) • (1 : Mat dim) := by
  let w := frameVector d.frame y z
  let α (s : ℝ) := (y,s • w)
  have hα : HasDerivAt α (0,w) 0 := by
    have h := (hasDerivAt_const (0:ℝ) y).prodMk ((hasDerivAt_id (0:ℝ)).smul_const w)
    simpa only [α,id_eq,one_smul] using h
  have hF' : HasFDerivAt (actualNormalVelocityField d)
      (fderiv ℝ (actualNormalVelocityField d) (y,0)) (α 0) := by
    simpa only [α,zero_smul] using hF.hasFDerivAt
  have hD := hF'.comp_hasDerivAt 0 hα
  ext i j
  let E := matrixEntryL i j
  have h := E.hasFDerivAt.comp_hasDerivAt 0 hD
  have hEq : (E : Mat dim → ℝ) ∘ actualNormalVelocityField d ∘ α =
      fun s => normalizedFirstNormalCoeff d y s z i j :=
    funext fun s => firstNormalVelocityCoefficient_rescaled d y z s i j
  have hEntryJet : HasDerivAt (fun s => normalizedFirstNormalCoeff d y s z i j)
      (E (fderiv ℝ (actualNormalVelocityField d) (y,0) (0,w))) 0 := by
    rw [← hEq]
    exact h
  exact hEntryJet.unique (hd.normalizedFirstNormalCoeff_first hn hΩ hK hy z i j)

@[expose] def actualFramedRadialInput (d : Data dim) (p : FramedRadialParameter dim) :
    NormalCoefficientRadialParameter dim :=
  (p.1.1,(p.1.2,frameVector d.frame p.1.1 p.2))

theorem uniform_actual_framedRadialInput_jets
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (L : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ floor ε d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ s ∈ Icc (-1:ℝ) 1, ∀ z ∈ closedBall (0:X dim) L,
        LocalSmoothJetBudget (actualFramedRadialInput d) ((y,s),z) N C := by
  let P := FramedRadialParameter dim
  let Z : Set P := (closure Y ×ˢ Icc (-1:ℝ) 1) ×ˢ closedBall (0:X dim) L
  let S : P →L[ℝ] (X dim × ℝ) := ContinuousLinearMap.fst ℝ _ _
  let U : P →L[ℝ] X dim := (ContinuousLinearMap.fst ℝ (X dim) ℝ).comp S
  let W : P →L[ℝ] X dim := ContinuousLinearMap.snd ℝ _ _
  have hZ : IsCompact Z := (hYc.prod isCompact_Icc).prod (isCompact_closedBall _ _)
  obtain ⟨CS,_,hS⟩ := exists_uniform_finite_jet_bound hZ (S.contDiff (n:=∞)) N
  obtain ⟨CW,_,hW⟩ := exists_uniform_finite_jet_bound hZ (W.contDiff (n:=∞)) N
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨CG,_,hFrame⟩ := uniform_canonical_frameVectorLinear_jets (dim:=dim) K hKp M
  let Ev := (ContinuousLinearMap.apply (E:=X dim) ℝ (X dim)).flip
  let Gc := N.factorial*CG*(max 1 ‖U‖)^N
  let Vc := (2:ℝ)^N*‖Ev‖*Gc*CW
  let Reorder : ((X dim × ℝ) × X dim) →L[ℝ] NormalCoefficientRadialParameter dim :=
    (ContinuousLinearEquiv.prodAssoc ℝ (X dim) ℝ (X dim)).toContinuousLinearMap
  let CIn := max 1 (‖Reorder‖*max CS Vc)
  refine ⟨CIn,le_max_left _ _,?_⟩
  intro floor ε d hd hdFrame y hy s hs z hz
  let p : P := ((y,s),z)
  have hyΩ := hd.2.1.center_mem hy
  have hpZ : p ∈ Z := ⟨⟨subset_closure hy,hs⟩,hz⟩
  have hFrameEq : d.frame = fun x => smoothMetricFrame (d.γ x) := funext fun x => funext (hdFrame x)
  have hGj : LocalSmoothJetBudget (frameVectorLinear d.frame) y N CG := by
    rw [hFrameEq]
    exact (hFrame hΩ hd.1.1 (fun j i k x hx => hd.1.2.2.2.2.1 d.γ (by simp) j i k x hx) y hyΩ).mono_order (by omega)
  have hG : LocalSmoothJetBudget (frameVectorLinear d.frame ∘ U) p N Gc :=
    hGj.linear_precomp U p
  have hWj : LocalSmoothJetBudget W p N CW := ⟨W.contDiff.contDiffAt,hW p hpZ⟩
  have hSj : LocalSmoothJetBudget S p N CS := ⟨S.contDiff.contDiffAt,hS p hpZ⟩
  change LocalSmoothJetBudget (fun q : P => (q.1.1,(q.1.2,frameVector d.frame q.1.1 q.2))) p N CIn
  have hV := hG.bilinear hWj Ev
  have hEnlarge : ‖Reorder‖*max CS Vc ≤ CIn := le_max_right _ _
  have H := ((hSj.prod hV).linear_postcomp Reorder).enlarge hEnlarge
  have he : Reorder ∘ (fun q : P => (S q,Ev ((frameVectorLinear d.frame ∘ U) q) (W q))) =
      fun q => (q.1.1,(q.1.2,frameVector d.frame q.1.1 q.2)) := by
    funext q
    change (q.1.1,(q.1.2,frameVectorLinear d.frame q.1.1 q.2)) = _
    rw [frameVectorLinear_apply]
  rwa [he] at H

theorem uniform_actual_framedCoefficient_radialRemainder (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ 2*d.radius y → ∀ z ∈ closedBall (0:X dim) L,
        LocalSmoothJetBudget (actualFramedCoefficientRadialRemainder d) ((y,s),z) N C ∧
        actualFramedCoefficientField d ((y,s),z) =
          1+s • ((firstDensityCenterLinear d y z) • (1 : Mat dim))+
            s^2 • actualFramedCoefficientRadialRemainder d ((y,s),z) := by
  have hKp := zero_lt_one.trans_le hK
  obtain ⟨η,hη,hGeom⟩ := uniform_actual_normal_radial_segment_enlarged (Y:=Y)
    hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηR,CR,hηR,hCR,hR⟩ := uniform_actual_normalCoefficient_radialRemainder
    hY hΩ hYc N hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨CIn,hCIn,hIn⟩ := uniform_actual_framedRadialInput_jets
    hΩ hYc N (by omega) K ρ c₀ M Cj hK L
  let C := N.factorial*CR*CIn^N
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCR)
    (pow_nonneg (zero_le_one.trans hCIn) _)
  refine ⟨min η ηR,C,lt_min hη hηR,hC,?_⟩
  intro floor hf ε hε hεη d hd hdFrame y hy s hs z hz
  let w := frameVector d.frame y z
  have hyΩ := hd.2.1.center_mem hy
  have hFrameY := hd.1.2.2.2.2.2.2.2 y hyΩ
  have hw : w ∈ disk d.γ y L := frameVector_mem_disk d.γ d.frame y z L hFrameY hz
  obtain ⟨hs₁,_,hRay⟩ := hGeom floor hf ε hε (hεη.trans (min_le_left _ _)) d hd y hy s hs w hw
  obtain ⟨hRj,hAffine⟩ := hR floor hf ε hε (hεη.trans (min_le_right _ _)) d hd hdFrame y hy s hs w hw
  have hInput := hIn floor ε d hd hdFrame y hy s hs₁ z hz
  refine ⟨hInput.comp hRj hCIn,?_⟩
  obtain ⟨V,hV,hTube,hF⟩ := smoothNear_actual_firstNormalVelocityCoefficient hΩ hKp hd
  have h0 := hRay 0 (by simp)
  simp only [zero_mul,zero_smul] at h0
  have hpV : (y,0) ∈ V := hTube ⟨hy,h0.1,h0.2.2.2.trans_lt (by norm_num)⟩
  have hDF : DifferentiableAt ℝ (actualNormalVelocityField d) (y,0) :=
    (hF.contDiffAt (hV.mem_nhds hpV)).differentiableAt (by simp)
  change actualNormalVelocityField d (y,s • w) = 1+s • (firstDensityCenterLinear d y z • (1 : Mat dim))+
    s^2 • actualNormalCoefficientRadialRemainder d (y,(s,w))
  rw [hAffine,actualFirstNormalCoefficient_at_zero hn hd hKp hy,
    actualFirstNormalCoefficient_verticalDerivative hn hΩ hd hKp hy z hDF]

end CalderonN

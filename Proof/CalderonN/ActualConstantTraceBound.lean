module

public import Proof.CalderonN.ActualSignedAdjointSlice
public import Proof.CalderonN.ActualSignedHorizontal

import Proof.CalderonN.SignedAdjointAtZero
import Proof.CalderonN.SignedNormalAdjointBounds
import Mathlib.Tactic

/-! Adapted from `ActualConstantTraceBound` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 4500000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The constant mode of the actual moving trace operator has a uniform
bound over compact center and dilation sets, down to radius zero. -/
theorem exists_uniform_actual_movingTrace_one_bound
    {γ g k : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    (hγ : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => γ p.1 p.2 i j))
    (hγPos : ∀ lam y, (γ lam y).PosDef)
    (hg : ∀ i j, ContDiff ℝ ∞ (fun p : ℝ × (X dim) => g p.1 p.2 i j))
    (hgPos : ∀ lam y, (g lam y).PosDef)
    (hE : ContDiff ℝ ∞ (fun q : ℝ × ((X dim) × (X dim)) => E q.1 q.2))
    (he : ∀ i, ContDiff ℝ ∞ (fun q : ℝ × (X dim) => e q.1 q.2 i))
    {S : Set ℝ} {K Y Y' Ω : Set (X dim)} (hS : IsCompact S) (hK : IsCompact K)
    (hY : IsOpen Y) (hY' : IsOpen Y') (hYK : Y ⊆ K) (hKY' : K ⊆ Y')
    {ρ ε D M P Γ T : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hM : 1 ≤ M)
    (hP : 0 ≤ P) (hΓ : 0 ≤ Γ) (hT : 0 ≤ T)
    (hNormal : ∀ lam ∈ S, NormalCoordinates Y' Ω (γ lam) (E lam) (fun _ => ρ))
    (hFrame : ∀ lam ∈ S, ∀ y ∈ K, ∀ i j,
      metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (hConf : ∀ lam ∈ S, ∀ y ∈ K, ∃ c : ℝ, 0 < c ∧ γ lam y = c • g lam y)
    (hCoeff : ∀ lam ∈ S, ∀ y ∈ K,
      (∀ i j, |principal (γ lam) (k lam) y i j| ≤ P) ∧
      (∀ l i j, |christoffel (γ lam) y l i j| ≤ Γ) ∧
      (∀ l, |drift (γ lam) (k lam) y l| ≤ T))
    (hGeom : ∀ lam ∈ S, ∀ y ∈ K, ∀ w ∈ (standardSphere dim),
      (∀ i, ‖connection (γ lam) y (axis i) (frameVector (e lam) y w)‖ ≤ M) ∧
      ‖fderiv ℝ (fun z => (movingBallToFrame (γ lam) (e lam) z).2)
        (y,frameVector (e lam) y w)‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam ∈ S, ∀ (r : (X dim) → ℝ), ContDiff ℝ ∞ r →
      (∀ y ∈ Y, r y ∈ Ioc 0 (ρ/2)) →
      (∀ y ∈ Y, ∀ i, |coordDeriv i r y| ≤ D) →
      (∀ y ∈ Y, ∀ i j, |coordDeriv i (coordDeriv j r) y| ≤ D) →
      Small Y (γ lam) (k lam) r ε →
      let A := actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r
      Dirichlet Y (γ lam) (g lam) (E lam) r →
      IsMovingTraceAdjoint Y (γ lam) (g lam) (e lam) (E lam) r A →
      ∀ y ∈ Y, ∀ w : ↥(standardSphere dim),
        ‖movingTrace (γ lam) (k lam) r A (1 : (Field dim)) (y,frameVector (e lam) y w)‖ ≤ C := by
  let C : Set (SignedNormalParameter dim) := S ×ˢ (K ×ˢ (Icc 0 (ρ/2) ×ˢ closedBall (0 : (I dim) → ℝ) D))
  have hC : IsCompact C := hS.prod (hK.prod (isCompact_Icc.prod (isCompact_closedBall _ _)))
  have hE' (lam : ℝ) : ContDiff ℝ ∞ (E lam) := hE.comp (contDiff_const.prodMk contDiff_id)
  have hAdmissible : C ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e := by
    rintro ⟨⟨lam,y,s,b⟩,w⟩ ⟨hp,hw⟩
    change lam ∈ S ∧ y ∈ K ∧ s ∈ Icc 0 (ρ/2) ∧ b ∈ closedBall 0 D at hp
    rcases hp with ⟨hlam,hy,hs,_⟩
    exact signedNormalNondegenerate_of_nonneg_radius b (hE' lam) (hNormal lam hlam) (hKY' hy)
      (hFrame lam hlam y hy) ⟨hs.1,hs.2.trans_lt (half_lt_self hρ)⟩ ⟨mem_singleton _,hw⟩
  obtain ⟨B,hB,ha,hd,hBound⟩ := exists_uniform_signedNormalAdjoint_bounds hγ hγPos hg hgPos hE he hC hAdmissible
  let H := B * max D (M^2)
  let N := (dim:ℝ)^2*P*(H+(dim:ℝ)*Γ*B+B) + (dim:ℝ)^2*ε*B + (dim:ℝ)*T*B
  have hH : 0 ≤ H := mul_nonneg hB ((sq_nonneg M).trans (le_max_right _ _))
  refine ⟨N, by dsimp only [N]; positivity,?_⟩
  intro lam hlam r hr hR h₁ h₂ hSmall A hDir hA
  let α := scaledFirstTrace r A
  let p := actualSignedNormalParameter lam r
  let L := actualSignedAngularLift (γ lam) (e lam) lam r
  let a := signedNormalFirstAdjoint γ g E e
  let d := signedNormalAdjointRemainder γ g E e
  let f (j : (I dim)) (q : (X dim) × (X dim)) : ℂ := (a j (L q) : ℂ)
  have hSmoothγ : SmoothMetric univ (γ lam) :=
    ⟨fun i j => ((hγ i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,fun y _ => hγPos lam y⟩
  have hSmoothE (i : (I dim)) : ContDiff ℝ ∞ (fun y => e lam y i) :=
    (he i).comp (contDiff_const.prodMk contDiff_id)
  have hFrameY (y : (X dim)) (hy : y ∈ Y) := hFrame lam hlam y (hYK hy)
  have hCmem {y : (X dim)} (hy : y ∈ Y) {s : ℝ} (hs : s ∈ Icc 0 (ρ/2)) :
      (lam,(y,(s,fun i => coordDeriv i r y))) ∈ C := by
    refine ⟨hlam,hYK hy,hs,?_⟩
    rw [mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg hD]
    exact fun i => by simpa only [Real.norm_eq_abs] using h₁ y hy i
  have hpC {y : (X dim)} (hy : y ∈ Y) : p y ∈ C :=
    hCmem hy ⟨(hR y hy).1.le,(hR y hy).2⟩
  have hSlice {p₀ : (SignedNormalParameter dim)} (hp₀ : p₀ ∈ C) :
      {p₀} ×ˢ closedBall (0 : (X dim)) 1 ⊆ signedNormalNondegenerate E e :=
    fun _ hq => hAdmissible ⟨mem_singleton_iff.mp hq.1 ▸ hp₀,hq.2⟩
  have hId {y : (X dim)} (hy : y ∈ Y) := scaledActualAdjoints_eq_signed hγ hγPos hg hgPos hE he
    hr hy (hR y hy).1.ne' (hFrameY y hy) hA (hSlice (hpC hy))
  have hLiftEq {y : (X dim)} (hy : y ∈ Y) (w : (X dim)) :
      L (y,frameVector (e lam) y w) = (p y,w) := by
    change (p y,(movingBallToFrame (γ lam) (e lam) (movingBallFromFrame (e lam) (y,w))).2) = (p y,w)
    exact congrArg
      (fun z : (X dim) × (X dim) => (p y,z.2)) (movingBallToFrame_fromFrame (w := w) (hFrameY y hy))
  have hEq (j : (I dim)) : EqOn (α j) (f j) (bundle Y (γ lam)) := by
    apply eqOn_bundle_of_eqOn_frames hFrameY
    intro y hy w
    have h := (hId hy).1 w w.property j
    change α j (y,frameVector (e lam) y w) = (a j (L (y,frameVector (e lam) y w)) : ℂ)
    rw [hLiftEq hy]
    exact h
  intro y hy w
  let q := (y,frameVector (e lam) y w)
  have hq : q ∈ bundle Y (γ lam) := ⟨hy,frameVector_mem_sphere _ _ _ (hFrameY y hy) w⟩
  have hlq : L q ∈ C ×ˢ (standardSphere dim) := by
    change (L (y,frameVector (e lam) y w)) ∈ _
    rw [hLiftEq hy]
    exact ⟨hpC hy,w.property⟩
  have hDiff {u : (SignedNormalParameter dim) × (X dim) → ℝ} (hu : smoothNear u (C ×ˢ (standardSphere dim)))
      {z : (SignedNormalParameter dim) × (X dim)} (hz : z ∈ C ×ˢ (standardSphere dim)) : DifferentiableAt ℝ u z := by
    obtain ⟨U,hU,hKU,hu⟩ := hu
    exact (hu.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)
  have hHq (i j : (I dim)) : ‖horizontal (γ lam) (α j) q.1 q.2 (axis i)‖ ≤ H := by
    have hfd : DifferentiableAt ℝ (f j) q := Complex.ofRealCLM.differentiableAt.comp q
      ((hDiff (ha j) hlq).comp q ((contDiff_actualSignedAngularLift hSmoothγ hSmoothE lam hr).differentiable (by simp) q))
    have h := horizontal_eq_of_eqOn_bundle hY hSmoothγ hy (hFrameY y hy) (hEq j) w
      (differentiableAt_of_smoothNear_bundle (smoothNear_scaledFirstTrace hr hA j) hq) hfd (axis i)
    change horizontal (γ lam) (α j) q.1 q.2 (axis i) = horizontal (γ lam) (f j) q.1 q.2 (axis i) at h
    rw [h]
    exact norm_horizontal_actualSignedAngularLift_le hSmoothγ hSmoothE lam hr i q hD hM
      (h₁ y hy i) (h₂ y hy i) ((hGeom lam hlam y (hYK hy) w w.property).1 i)
      (hGeom lam hlam y (hYK hy) w w.property).2 (hDiff (ha j) hlq) (hBound _ hlq i j).2.1
  have haQ (j : (I dim)) : ‖α j q‖ ≤ B := by
    have ht : α j q = (a j (p y,w) : ℂ) := (hId hy).1 w w.property j
    rw [ht,Complex.norm_real]
    exact (hBound (p y,(w:(X dim))) ⟨hpC hy,w.property⟩ 0 j).1
  let b (i : (I dim)) := coordDeriv i r y
  let p₀ : (SignedNormalParameter dim) := (lam,(y,(0,b)))
  let τ (i j : (I dim)) : ℂ := (d i j (p₀,w) : ℂ)
  have hp₀ : p₀ ∈ C := hCmem hy ⟨le_rfl,(half_pos hρ).le⟩
  have hτ (i j : (I dim)) : ‖τ i j‖ ≤ B := by
    change ‖(d i j (p₀,w) : ℂ)‖ ≤ B
    rw [Complex.norm_real]
    exact (hBound (p₀,(w:(X dim))) ⟨hp₀,w.property⟩ i j).2.2.1
  obtain ⟨c,hc,hγc⟩ := hConf lam hlam y (hYK hy)
  have hz := sum_inverse_mul_signedNormalAdjointRemainder_zero hY' (hE' lam) (hNormal lam hlam)
    (hKY' (hYK hy)) (hγPos lam y) (hFrameY y hy) hc hγc b
      (contDiffOn_signedNormalFirstAdjoint_slice hγ hγPos hg hgPos hE he p₀ (hSlice hp₀)) w.property
  have hzero : ∑ i, ∑ j, ((γ lam y)⁻¹ i j : ℂ) * τ i j = 0 := by
    change ∑ i, ∑ j, ((γ lam y)⁻¹ i j : ℂ) * (d i j (p₀,w) : ℂ) = 0
    exact_mod_cast hz
  have hL (i j : (I dim)) :
      ‖(r y : ℂ) * adjointField A i (α j) q - Complex.ofReal (coordDeriv i r y) * α j q - τ i j‖ ≤ B*r y := by
    have hId' := (hId hy).2 w w.property i j
    change (r y : ℂ) * adjointField A i (α j) q - Complex.ofReal (coordDeriv i r y) * α j q =
      (d i j (p y,w) : ℂ) at hId'
    rw [hId']
    change ‖(d i j (p y,w) : ℂ) - (d i j (p₀,w) : ℂ)‖ ≤ B*r y
    rw [← Complex.ofReal_sub,Complex.norm_real]
    have hseg (s : ℝ) (hs : s ∈ Icc 0 (r y)) :
        ((lam,(y,(s,b))),(w : (X dim))) ∈ C ×ˢ (standardSphere dim) :=
      ⟨hCmem hy ⟨hs.1,hs.2.trans (hR y hy).2⟩,w.property⟩
    exact signedNormal_radius_difference_le (hR y hy).1.le
      (fun s hs => hDiff (hd i j) (hseg s hs))
      (fun s hs => (hBound ((lam,(y,(s,b))),(w:(X dim))) (hseg s hs) i j).2.2.2)
  obtain ⟨hPc,hΓc,hTc⟩ := hCoeff lam hlam y (hYK hy)
  exact norm_movingTrace_one_le_of_scaled_bounds hSmoothγ (hE' lam) hr hDir hFrameY hA (k lam)
    hq (hR y hy).1 (hSmall y hy).1 hPc hΓc hTc hHq haQ τ hτ hzero hL

end CalderonN

module

public import Proof.Manuscript.ScalarInteriorJets
public import Proof.Manuscript.ScalarCrossSlices

import Proof.CalderonN.CrossNormalConvergence
import Proof.CalderonN.EllipticCalculus
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Proof.CalderonN.NormalTensorSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

public section

open Set Filter MeasureTheory CalderonN LocalMetricExtension
open scoped ContDiff ENNReal Topology

noncomputable section

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

@[expose] def ScalarInteriorJets (L : ScalarElliptic n) (D : Set (X n)) : Prop :=
  ∀ (K : Set (X n)), IsCompact K → K ⊆ D → ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (u : ChartL2 D) {f : X n → ℝ}, L.SolvesOn D f →
      (u : X n → ℝ) =ᵐ[volume.restrict D] f →
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖u‖

theorem scalarInteriorJets_of_smoothOn {L : ScalarElliptic n} {D : Set (X n)}
    (hD : IsOpen D) (hL : L.SmoothOn D) : ScalarInteriorJets L D :=
  fun _ hK hKD k => exists_scalar_interior_jet_bound hD hL hK hKD k

private abbrev FirstJet (d : ℕ) := X d →L[ℝ] ℝ
private abbrev SecondJet (d : ℕ) := X d →L[ℝ] FirstJet d

private def firstJetEval (L : ScalarElliptic n) (x : X n) : FirstJet n →L[ℝ] ℝ :=
  ∑ i, L.first x i • ContinuousLinearMap.apply ℝ ℝ (axis i)

private def secondJetEval (L : ScalarElliptic n) (x : X n) : SecondJet n →L[ℝ] ℝ :=
  ∑ i, ∑ j, L.principalMatrix x i j •
    (ContinuousLinearMap.apply ℝ ℝ (axis j)).comp (ContinuousLinearMap.apply ℝ (FirstJet n) (axis i))

private theorem apply_eq_jetEval {L : ScalarElliptic n} {u : X n → ℝ} {x : X n}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) x) :
    L.apply u x = secondJetEval L x (fderiv ℝ (fderiv ℝ u) x) +
      firstJetEval L x (fderiv ℝ u x) + L.zeroth x * u x := by
  have hsecond (i j : I n) :
      coordDeriv i (coordDeriv j u) x = fderiv ℝ (fderiv ℝ u) x (axis i) (axis j) := by
    let A := ContinuousLinearMap.apply ℝ ℝ (axis j)
    have h := A.hasFDerivAt.comp x hu.hasFDerivAt
    change fderiv ℝ (A ∘ fderiv ℝ u) x (axis i) = _
    rw [h.fderiv]
    rfl
  change (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j u) x) +
    (∑ i, L.first x i * ((fderiv ℝ u x) (axis i))) + L.zeroth x * u x = _
  simp_rw [hsecond]
  simp only [firstJetEval, secondJetEval, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]

private theorem apply_congr_germ {L : ScalarElliptic n} {f g : X n → ℝ} {x : X n}
    (heq : f =ᶠ[𝓝 x] g) :
    L.apply f x = L.apply g x := by
  have h₁ (j : I n) : coordDeriv j f =ᶠ[𝓝 x] coordDeriv j g := by
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : X n →L[ℝ] ℝ => A (axis j)) hy
  have h₂ (i j : I n) :
      coordDeriv i (coordDeriv j f) x = coordDeriv i (coordDeriv j g) x :=
    congrArg (fun A : X n →L[ℝ] ℝ => A (axis i)) (h₁ j).fderiv_eq
  change (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j f) x) +
    (∑ i, L.first x i * coordDeriv i f x) + L.zeroth x * f x =
      (∑ i, ∑ j, L.principalMatrix x i j * coordDeriv i (coordDeriv j g) x) +
    (∑ i, L.first x i * coordDeriv i g x) + L.zeroth x * g x
  simp only [h₂, (h₁ _).eq_of_nhds, heq.eq_of_nhds]

set_option maxHeartbeats 1600000 in
/-- The literal scalar second-order expression commutes with a normally
convergent series. The evaluation uses the same coordinate jets. -/
theorem hasSum_scalar_apply_of_uniform_jets {ι : Type*} {f : ι → X n → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (v : ℕ → ι → ℝ)
    (hs : ∀ k : ℕ, Summable (v k))
    (hbound : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ v k i)
    (L : ScalarElliptic n) (x : X n) :
    HasSum (fun i => L.apply (f i) x) (L.apply (fun y => ∑' i, f i y) x) := by
  let F (x : X n) := ∑' i, f i x
  have h₀ : ∀ x : X n, Summable (fun i => f i x) := fun x =>
    (hs 0).of_norm_bounded (by simpa only [norm_iteratedFDeriv_zero] using fun i => hbound 0 i x)
  have h₁ (i : ι) (x : X n) : ‖fderiv ℝ (f i) x‖ ≤ v 1 i := by
    simpa only [norm_iteratedFDeriv_one] using hbound 1 i x
  have h₂ (i : ι) (x : X n) : ‖fderiv ℝ (fderiv ℝ (f i)) x‖ ≤ v 2 i := by
    rw [← norm_iteratedFDeriv_one (x := x) (fderiv ℝ (f i)), norm_iteratedFDeriv_fderiv]
    exact hbound 2 i x
  have hf' (i : ι) : ContDiff ℝ ∞ (fderiv ℝ (f i)) := (hf i).fderiv_right (by simp)
  have d₁ : fderiv ℝ F = fun x => ∑' i, fderiv ℝ (f i) x :=
    fderiv_tsum (hs 1) (fun i => (hf i).differentiable (by simp)) h₁ (h₀ 0)
  have hsecond : HasFDerivAt (fderiv ℝ F) (∑' i, fderiv ℝ (fderiv ℝ (f i)) x) x := by
    rw [d₁]
    exact hasFDerivAt_tsum (hs 2) (fun i x => ((hf' i).differentiable (by simp) x).hasFDerivAt) h₂
      ((hs 1).of_norm_bounded (fun i => h₁ i 0)) x
  have hs₁ : Summable (fun i => fderiv ℝ (f i) x) := (hs 1).of_norm_bounded (fun i => h₁ i x)
  let F₂ : ι → SecondJet n := fun i => fderiv ℝ (fderiv ℝ (f i)) x
  have hs₂ : Summable F₂ :=
    Summable.of_norm_bounded (E := SecondJet n) (f := F₂) (g := v 2) (hs 2) (fun i => h₂ i x)
  have hL₁ : HasSum (fun i => firstJetEval L x (fderiv ℝ (f i) x))
      (firstJetEval L x (fderiv ℝ F x)) := by
    rw [d₁]
    exact (firstJetEval L x).hasSum hs₁.hasSum
  have hL₂ : HasSum (fun i => secondJetEval L x (fderiv ℝ (fderiv ℝ (f i)) x))
      (secondJetEval L x (fderiv ℝ (fderiv ℝ F) x)) := by
    rw [hsecond.fderiv]
    exact (secondJetEval L x).hasSum hs₂.hasSum
  have h := (hL₂.add hL₁).add ((h₀ x).hasSum.mul_left (L.zeroth x))
  have he (i : ι) := apply_eq_jetEval (L := L) ((hf' i).differentiable (by simp) x)
  have hF := apply_eq_jetEval (L := L) hsecond.differentiableAt
  change HasSum (fun i => L.apply (f i) x) (L.apply F x)
  rw [show (fun i => L.apply (f i) x) = _ from funext he, hF]
  exact h

/-- A family of compactly supported scalar representatives has common
global jet bounds whenever its interior bounds are common on the cutoff
support through the selected order. -/
theorem exists_scalar_global_cutoff_jet_bound_family {Θ : Type*} {U : Set (X n)}
    (hU : IsOpen U) (L : Θ → ScalarElliptic n) {χ : (X n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (k : ℕ)
    (hjet : ∀ r ≤ k, ∃ B : ℝ, 0 ≤ B ∧
      ∀ p (u : ChartL2 U) {f : X n → ℝ}, (L p).SolvesOn U f →
        (u : X n → ℝ) =ᵐ[volume.restrict U] f →
        ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ r f x‖ ≤ B * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p (u : ChartL2 U) (f : X n → ℝ), (L p).SolvesOn U f →
      (u : X n → ℝ) =ᵐ[volume.restrict U] f →
      ∀ x : X n, ‖iteratedFDeriv ℝ k (fun y => χ y * f y) x‖ ≤ C * ‖u‖ := by
  choose B hB hbound using (fun m : ℕ => hjet (k-m) (Nat.sub_le _ _))
  have hcb (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ m χ x‖ ≤ A := by
    obtain ⟨A,hA⟩ := hχc.exists_bound_of_continuousOn
      ((hχ.continuous_iteratedFDeriv (m := m) (by simp)).continuousOn)
    exact ⟨max A 0,le_max_right _ _,fun x hx => (hA x hx).trans (le_max_left _ _)⟩
  choose A hA hAbound using hcb
  let C := ∑ m ∈ Finset.range (k+1), (k.choose m : ℝ) * A m * B m
  have hC : 0 ≤ C := Finset.sum_nonneg fun m _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA m)) (hB m)
  refine ⟨C, hC, fun p u f hf hrep x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · have hxU := hχU hx
    have hmul := norm_iteratedFDerivWithin_mul_le hχ.contDiffOn hf.1 hU.uniqueDiffOn hxU
      (n := k) (by simp)
    simp_rw [iteratedFDerivWithin_of_isOpen _ hU hxU] at hmul
    refine hmul.trans ?_
    rw [show C = _ from rfl, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m _
    rw [mul_assoc ((k.choose m : ℝ) * A m)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (hAbound m x hx) (Nat.cast_nonneg _))
      (hbound m p u hf hrep x hx) (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (hA m))
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hx] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
    have hz : iteratedFDeriv ℝ k (fun _ : (X n) => (0 : ℝ)) x = 0 := by
      cases k with
      | zero => ext z; simp
      | succ k => exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := (X n)) (Nat.succ_ne_zero k) (0 : ℝ)) x
    rw [hz,norm_zero]
    exact mul_nonneg hC (norm_nonneg _)



-- Scalar form of the cutoff estimate from the released InteriorJetCutoff.
/-- Compactly supporting a scalar representative gives a uniform
global bound on each derivative of the cutoff representative. -/
theorem exists_scalar_global_cutoff_jet_bound {U : Set (X n)} (hU : IsOpen U) {L : ScalarElliptic n}
    (hjet : ScalarInteriorJets L U) {χ : (X n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ChartL2 (d := n) U) (f : (X n) → ℝ), L.SolvesOn U f →
      (u : (X n) → ℝ) =ᵐ[(volume : Measure (X n)).restrict U] f →
      ∀ x : (X n), ‖iteratedFDeriv ℝ k (fun y => χ y * f y) x‖ ≤ C * ‖u‖ := by
  obtain ⟨C,hC,h⟩ := exists_scalar_global_cutoff_jet_bound_family hU (fun _ : Unit => L)
    hχ hχc hχU k (fun r _ => by
      obtain ⟨B,hB,h⟩ := hjet (tsupport χ) hχc hχU r
      exact ⟨B,hB,fun _ u _ => h u⟩)
  exact ⟨C,hC,h ()⟩

private theorem apply_const_mul (L : ScalarElliptic n) {u : X n → ℝ} (hu : ContDiff ℝ ∞ u)
    (r : ℝ) (x : X n) :
    L.apply (fun y => r * u y) x = r * L.apply u x := by
  have hu' := (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hr : ContDiff ℝ ∞ (fun y => r * u y) := (contDiff_const (c := r)).mul hu
  have hr' := (hr.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [apply_eq_jetEval hr', apply_eq_jetEval hu']
  have hF : fderiv ℝ (fun y => r * u y) = r • fderiv ℝ u :=
    fderiv_const_smul_field r
  have hF₂ : fderiv ℝ (r • fderiv ℝ u) x =
      r • fderiv ℝ (fderiv ℝ u) x := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ u) r) x
  rw [hF, hF₂]
  simp only [Pi.smul_apply,map_smul,smul_eq_mul]
  ring

/-- At a point where every summand solves the same scalar equation,
the weighted normal series solves it as well. -/
theorem scalar_apply_tsum_mul_eq_zero_of_global_jets {ι : Type*}
    {f : ι → (X n) → ℝ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {a c q : ι → ℝ} (_ha : ∀ i, 0 ≤ a i) (hq : ∀ i, ‖q i‖ ≤ c i)
    {A : ℕ → ℝ} (_hA : ∀ k, 0 ≤ A k)
    (hFa : ∀ k i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ A k * a i)
    (hsum : Summable (fun i => a i * c i))
    (L : ScalarElliptic n) (x : (X n)) (hLap : ∀ i, L.apply (f i) x = 0) :
    L.apply (fun y => ∑' i, q i * f i y) x = 0 := by
  have hfi (i : ι) : ContDiff ℝ ∞ (fun y => q i * f i y) :=
    contDiff_const.mul (hf i)
  have hj (k : ℕ) (i : ι) (y : (X n)) :
      ‖iteratedFDeriv ℝ k (fun y => q i * f i y) y‖ ≤ A k * (a i * c i) := by
    have hd : ContDiffAt ℝ (k : ℕ∞ω) (f i) y :=
      (hf i).contDiffAt.of_le (by simp)
    rw [show (fun y => q i * f i y) = (fun y => q i • f i y) by funext y; rfl,
      iteratedFDeriv_const_smul_apply' hd, norm_smul]
    calc
      _ ≤ c i * (A k * a i) :=
        mul_le_mul (hq i) (hFa k i y) (norm_nonneg _) ((norm_nonneg _).trans (hq i))
      _ = _ := by ring
  have h := hasSum_scalar_apply_of_uniform_jets hfi (fun k i => A k * (a i * c i))
    (fun k => hsum.mul_left (A k)) hj L x
  have hz (i : ι) : L.apply (fun y => q i * f i y) x = 0 := by
    rw [apply_const_mul L (hf i) (q i), hLap i, mul_zero]
  simp only [hz] at h
  exact h.unique hasSum_zero


private theorem exists_point_cutoff {U : Set (X n)} (hU : IsOpen U) {p : (X n)} (hp : p ∈ U) :
    ∃ χ : (X n) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      χ =ᶠ[𝓝 p] fun _ => (1 : ℝ) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ₁⟩ := Elliptic.exists_plateau_cutoff
    hU (isCompact_singleton (x := p)) (singleton_subset_iff.mpr hp)
  exact ⟨χ,hχ,hχc,hχU,hχ₁ p (mem_singleton p)⟩


-- Adapted from the released CrossNormalConvergence using the scalar jet maps.
/-- Interior scalar derivative bounds upgrade the actual absolutely
convergent tensor series to a smooth product solution. -/
theorem exists_smooth_scalar_productSeries {D₁ D₂ : Set (X n)}
    [NeZero n] (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂)
    {L₁ L₂ : ScalarElliptic n} (hL₁ : L₁.SmoothOn D₁) (hL₂ : L₂.SmoothOn D₂)
    (hjet₁ : ScalarInteriorJets L₁ D₁) (hjet₂ : ScalarInteriorJets L₂ D₂)
    {ι : Type*} [Countable ι]
    (f : ι → scalarSolutionL2 hD₁ hL₁) (b : ι → scalarSolutionL2 hD₂ hL₂)
    {Q : ChartProductL2 (d := n) D₁ D₂} (habs : Summable fun i => ‖tensorLp (f i).1 (b i).1‖)
    (hQ : HasSum (fun i => tensorLp (f i).1 (b i).1) Q) :
    ∃ (F : (X n) × (X n) → ℝ) (a c : ι → X n → ℝ),
      L₁.ProductSolvesOn L₂ (D₁ ×ˢ D₂) F ∧
      ((Q : (X n) × (X n) → ℝ) =ᵐ[(chartMeasure D₁).prod (chartMeasure D₂)] F) ∧
      (∀ i, L₁.SolvesOn D₁ (a i)) ∧ (∀ i, L₂.SolvesOn D₂ (c i)) ∧
      (∀ i, ((f i).1 : X n → ℝ) =ᵐ[chartMeasure D₁] a i) ∧
      (∀ i, ((b i).1 : X n → ℝ) =ᵐ[chartMeasure D₂] c i) ∧
      F = (fun z => ∑' i, a i z.1 * c i z.2) := by
  classical
  choose a ha haeq using fun i => (mem_scalarSolutionL2_iff hD₁ hL₁ (f i).1).mp (f i).2
  choose c hc hceq using fun i => (mem_scalarSolutionL2_iff hD₂ hL₂ (b i).1).mp (b i).2
  let F (q : (X n) × (X n)) := ∑' i, a i q.1 * c i q.2
  have hsum : Summable (fun i => ‖(f i).1‖ * ‖(b i).1‖) := by
    simpa only [norm_tensorLp] using habs
  refine ⟨F,a,c,?_,?_,ha,hc,haeq,hceq,rfl⟩
  · suffices hlocal : ∀ q ∈ D₁ ×ˢ D₂, ContDiffAt ℝ ∞ F q ∧
        L₁.apply (fun x => F (x,q.2)) q.1 = 0 ∧
        L₂.apply (fun y => F (q.1,y)) q.2 = 0 by
      exact ⟨fun q hq => (hlocal q hq).1.contDiffWithinAt,
        fun q hq => (hlocal q hq).2.1, fun q hq => (hlocal q hq).2.2⟩
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    obtain ⟨χ,hχ,hχc,hχD,hχ₁⟩ := exists_point_cutoff hD₁ hx
    obtain ⟨ζ,hζ,hζc,hζD,hζ₁⟩ := exists_point_cutoff hD₂ hy
    let a' (i : ι) (q : (X n)) := χ q * a i q
    let c' (i : ι) (q : (X n)) := ζ q * c i q
    have ha' (i : ι) : ContDiff ℝ ∞ (a' i) :=
      Elliptic.contDiff_mul_of_tsupport_subset hD₁ hχ hχD (ha i).1
    have hc' (i : ι) : ContDiff ℝ ∞ (c' i) :=
      Elliptic.contDiff_mul_of_tsupport_subset hD₂ hζ hζD (hc i).1
    choose A hA hAb using exists_scalar_global_cutoff_jet_bound hD₁ hjet₁ hχ hχc hχD
    choose C hC hCb using exists_scalar_global_cutoff_jet_bound hD₂ hjet₂ hζ hζc hζD
    have hder₁ (k : ℕ) (i : ι) (p : (X n)) : ‖iteratedFDeriv ℝ k (a' i) p‖ ≤ A k * ‖(f i).1‖ :=
      hAb k (f i).1 (a i) (ha i) (haeq i) p
    have hder₂ (k : ℕ) (i : ι) (p : (X n)) : ‖iteratedFDeriv ℝ k (c' i) p‖ ≤ C k * ‖(b i).1‖ :=
      hCb k (b i).1 (c i) (hc i) (hceq i) p
    let J (p : (X n) × (X n)) := ∑' i, a' i p.1 * c' i p.2
    have hJ : ContDiff ℝ ∞ J := contDiff_tsum_tensor_of_global_jets
      ha' hc' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hA hC hder₁ hder₂ hsum
    have hJa : J =ᶠ[𝓝 (x,y)] F := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hχ₁,
        continuous_snd.continuousAt.preimage_mem_nhds hζ₁] with p hp hp'
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hp hp'
      simp [J,F,a',c',hp,hp']
    have hJa₁ : (fun p => J (p,y)) =ᶠ[𝓝 x] fun p => F (p,y) :=
      hJa.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
    have hJa₂ : (fun p => J (x,p)) =ᶠ[𝓝 y] fun p => F (x,p) :=
      hJa.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
    have hAt₁ (i : ι) : L₁.apply (a' i) x = 0 := by
      have h : a' i =ᶠ[𝓝 x] a i := by
        filter_upwards [hχ₁] with p hp
        simp [a',hp]
      exact (apply_congr_germ (L := L₁) h).trans ((ha i).2 x hx)
    have hAt₂ (i : ι) : L₂.apply (c' i) y = 0 := by
      have h : c' i =ᶠ[𝓝 y] c i := by
        filter_upwards [hζ₁] with p hp
        simp [c',hp]
      exact (apply_congr_germ (L := L₂) h).trans ((hc i).2 y hy)
    have hcs : Summable (fun i => ‖(f i).1‖ * (C 0 * ‖(b i).1‖)) := by
      convert hsum.mul_left (C 0) using 1
      funext i
      ring
    have has : Summable (fun i => ‖(b i).1‖ * (A 0 * ‖(f i).1‖)) := by
      convert hsum.mul_left (A 0) using 1
      funext i
      ring
    have hslice₁ := scalar_apply_tsum_mul_eq_zero_of_global_jets ha' (fun _ => norm_nonneg _)
      (fun i => by simpa only [norm_iteratedFDeriv_zero] using hder₂ 0 i y) hA hder₁ hcs L₁ x hAt₁
    have hslice₂ := scalar_apply_tsum_mul_eq_zero_of_global_jets hc' (fun _ => norm_nonneg _)
      (fun i => by simpa only [norm_iteratedFDeriv_zero] using hder₁ 0 i x) hC hder₂ has L₂ y hAt₂
    refine ⟨hJ.contDiffAt.congr_of_eventuallyEq hJa.symm,?_,?_⟩
    · rw [← apply_congr_germ (L := L₁) hJa₁]
      simpa [J,mul_comm] using hslice₁
    · rw [← apply_congr_germ (L := L₂) hJa₂]
      exact hslice₂
  · let μ := (volume : Measure (X n)).restrict D₁
    let ν := (volume : Measure (X n)).restrict D₂
    have htsum := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr habs)
    rw [hQ.tsum_eq] at htsum
    have hf' (i : ι) : ∀ᵐ q ∂μ.prod ν, (f i).1 q.1 = a i q.1 :=
      Measure.quasiMeasurePreserving_fst.ae (haeq i)
    have hb' (i : ι) : ∀ᵐ q ∂μ.prod ν, (b i).1 q.2 = c i q.2 :=
      Measure.quasiMeasurePreserving_snd.ae (hceq i)
    filter_upwards [htsum, ae_all_iff.mpr hf', ae_all_iff.mpr hb',
      ae_all_iff.mpr (fun i => tensorLp_ae (f i).1 (b i).1)] with q hsum hfa hbc htt
    have hs : HasSum (fun i => a i q.1 * c i q.2) (Q q) := by
      simpa only [htt,hfa,hbc] using hsum
    exact hs.tsum_eq.symm


private theorem norm_jet_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p : E →L[ℝ] F} (hp : ‖p‖ ≤ 1)
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ p) x‖ ≤ ‖iteratedFDeriv ℝ k f (p x)‖ := by
  rw [p.iteratedFDeriv_comp_right hf x (i := k) (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg p) hp (n := k))
    (norm_nonneg (iteratedFDeriv ℝ k f (p x)))

set_option maxHeartbeats 1800000 in
/-- A compact product jet estimate with one constant shared by all
operators in the two families. Only factor jets through `k` enter. -/
theorem exists_scalar_productSeries_jetBound_family {Θ₁ Θ₂ : Type*} {D₁ D₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (L₁ : Θ₁ → ScalarElliptic n) (L₂ : Θ₂ → ScalarElliptic n)
    {K : Set (X n × X n)} (hK : IsCompact K) (hKD : K ⊆ D₁ ×ˢ D₂) (k : ℕ)
    (hjet₁ : ∀ K' : Set (X n), IsCompact K' → K' ⊆ D₁ → ∀ r ≤ k, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p (u : ChartL2 D₁) {f : X n → ℝ}, (L₁ p).SolvesOn D₁ f →
      (u : X n → ℝ) =ᵐ[chartMeasure D₁] f → ∀ x ∈ K', ‖iteratedFDeriv ℝ r f x‖ ≤ C * ‖u‖)
    (hjet₂ : ∀ K' : Set (X n), IsCompact K' → K' ⊆ D₂ → ∀ r ≤ k, ∃ C : ℝ, 0 ≤ C ∧
      ∀ p (u : ChartL2 D₂) {f : X n → ℝ}, (L₂ p).SolvesOn D₂ f →
      (u : X n → ℝ) =ᵐ[chartMeasure D₂] f → ∀ x ∈ K', ‖iteratedFDeriv ℝ r f x‖ ≤ C * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p q {ι : Type} (f : ι → ChartL2 D₁) (b : ι → ChartL2 D₂)
      (a c : ι → X n → ℝ),
      (∀ i, (L₁ p).SolvesOn D₁ (a i)) → (∀ i, (L₂ q).SolvesOn D₂ (c i)) →
      (∀ i, (f i : X n → ℝ) =ᵐ[chartMeasure D₁] a i) →
      (∀ i, (b i : X n → ℝ) =ᵐ[chartMeasure D₂] c i) →
      Summable (fun i => ‖f i‖ * ‖b i‖) →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ k (fun z : X n × X n => ∑' i, a i z.1 * c i z.2) z‖ ≤
        C * (∑' i, ‖f i‖ * ‖b i‖) := by
  obtain ⟨χ,hχ,hχc,hχD,hχ₁⟩ := Elliptic.exists_plateau_cutoff hD₁ (hK.image continuous_fst)
    (by rintro _ ⟨z,hz,rfl⟩; exact (hKD hz).1)
  obtain ⟨ζ,hζ,hζc,hζD,hζ₁⟩ := Elliptic.exists_plateau_cutoff hD₂ (hK.image continuous_snd)
    (by rintro _ ⟨z,hz,rfl⟩; exact (hKD hz).2)
  obtain ⟨A,hA,hAb⟩ : ∃ A : ℕ → ℝ, (∀ r, 0 ≤ A r) ∧
      ∀ r ≤ k, ∀ p (u : ChartL2 D₁) (f : X n → ℝ), (L₁ p).SolvesOn D₁ f →
      (u : X n → ℝ) =ᵐ[chartMeasure D₁] f →
      ∀ x, ‖iteratedFDeriv ℝ r (fun y => χ y * f y) x‖ ≤ A r * ‖u‖ := by
    have h (r : ℕ) : ∃ A : ℝ, 0 ≤ A ∧
        (r ≤ k → ∀ p (u : ChartL2 D₁) (f : X n → ℝ), (L₁ p).SolvesOn D₁ f →
        (u : X n → ℝ) =ᵐ[chartMeasure D₁] f →
        ∀ x, ‖iteratedFDeriv ℝ r (fun y => χ y * f y) x‖ ≤ A * ‖u‖) := by
      by_cases hr : r ≤ k
      · obtain ⟨A,hA,h⟩ := exists_scalar_global_cutoff_jet_bound_family hD₁ L₁ hχ hχc hχD r
          (fun s hs => hjet₁ (tsupport χ) hχc hχD s (hs.trans hr))
        exact ⟨A,hA,fun _ => h⟩
      · exact ⟨0,le_rfl,fun h => (hr h).elim⟩
    choose A hA hAb using h
    exact ⟨A,hA,hAb⟩
  obtain ⟨B,hB,hBb⟩ : ∃ B : ℕ → ℝ, (∀ r, 0 ≤ B r) ∧
      ∀ r ≤ k, ∀ p (u : ChartL2 D₂) (f : X n → ℝ), (L₂ p).SolvesOn D₂ f →
      (u : X n → ℝ) =ᵐ[chartMeasure D₂] f →
      ∀ x, ‖iteratedFDeriv ℝ r (fun y => ζ y * f y) x‖ ≤ B r * ‖u‖ := by
    have h (r : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
        (r ≤ k → ∀ p (u : ChartL2 D₂) (f : X n → ℝ), (L₂ p).SolvesOn D₂ f →
        (u : X n → ℝ) =ᵐ[chartMeasure D₂] f →
        ∀ x, ‖iteratedFDeriv ℝ r (fun y => ζ y * f y) x‖ ≤ B * ‖u‖) := by
      by_cases hr : r ≤ k
      · obtain ⟨B,hB,h⟩ := exists_scalar_global_cutoff_jet_bound_family hD₂ L₂ hζ hζc hζD r
          (fun s hs => hjet₂ (tsupport ζ) hζc hζD s (hs.trans hr))
        exact ⟨B,hB,fun _ => h⟩
      · exact ⟨0,le_rfl,fun h => (hr h).elim⟩
    choose B hB hBb using h
    exact ⟨B,hB,hBb⟩
  let C (k : ℕ) := ∑ j ∈ Finset.range (k+1), (k.choose j : ℝ) * A j * B (k-j)
  have hC (k : ℕ) : 0 ≤ C k := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j)) (hB (k-j))
  refine ⟨C k,hC k,?_⟩
  intro p₁' p₂' ι f b a c ha hc hfa hbc hsum z hz
  let a' (i : ι) (x : X n) := χ x * a i x
  let c' (i : ι) (x : X n) := ζ x * c i x
  have ha' (i : ι) : ContDiff ℝ ∞ (a' i) :=
    Elliptic.contDiff_mul_of_tsupport_subset hD₁ hχ hχD (ha i).1
  have hc' (i : ι) : ContDiff ℝ ∞ (c' i) :=
    Elliptic.contDiff_mul_of_tsupport_subset hD₂ hζ hζD (hc i).1
  let p₁ := ContinuousLinearMap.fst ℝ (X n) (X n)
  let p₂ := ContinuousLinearMap.snd ℝ (X n) (X n)
  let R (i : ι) (z : X n × X n) := a' i z.1 * c' i z.2
  have ha'' (i : ι) : ContDiff ℝ ∞ (a' i ∘ p₁) := (ha' i).comp contDiff_fst
  have hc'' (i : ι) : ContDiff ℝ ∞ (c' i ∘ p₂) := (hc' i).comp contDiff_snd
  have hR (i : ι) : ContDiff ℝ ∞ (R i) := (ha'' i).mul (hc'' i)
  have hBound (r : ℕ) (hr : r ≤ k) (i : ι) (q : X n × X n) :
      ‖iteratedFDeriv ℝ r (R i) q‖ ≤ C r * (‖f i‖ * ‖b i‖) := by
    refine (norm_iteratedFDeriv_mul_le (ha'' i) (hc'' i) q (n := r) (by simp)).trans ?_
    rw [show C r = _ from rfl, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjr : j ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have h₁ := (norm_jet_comp_le (ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := X n) (F := X n))
      (ha' i) j q).trans (hAb j (hjr.trans hr) p₁' (f i) (a i) (ha i) (hfa i) q.1)
    have h₂ := (norm_jet_comp_le (ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := X n) (F := X n))
      (hc' i) (r-j) q).trans (hBb (r-j) ((Nat.sub_le _ _).trans hr) p₂' (b i) (c i) (hc i) (hbc i) q.2)
    calc
      _ ≤ (r.choose j : ℝ) * (A j * ‖f i‖) * (B (r-j) * ‖b i‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₁ (Nat.cast_nonneg _)) h₂
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hA j) (norm_nonneg _)))
      _ = _ := by ring
  have hEq : (fun q => ∑' i, R i q) =ᶠ[𝓝 z]
      (fun q : X n × X n => ∑' i, a i q.1 * c i q.2) := by
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hχ₁ z.1 (mem_image_of_mem _ hz)),
      continuous_snd.continuousAt.preimage_mem_nhds (hζ₁ z.2 (mem_image_of_mem _ hz))]
      with q hq₁ hq₂
    simp only [mem_preimage,mem_ofPred_eq] at hq₁ hq₂
    simp [R,a',c',hq₁,hq₂]
  rw [← (hEq.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  rw [iteratedFDeriv_tsum (N := (k : ℕ∞)) (fun i => (hR i).of_le (by simp))
    (fun r _ => hsum.mul_left (C r))
    (fun r i q hr => hBound r (by exact_mod_cast hr) i q) (by simp)]
  have hMass := hsum.hasSum.mul_left (C k)
  exact tsum_of_norm_bounded hMass (fun i => hBound k le_rfl i z)


set_option maxHeartbeats 1200000 in
/-- A fixed compact product subset has an explicit jet bound given the
total norm of the actual series and the two interior jet interfaces. -/
theorem exists_scalar_productSeries_jetBound {D₁ D₂ : Set (X n)}
    (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) {L₁ L₂ : ScalarElliptic n}
    (hjet₁ : ScalarInteriorJets L₁ D₁) (hjet₂ : ScalarInteriorJets L₂ D₂)
    {K : Set (X n × X n)} (hK : IsCompact K) (hKD : K ⊆ D₁ ×ˢ D₂) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (f : ι → ChartL2 D₁) (b : ι → ChartL2 D₂)
      (a c : ι → X n → ℝ),
      (∀ i, L₁.SolvesOn D₁ (a i)) → (∀ i, L₂.SolvesOn D₂ (c i)) →
      (∀ i, (f i : X n → ℝ) =ᵐ[chartMeasure D₁] a i) →
      (∀ i, (b i : X n → ℝ) =ᵐ[chartMeasure D₂] c i) →
      Summable (fun i => ‖f i‖ * ‖b i‖) →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ k (fun z : X n × X n => ∑' i, a i z.1 * c i z.2) z‖ ≤
        C * (∑' i, ‖f i‖ * ‖b i‖) := by
  obtain ⟨C,hC,h⟩ := exists_scalar_productSeries_jetBound_family hD₁ hD₂
    (fun _ : Unit => L₁) (fun _ : Unit => L₂) hK hKD k
    (fun K hK hKD r _ => by
      obtain ⟨C,hC,h⟩ := hjet₁ K hK hKD r
      exact ⟨C,hC,fun _ u _ => h u⟩)
    (fun K hK hKD r _ => by
      obtain ⟨C,hC,h⟩ := hjet₂ K hK hKD r
      exact ⟨C,hC,fun _ u _ => h u⟩)
  exact ⟨C,hC,h () ()⟩

end CalderonPaper.ScalarElliptic

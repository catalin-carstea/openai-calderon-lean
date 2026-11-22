module

public import Proof.CalderonN.CutoffCommutator

public import Proof.CalderonN.InteriorFluxEnergy

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

@[expose] public section

/-! Compact collar estimates adopted from `MixedKernelNativeRoomInterpolation` from anisotropic-calderon-lean revision `d6704c49395a38eb07e0249afeb8ea83d67971cc`. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace CalderonN.Elliptic

variable {dim : ℕ} [NeZero dim]
open CutoffCommutator (Lop_congr_of_eventuallyEq Lop_mul_symm)
open Strict

/-- The same compact collars give a Caccioppoli constant for the entire
compact family of elliptic operators. -/
theorem collar_caccioppoli_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    {U K : Set (X dim)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : P → Fin dim → Fin dim → (X dim) → ℝ) (ha : ∀ i k, JointSmooth fun p => a p i k)
    (hpos : ∀ p ∈ J, ∀ x ∈ U, Matrix.PosDef (fun i k => a p i k x : (Mat dim))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ w : (X dim) → ℝ, ContDiffOn ℝ ∞ w U →
      (∀ x ∈ U, Lop (a p) w x = 0) → IntegrableOn (fun x => w x ^ 2) U →
      ∫ x in K, ∑ i, pd i w x ^ 2 ≤ C * ∫ x in U, w x ^ 2 := by
  obtain ⟨V,hV,hKV,hVU,hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hVU' : V ⊆ U := subset_closure.trans hVU
  obtain ⟨L,hL,hLV,C,hC,hbound⟩ :=
    exists_interior_flux_energy_bound_family hJ hV hK hKV a ha
      (fun p hp x hx => hpos p hp x (hVU' hx))
  obtain ⟨zeta,hζ,_,hζU,hζV⟩ := exists_plateau_cutoff hU hVc hVU
  refine ⟨C,hC,fun p hp w hw hLw hwInt => ?_⟩
  let u : (X dim) → ℝ := fun x => zeta x * w x
  have hu : ContDiff ℝ ∞ u := contDiff_mul_of_tsupport_subset hU hζ hζU hw
  have he (x : (X dim)) (hx : x ∈ V) : u =ᶠ[𝓝 x] w := by
    filter_upwards [hζV x (subset_closure hx)] with y hy
    simp [u,hy]
  have hEq (x : (X dim)) (hx : x ∈ V) : Lop (a p) u x = ∑ i : Fin dim, pd i (fun _ => (0 : ℝ)) x := by
    rw [Lop_congr_of_eventuallyEq (a p) (he x hx), hLw x (hVU' hx)]
    simp [pd, coordDeriv]
  have hEstimate := hbound p hp u (fun _ _ => (0 : ℝ)) hu (fun _ => contDiff_const) hEq
  simp only [zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, add_zero] at hEstimate
  have hGradient : (∫ x in K, ∑ i, pd i u x ^ 2) = ∫ x in K, ∑ i, pd i w x ^ 2 :=
    setIntegral_congr_fun hK.measurableSet (fun x hx => Finset.sum_congr rfl
      fun i _ => by rw [pd_congr_of_eventuallyEq (he x (hKV hx)) i])
  have hMass : (∫ x in L, u x ^ 2) = ∫ x in L, w x ^ 2 :=
    setIntegral_congr_fun hL.measurableSet (fun x hx => by rw [(he x (hLV hx)).eq_of_nhds])
  rw [hGradient, hMass] at hEstimate
  exact hEstimate.trans (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set hwInt (ae_of_all _ fun x => sq_nonneg (w x)) (hLV.trans hVU').eventuallyLE) hC)

/-- The gradient on a compact collar is controlled by the (L^2) norm
on its containing room. -/
theorem collar_caccioppoli {U K : Set (X dim)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {a : Fin dim → Fin dim → (X dim) → ℝ} (ha : ∀ i k, ContDiff ℝ ∞ (a i k))
    (hpos : ∀ x ∈ U, Matrix.PosDef (fun i k => a i k x : (Mat dim))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : (X dim) → ℝ, ContDiffOn ℝ ∞ w U → (∀ x ∈ U, Lop a w x = 0) →
      IntegrableOn (fun x => w x ^ 2) U →
      ∫ x in K, ∑ i, pd i w x ^ 2 ≤ C * ∫ x in U, w x ^ 2 := by
  obtain ⟨C,hC,h⟩ := collar_caccioppoli_family
    (isCompact_singleton : IsCompact ({(0 : ℝ)} : Set ℝ)) hU hK hKU
    (fun _ => a) (fun i j => (ha i j).comp contDiff_snd) (fun _ _ => hpos)
  exact ⟨C,hC,h 0 (mem_singleton _)⟩

/-- C4a: scalar and gradient terms in the Cauchy–Schwarz estimate. -/
theorem affine_sum_sq_le (a u : ℝ) (b v : Fin dim → ℝ) :
    (a * u + ∑ j, b j * v j) ^ 2 ≤
      (a ^ 2 + ∑ j, b j ^ 2) * (u ^ 2 + ∑ j, v j ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (dim+1)))
    (Fin.cases a b) (Fin.cases u v)
  simpa only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ] using h

/-- C4b: compact coefficient bound, chosen before the function and gradient values. -/
theorem exists_compact_affine_residual_constant
    {T : Type*} [TopologicalSpace T]
    {K : Set T} (hK : IsCompact K) {beta c : T → ℝ} {q : Fin dim → T → ℝ}
    (hbeta : Continuous beta) (hc : Continuous c) (hq : ∀ j, Continuous (q j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ u : ℝ, ∀ v : Fin dim → ℝ,
      (beta x * (c x * u + ∑ j, q j x * v j)) ^ 2 ≤
        C * (u ^ 2 + ∑ j, v j ^ 2) := by
  let F : T → ℝ := fun x => beta x ^ 2 * (c x ^ 2 + ∑ j, q j x ^ 2)
  have hFc : Continuous F :=
    (hbeta.pow 2).mul ((hc.pow 2).add (continuous_finsetSum _ fun j _ => (hq j).pow 2))
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  refine ⟨max M0 0, le_max_right _ _, fun x hx u v => ?_⟩
  have hab : |F x| ≤ M0 := by
    simpa only [Real.norm_eq_abs] using hM0 x hx
  have hF : F x ≤ max M0 0 :=
    (le_abs_self (F x)).trans (hab.trans (le_max_left _ _))
  have hCS := affine_sum_sq_le (c x) u (fun j => q j x) v
  calc
    (beta x * (c x * u + ∑ j, q j x * v j)) ^ 2 =
        beta x ^ 2 * (c x * u + ∑ j, q j x * v j) ^ 2 := mul_pow _ _ 2
    _ ≤ beta x ^ 2 * ((c x ^ 2 + ∑ j, q j x ^ 2) * (u ^ 2 + ∑ j, v j ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = F x * (u ^ 2 + ∑ j, v j ^ 2) := by dsimp [F]; ring
    _ ≤ max M0 0 * (u ^ 2 + ∑ j, v j ^ 2) :=
      mul_le_mul_of_nonneg_right hF (add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- The cutoff commutator coefficients are bounded jointly on the compact
parameter and spatial sets. -/
private theorem exists_family_cutoff_residual_pointwise_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    (a : P → Fin dim → Fin dim → (X dim) → ℝ) (ha : ∀ i j, JointSmooth fun p => a p i j)
    (hs : ∀ p i j x, a p i j x = a p j i x)
    {chi beta : (X dim) → ℝ} (hchi : ContDiff ℝ ∞ chi) (hbeta : Continuous beta)
    {K : Set (X dim)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ w : (X dim) → ℝ, ContDiff ℝ ∞ w →
      (∀ x ∈ K, Lop (a p) w x = 0) → ∀ x ∈ K,
      (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2 ≤
        C * (w x ^ 2 + ∑ j, pd j w x ^ 2) := by
  let c (z : P × (X dim)) := Lop (a z.1) chi z.2
  let q (j : Fin dim) (z : P × (X dim)) := 2 * ∑ i, a z.1 i j z.2 * pd i chi z.2
  have hc : Continuous c := (jointSmooth_Lop (a := a) (f := fun _ => chi) ha (hchi.comp contDiff_snd)).continuous
  have hq (j : Fin dim) : Continuous (q j) :=
    continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (ha i j).continuous.mul ((contDiff_pd hchi).continuous.comp continuous_snd))
  obtain ⟨C,hC,hbound⟩ := exists_compact_affine_residual_constant (hJ.prod hK)
    (hbeta.comp continuous_snd) hc hq
  refine ⟨C,hC,fun p hp w hw hLw x hx => ?_⟩
  have hcomm := Lop_mul_symm (a p) (fun i j => jointSmooth_slice (ha i j) p) (hs p) hchi hw x
  rw [hLw x hx] at hcomm
  have heq : Lop (a p) (fun y => chi y * w y) x =
      c (p,x) * w x + ∑ j, q j (p,x) * pd j w x := by
    rw [hcomm]
    simp only [c,q, mul_zero, zero_add, Finset.sum_mul, Finset.mul_sum]
    rw [mul_comm (w x) (Lop (a p) chi x)]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact hbound (p,x) ⟨hp,hx⟩ (w x) (fun j => pd j w x)

/-- C4d: the same bound for a solution smooth only on the open room `D`, through a
plateau `zeta = 1` near `K ∪ tsupport chi` chosen before `w` (germ equality only). -/
private theorem exists_family_cutoff_residual_pointwise_bound_local
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    (a : P → Fin dim → Fin dim → (X dim) → ℝ) (ha : ∀ i j, JointSmooth fun p => a p i j)
    (hs : ∀ p i j x, a p i j x = a p j i x)
    {D K : Set (X dim)} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    {chi beta : (X dim) → ℝ} (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (htc : tsupport chi ⊆ D) (hbeta : Continuous beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ w : (X dim) → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ D, Lop (a p) w x = 0) → ∀ x ∈ K,
      (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2 ≤
        C * (w x ^ 2 + ∑ j, pd j w x ^ 2) := by
  obtain ⟨zeta, hzeta, -, hzD, hz1⟩ :=
    CalderonN.Elliptic.exists_plateau_cutoff hD (hK.union hchic)
      (Set.union_subset hKD htc)
  obtain ⟨C, hC, hb⟩ := exists_family_cutoff_residual_pointwise_bound hJ a ha hs hchi hbeta hK
  refine ⟨C, hC, fun p hp w hw hLw x hx => ?_⟩
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    CalderonN.Elliptic.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y (Or.inl hy)] with z hz
    rw [hz, one_mul]
  have hchiW : (fun y => chi y * (zeta y * w y)) = fun y => chi y * w y := by
    funext y
    by_cases hy : y ∈ tsupport chi
    · rw [(hz1 y (Or.inr hy)).eq_of_nhds, one_mul]
    · have h0 : chi y = 0 := (notMem_tsupport_iff_eventuallyEq.mp hy).eq_of_nhds
      rw [h0, zero_mul, zero_mul]
  have hLW : ∀ y ∈ K, Lop (a p) (fun y => zeta y * w y) y = 0 := fun y hy => by
    rw [Lop_congr_of_eventuallyEq (a p) (hgerm y hy)]
    exact hLw y (hKD hy)
  have h := hb p hp _ hW hLW x hx
  rw [hchiW] at h
  have hval : zeta x * w x = w x := by rw [(hz1 x (Or.inl hx)).eq_of_nhds, one_mul]
  have hpdx : ∀ j, pd j (fun y => zeta y * w y) x = pd j w x := fun j =>
    pd_congr_of_eventuallyEq (hgerm x hx) j
  simp only [hval, hpdx] at h
  exact h

/-- C4e: integrated collar residual bound by the SAME `L²(E)` norm; `C` precedes `w`. -/
theorem exists_family_collar_residual_l2_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J)
    (a : P → Fin dim → Fin dim → (X dim) → ℝ) (ha : ∀ i j, JointSmooth fun p => a p i j)
    (hs : ∀ p i j x, a p i j x = a p j i x)
    {D E K : Set (X dim)} (hD : IsOpen D) (hE : IsOpen E) (hED : E ⊆ D)
    (hK : IsCompact K) (hKE : K ⊆ E)
    (hpos : ∀ p ∈ J, ∀ x ∈ E, Matrix.PosDef (fun i k => a p i k x : (Mat dim)))
    {chi beta : (X dim) → ℝ} (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (htc : tsupport chi ⊆ D) (hbeta : Continuous beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ w : (X dim) → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ D, Lop (a p) w x = 0) → IntegrableOn (fun x => w x ^ 2) E →
      ∫ x in K, (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2 ≤
        C * ∫ x in E, w x ^ 2 := by
  obtain ⟨C1, hC1, hpt⟩ := exists_family_cutoff_residual_pointwise_bound_local hJ a ha hs hD hK
    (hKE.trans hED) hchi hchic htc hbeta
  obtain ⟨C2, hC2, hcac⟩ := collar_caccioppoli_family hJ hE hK hKE a ha hpos
  obtain ⟨zeta, hzeta, -, hzD, hz1⟩ :=
    CalderonN.Elliptic.exists_plateau_cutoff hD hK (hKE.trans hED)
  refine ⟨C1 * (1 + C2), by positivity, fun p hp w hw hLw hwint => ?_⟩
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    CalderonN.Elliptic.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y hy] with z hz
    rw [hz, one_mul]
  have hwK : ContinuousOn w K := hw.continuousOn.mono (hKE.trans hED)
  have hpdK : ∀ j, ContinuousOn (fun x => pd j w x) K := fun j =>
    (CalderonN.Elliptic.contDiff_pd_apply hW).continuous.continuousOn.congr
      fun x hx => (pd_congr_of_eventuallyEq (hgerm x hx) j).symm
  have hiw : IntegrableOn (fun x => w x ^ 2) K := (hwK.pow 2).integrableOn_compact hK
  have higrad : IntegrableOn (fun x => ∑ j, pd j w x ^ 2) K :=
    (continuousOn_finsetSum _ fun j _ => (hpdK j).pow 2).integrableOn_compact hK
  have hcw : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    CalderonN.Elliptic.contDiff_mul_of_tsupport_subset hD hchi htc hw
  have hLop : Continuous (Lop (a p) (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (CalderonN.Elliptic.contDiff_pd_apply
      (ContDiff.sum fun k _ => (jointSmooth_slice (ha i k) p).mul
        (CalderonN.Elliptic.contDiff_pd_apply hcw))).continuous
  have hres : IntegrableOn (fun x => (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2) K :=
    ((hbeta.mul hLop).pow 2).continuousOn.integrableOn_compact hK
  have h1 : ∫ x in K, (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2 ≤
      ∫ x in K, C1 * (w x ^ 2 + ∑ j, pd j w x ^ 2) :=
    setIntegral_mono_on hres ((hiw.add higrad).const_mul C1) hK.measurableSet
      (fun x hx => hpt p hp w hw hLw x hx)
  rw [integral_const_mul, integral_add hiw higrad] at h1
  have h2 : ∫ x in K, w x ^ 2 ≤ ∫ x in E, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hKE.eventuallyLE
  have h3 := hcac p hp w (hw.mono hED) (fun x hx => hLw x (hED hx)) hwint
  calc ∫ x in K, (beta x * Lop (a p) (fun y => chi y * w y) x) ^ 2
      ≤ C1 * ((∫ x in K, w x ^ 2) + (∫ x in K, ∑ j, pd j w x ^ 2)) := h1
    _ ≤ C1 * ((∫ x in E, w x ^ 2) + C2 * (∫ x in E, w x ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC1
    _ = C1 * (1 + C2) * (∫ x in E, w x ^ 2) := by ring

/-- C4e: integrated collar residual bound by the SAME `L²(E)` norm; `C` precedes `w`. -/
theorem exists_collar_residual_l2_bound
    (a : Fin dim → Fin dim → (X dim) → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hs : ∀ i j x, a i j x = a j i x)
    {D E K : Set (X dim)} (hD : IsOpen D) (hE : IsOpen E) (hED : E ⊆ D)
    (hK : IsCompact K) (hKE : K ⊆ E)
    (hpos : ∀ x ∈ E, Matrix.PosDef (fun i k => a i k x : (Mat dim)))
    {chi beta : (X dim) → ℝ} (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (htc : tsupport chi ⊆ D) (hbeta : Continuous beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : (X dim) → ℝ, ContDiffOn ℝ ∞ w D →
      (∀ x ∈ D, Lop a w x = 0) → IntegrableOn (fun x => w x ^ 2) E →
      ∫ x in K, (beta x * Lop a (fun y => chi y * w y) x) ^ 2 ≤
        C * ∫ x in E, w x ^ 2 := by
  obtain ⟨C,hC,h⟩ := exists_family_collar_residual_l2_bound
    (isCompact_singleton : IsCompact ({(0 : ℝ)} : Set ℝ))
    (fun _ => a) (fun i j => (ha i j).comp contDiff_snd) (fun _ => hs)
    hD hE hED hK hKE (fun _ _ => hpos) hchi hchic htc hbeta
  exact ⟨C,hC,h 0 (mem_singleton _)⟩

/-- Elementary combination of the two collar bounds inside the weighted split. -/
theorem weighted_two_collar_combine {C EB EH IB IH D S K : ℝ} (hC : 0 ≤ C) (hEB : 0 ≤ EB)
    (hEH : 0 ≤ EH) (h1 : IB ≤ K * D) (h2 : IH ≤ K * S) :
    C * (EB * IB + EH * IH) ≤ C * K * (EB * D + EH * S) := by
  have h := add_le_add (mul_le_mul_of_nonneg_left h1 hEB) (mul_le_mul_of_nonneg_left h2 hEH)
  calc C * (EB * IB + EH * IH) ≤ C * (EB * (K * D) + EH * (K * S)) :=
        mul_le_mul_of_nonneg_left h hC
    _ = C * K * (EB * D + EH * S) := by ring

end CalderonN.Elliptic

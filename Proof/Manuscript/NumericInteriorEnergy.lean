module

public import Proof.CalderonN.InteriorFluxEnergy
public import Proof.CalderonN.InteriorPointwise

import all Proof.CalderonN.DifferentiatedFlux
import all Proof.CalderonN.InteriorWordEnergy
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.Elliptic

variable {d : ℕ} [NeZero d]

/-- The pointwise ellipticity floor for a coordinate divergence field. -/
@[expose] def HasEllipticityFloor (a : I d → I d → X d → ℝ) (U : Set (X d)) (lam : ℝ) : Prop :=
  ∀ x ∈ U, ∀ p : I d → ℝ, lam * (∑ i, p i ^ 2) ≤ ∑ i, ∑ j, p i * a i j x * p j

/-- A common budget for coordinate words of the coefficient field. -/
@[expose] def HasWordBudget (a : I d → I d → X d → ℝ) (U : Set (X d)) (Ma : ℝ) (N : ℕ) : Prop :=
  ∀ x ∈ U, ∀ i j : I d, ∀ w : List (I d), w.length ≤ N →
    |wordDeriv w (a i j) x| ≤ Ma

/-- Numerical Caccioppoli bound. The proof uses the release's
`exists_interior_flux_energy_bound_family` energy test with the compact-family
budgets supplied explicitly by numbers. -/
theorem exists_interior_flux_energy_bound_numeric {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {lam Ma : ℝ} (hlam : 0 < lam) :
    ∃ L : Set (X d), IsCompact L ∧ L ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : (I d) → (I d) → (X d) → ℝ, (∀ i j, ContDiff ℝ ∞ (a i j)) →
        (∀ x ∈ U, ∀ i j, |a i j x| ≤ Ma) → HasEllipticityFloor a U lam →
        ∀ (u : (X d) → ℝ) (F : (I d) → (X d) → ℝ), ContDiff ℝ ∞ u → (∀ i, ContDiff ℝ ∞ (F i)) →
        (∀ x ∈ U, Lop a u x = ∑ i, pd i (F i) x) →
        (∫ x in K, ∑ i, pd i u x ^ 2) ≤ C * ∫ x in L, (u x^2 + ∑ i, F i x^2) := by
  obtain ⟨η,hη,hηc,hηU,hηK⟩ := exists_plateau_cutoff hU hK hKU
  let L := tsupport η
  obtain ⟨Mb,hMb⟩ := hηc.exists_bound_of_continuousOn (f := fun x : (X d) => fun i : (I d) => pd i η x)
    (continuous_pi (fun _ => (contDiff_pd hη).continuous)).continuousOn
  obtain ⟨Me,hMe⟩ := hηc.exists_bound_of_continuousOn hη.continuous.continuousOn
  let M := max (max Ma Mb) (max Me 0)
  have hM : 0 ≤ M := (le_max_right Me 0).trans (le_max_right _ _)
  let Cᵤ := 4*(d:ℝ)^3*M^4/lam+(d:ℝ)*M^2
  let CF := M^2/lam+M^2
  let C := max Cᵤ CF
  have hC : 0 ≤ C := (by dsimp only [Cᵤ]; positivity : 0 ≤ Cᵤ).trans (le_max_left _ _)
  refine ⟨L,hηc,hηU,2*C/lam,by positivity,fun a ha hMat hell u F hu hF hPDE => ?_⟩
  let A (x : (X d)) := η x ^ 2 * ∑ i, pd i u x ^ 2
  let B (x : (X d)) := u x^2 + ∑ i, F i x^2
  let φ (x : (X d)) := η x^2 * u x
  let G (i : (I d)) (x : (X d)) := (∑ j, a i j x * pd j u x) - F i x
  let T (x : (X d)) := ∑ i, pd i φ x * G i x
  have hφ : ContDiff ℝ ∞ φ := (hη.pow 2).mul hu
  have hφc : HasCompactSupport φ := hηc.mono fun x hx hz => hx (by simp [φ,hz])
  have hG (i : (I d)) : ContDiff ℝ ∞ (G i) :=
    (ContDiff.sum fun j _ => (ha i j).mul (contDiff_pd hu)).sub (hF i)
  have hT : ∫ x, T x = 0 := by
    apply integral_pd_mul_flux_eq_zero hG hφ hφc
    intro x hx
    have hxU : x ∈ U := hηU (subset_tsupport η (fun h => hx (by simp [φ,h])))
    simp only [G,pd_sub (ContDiff.sum fun j _ => (ha _ j).mul (contDiff_pd hu)) (hF _),
      Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hPDE x hxU)
  have hTsm : ContDiff ℝ ∞ T := ContDiff.sum fun i _ => (contDiff_pd hφ).mul (hG i)
  have hpd (i : (I d)) (x : (X d)) : pd i φ x =
      η x^2 * pd i u x + 2*η x*u x*pd i η x := by
    unfold φ
    rw [pd_mul (hη.pow 2) hu, show (fun z => η z^2) = fun z => η z*η z from funext fun z => pow_two _,
      pd_mul hη hη]
    ring
  have hAint : Integrable A := integrable_of_eta_factor hηc
    ((hη.pow 2).mul (ContDiff.sum fun _ _ => (contDiff_pd hu).pow 2)) (fun x hx => by simp [A,hx])
  have hBint : IntegrableOn B L :=
    ((hu.pow 2).add (ContDiff.sum fun i _ => (hF i).pow 2)).continuous.continuousOn.integrableOn_compact hηc
  have hTint : Integrable T := integrable_of_eta_factor hηc hTsm (fun x hx => by
    unfold T
    simp [hpd,hx])
  have hpoint (x : (X d)) : (lam/2) * A x ≤ L.indicator (fun x => C * B x) x + T x := by
    by_cases hx : x ∈ L
    · rw [indicator_of_mem hx]
      have hma (i j : (I d)) : |a i j x| ≤ M :=
        (hMat x (hηU hx) i j).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hmb (i : (I d)) : |pd i η x| ≤ M :=
        ((by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (fun i : (I d) => pd i η x) i :
          |pd i η x| ≤ _).trans (hMb x hx)).trans ((le_max_right _ _).trans (le_max_left _ _))
      have hme : |η x| ≤ M := ((by simpa only [Real.norm_eq_abs] using hMe x hx : |η x| ≤ Me)).trans
        ((le_max_left _ _).trans (le_max_right _ _))
      have hw := flux_energy_integrand_le (fun i j => a i j x) (fun i => pd i u x)
        (fun i => pd i η x) (fun i => F i x) (η x) (u x) lam M hlam hM hma hmb hme
        (hell x (hηU hx) (fun i => pd i u x))
      have hi : Cᵤ*u x^2 + CF*(∑ i, F i x^2) ≤ C*B x := by
        unfold B
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      simp only [T,hpd,G] at ⊢
      exact hw.trans (add_le_add_left hi _)
    · have h0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [indicator_of_notMem hx,A,T,hpd,h0]
  have hIB : Integrable (L.indicator (fun x => C * B x)) :=
    (integrable_indicator_iff hηc.isClosed.measurableSet).2 (hBint.const_mul _)
  have hInt := integral_mono (hAint.const_mul (lam/2)) (hIB.add hTint) hpoint
  simp only [Pi.add_apply] at hInt
  rw [integral_const_mul,integral_add hIB hTint,hT,add_zero,
    integral_indicator hηc.isClosed.measurableSet,integral_const_mul] at hInt
  have hAK : (∫ x in K, ∑ i, pd i u x^2) ≤ ∫ x, A x := by
    have h1 : (∫ x in K, ∑ i, pd i u x^2) = ∫ x in K, A x := by
      apply setIntegral_congr_fun hK.isClosed.measurableSet
      intro x hx
      have he : η x = 1 := (hηK x hx).eq_of_nhds
      simp [A,he]
    rw [h1]
    exact setIntegral_le_integral hAint (Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  refine hAK.trans ?_
  calc
    _ ≤ (C * ∫ x in L, B x)/(lam/2) := (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hInt)
    _ = _ := by ring


omit [NeZero d] in
private theorem wordFluxTerms_numeric_shape {a : I d → I d → X d → ℝ}
    (w : List (I d)) (j : I d)
    (t : FluxTerm d) (ht : t ∈ wordFluxTerms a w j) :
    ∃ k : I d, ∃ r : List (I d), r.length ≤ w.length ∧
      t.1 = (fun x => -wordDeriv r (a j k) x) := by
  induction w generalizing t with
  | nil => simp [wordFluxTerms] at ht
  | cons i w ih =>
    simp only [wordFluxTerms,List.mem_append] at ht
    rcases ht with ht | ht
    · rw [differentiateTerms,List.mem_flatMap] at ht
      obtain ⟨v,hv,ht⟩ := ht
      obtain ⟨k,r,hr,he⟩ := ih v hv
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · refine ⟨k,i :: r,Nat.succ_le_succ hr,?_⟩
        change pd i v.1 = _
        rw [he]
        exact funext (pd_neg (i := i) (f := wordDeriv r (a j k)))
      · exact ⟨k,r,hr.trans (Nat.le_succ _),he⟩
    · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ht
      exact ⟨k,[i],Nat.succ_le_succ (Nat.zero_le _),rfl⟩

omit [NeZero d] in
private theorem wordFluxTerms_numeric_length (a : I d → I d → X d → ℝ)
    (w : List (I d)) (j : I d) :
    (wordFluxTerms a w j).length = (Nat.rec 0 (fun _ count => count * 2 + d) w.length) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hl (T : List (FluxTerm d)) : (differentiateTerms i T).length = T.length * 2 := by
      induction T with
      | nil => rfl
      | cons t T h =>
        rw [differentiateTerms,List.flatMap_cons,List.length_append]
        change 2 + (differentiateTerms i T).length = (T.length + 1) * 2
        rw [h]
        omega
    simp [wordFluxTerms, coefficientDerivativeTerms, hl, ih]

private def evalTermsBudget (Ma : ℝ) : ℕ → ℝ
  | 0 => 0
  | k+1 => 2 * (Ma^2 + evalTermsBudget Ma k)

private theorem evalTermsBudget_nonneg (Ma : ℝ) (k : ℕ) : 0 ≤ evalTermsBudget Ma k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => simp only [evalTermsBudget]; positivity

omit [NeZero d] in
private theorem evalTerms_energy_numeric {L : Set (X d)} (hL : IsCompact L)
    (T : List (FluxTerm d)) (k : ℕ) (Ma : ℝ)
    (hT : ∀ t ∈ T, ContDiff ℝ ∞ t.1 ∧ t.2.length ≤ k ∧ ∀ x ∈ L, |t.1 x| ≤ Ma)
    {u : X d → ℝ} {E : ℝ} (hu : ContDiff ℝ ∞ u)
    (hE : ∀ w : List (I d), w.length ≤ k → (∫ x in L, wordDeriv w u x ^ 2) ≤ E) :
    (∫ x in L, evalTerms T u x ^ 2) ≤ evalTermsBudget Ma T.length * E := by
  induction T with
  | nil => simp [evalTerms,evalTermsBudget]
  | cons t T ih =>
    have ht := hT t List.mem_cons_self
    have hT' (v : FluxTerm d) (hv : v ∈ T) := hT v (List.mem_cons_of_mem _ hv)
    let g (x : X d) := wordDeriv t.2 u x
    let f (x : X d) := t.1 x * g x
    let v := evalTerms T u
    have hg : ContDiff ℝ ∞ g := contDiff_wordDeriv t.2 hu
    have hf : ContDiff ℝ ∞ f := ht.1.mul hg
    have hv : ContDiff ℝ ∞ v := contDiff_evalTerms T (fun t ht => (hT' t ht).1) hu
    have hI (z : X d → ℝ) (hz : ContDiff ℝ ∞ z) :
        IntegrableOn (fun x => z x^2) L :=
      (hz.continuous.pow 2).continuousOn.integrableOn_compact hL
    have hFSq : (∫ x in L, f x^2) ≤ Ma^2*E := by
      have hpoint : ∀ᵐ x ∂(volume : Measure (X d)).restrict L, f x^2 ≤ Ma^2*g x^2 :=
        (ae_restrict_mem hL.isClosed.measurableSet).mono (fun x hx => by
          have hb := pow_le_pow_left₀ (abs_nonneg _) (ht.2.2 x hx) 2
          rw [sq_abs] at hb
          rw [show f x = t.1 x * g x from rfl,mul_pow]
          exact mul_le_mul_of_nonneg_right hb (sq_nonneg _))
      refine (integral_mono_ae (hI f hf) ((hI g hg).const_mul _) hpoint).trans ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hE t.2 ht.2.1) (sq_nonneg _)
    have hpt : ∀ x : X d, evalTerms (t :: T) u x ^ 2 ≤ 2*(f x^2+v x^2) := by
      intro x
      change (f x+v x)^2 ≤ _
      nlinarith only [sq_nonneg (f x-v x)]
    have h := integral_mono (hI (evalTerms (t :: T) u) (hf.add hv))
      (((hI f hf).add (hI v hv)).const_mul 2) hpt
    simp only [Pi.add_apply] at h
    rw [integral_const_mul,integral_add (hI f hf) (hI v hv)] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add hFSq (ih hT')) (by norm_num)).trans_eq
      (by simp only [List.length_cons,evalTermsBudget]; ring))

omit [NeZero d] in
/-- The differentiated release flux, bounded only by a finite coefficient budget. -/
theorem exists_wordFlux_energy_constant_numeric {L : Set (X d)} (hL : IsCompact L)
    (w : List (I d)) (j : I d) (Ma : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : I d → I d → X d → ℝ, (∀ i j, ContDiff ℝ ∞ (a i j)) →
      HasWordBudget a L Ma w.length →
      ∀ (u : X d → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ v : List (I d), v.length ≤ w.length → (∫ x in L, wordDeriv v u x ^ 2) ≤ E) →
      (∫ x in L, wordFlux a w u j x ^ 2) ≤ C * E := by
  let count : ℕ := Nat.rec 0 (fun _ count => count * 2 + d) w.length
  refine ⟨evalTermsBudget Ma count,evalTermsBudget_nonneg Ma count,fun a ha hWord u E hu hE => ?_⟩
  have hTerms (t : FluxTerm d) (ht : t ∈ wordFluxTerms a w j) :
      ContDiff ℝ ∞ t.1 ∧ t.2.length ≤ w.length ∧ ∀ x ∈ L, |t.1 x| ≤ Ma := by
    obtain ⟨htsm,htlen⟩ := wordFluxTerms_property ha w j t ht
    obtain ⟨k,r,hr,he⟩ := wordFluxTerms_numeric_shape w j t ht
    exact ⟨htsm,htlen,fun x hx => by simpa only [he,abs_neg] using hWord x hx j k r hr⟩
  simpa only [wordFlux,wordFluxTerms_numeric_length] using
    evalTerms_energy_numeric hL _ w.length Ma hTerms hu hE


/-- Finite order squared interior estimate with constants fixed by the
ellipticity and coefficient budgets. The word induction follows
`exists_interior_word_energy_bound_family` from the release. -/
theorem exists_interior_word_energy_bound_numeric {U : Set (X d)} (hU : IsOpen U)
    {lam Ma : ℝ} (hlam : 0 < lam)
    (n : ℕ) {K : Set (X d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : I d → I d → X d → ℝ, (∀ i j, ContDiff ℝ ∞ (a i j)) →
      HasEllipticityFloor a U lam → HasWordBudget a U Ma n →
      ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop a u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ w : List (I d), w.length ≤ n →
        (∫ x in K, wordDeriv w u x ^ 2) ≤ C*(∫ x in U, u x^2) := by
  induction n generalizing K with
  | zero =>
    refine ⟨1,zero_le_one,fun _ _ _ _ u _ _ hInt w hw => ?_⟩
    have hz : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    rw [hz,wordDeriv,one_mul]
    exact setIntegral_mono_set hInt (ae_of_all _ fun x => sq_nonneg (u x)) hKU.eventuallyLE
  | succ n ih =>
    obtain ⟨L,hL,hLU,C₀,hC₀,hstep⟩ := exists_interior_flux_energy_bound_numeric hU hK hKU (Ma := Ma) hlam
    obtain ⟨A,hA,hprev⟩ := ih hL hLU
    choose B hB hF using (fun (w : List (I d)) (j : (I d)) => exists_wordFlux_energy_constant_numeric hL w j Ma)
    let S := ∑ w ∈ wordsThrough n, ∑ j : (I d), B w j
    have hS : 0 ≤ S := Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun j _ => hB w j
    refine ⟨max 1 (C₀*((1+S)*A)),zero_le_one.trans (le_max_left _ _),fun a ha hell hMaN u hu hPDE hInt w hw => ?_⟩
    let E := ∫ x in U, u x^2
    have hE : 0 ≤ E := integral_nonneg fun x => sq_nonneg (u x)
    cases w with
    | nil =>
      rw [wordDeriv]
      exact (setIntegral_mono_set hInt (ae_of_all _ fun x => sq_nonneg (u x)) hKU.eventuallyLE).trans
        (le_mul_of_one_le_left hE (le_max_left _ _))
    | cons i w =>
      have hw' : w.length ≤ n := Nat.le_of_succ_le_succ hw
      have hUword := contDiff_wordDeriv w hu
      have hFw (j : (I d)) := contDiff_wordFlux ha w hu j
      have hEq := lop_wordDeriv_eq_div_wordFlux hU ha hu hPDE w
      have hbound (v : List (I d)) (hv : v.length ≤ w.length) :
          (∫ x in L, wordDeriv v u x^2) ≤ A*E :=
        hprev a ha hell (fun x hx i j w hw => hMaN x hx i j w (hw.trans (Nat.le_succ _)))
          u hu hPDE hInt v (hv.trans hw')
      have hS₁ : ∑ j : (I d), B w j ≤ S :=
        Finset.single_le_sum (f := fun v => ∑ j : (I d), B v j)
          (fun v _ => Finset.sum_nonneg fun j _ => hB v j) ((mem_wordsThrough n w).mpr hw')
      have hIntU (j : (I d)) : IntegrableOn (fun x => pd j (wordDeriv w u) x ^ 2) K :=
        ((contDiff_pd hUword).continuous.pow 2).continuousOn.integrableOn_compact hK
      have hIntF (j : (I d)) : IntegrableOn (fun x => wordFlux a w u j x ^ 2) L :=
        ((hFw j).continuous.pow 2).continuousOn.integrableOn_compact hL
      have hIntW : IntegrableOn (fun x => wordDeriv w u x^2) L :=
        (hUword.continuous.pow 2).continuousOn.integrableOn_compact hL
      have hSumF : (∫ x in L, ∑ j, wordFlux a w u j x ^ 2) ≤ S*(A*E) := by
        rw [integral_finsetSum _ (fun j _ => hIntF j)]
        calc
          _ ≤ ∑ j : (I d), B w j*(A*E) :=
            Finset.sum_le_sum (fun j _ => hF w j a ha
              (fun x hx i j v hv => hMaN x (hLU hx) i j v ((hv.trans hw').trans (Nat.le_succ _)))
              u (A*E) hu hbound)
          _ = (∑ j : (I d), B w j)*(A*E) := (Finset.sum_mul ..).symm
          _ ≤ S*(A*E) := mul_le_mul_of_nonneg_right hS₁ (mul_nonneg hA hE)
      have hLbound : (∫ x in L, (wordDeriv w u x ^ 2 + ∑ j, wordFlux a w u j x ^ 2)) ≤ (1+S)*A*E := by
        rw [integral_add hIntW (integrable_finsetSum _ (fun j _ => hIntF j))]
        exact (add_le_add (hbound w le_rfl) hSumF).trans_eq (by ring)
      have hI : (∫ x in K, pd i (wordDeriv w u) x^2) ≤ ∫ x in K, ∑ j, pd j (wordDeriv w u) x^2 := by
        apply integral_mono (hIntU i) (integrable_finsetSum _ (fun j _ => hIntU j))
        exact fun x => Finset.single_le_sum (f := fun j => pd j (wordDeriv w u) x^2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [wordDeriv]
      exact hI.trans ((hstep a ha (fun x hx i j => hMaN x hx i j [] (Nat.zero_le _)) hell _ _ hUword hFw hEq).trans
        ((mul_le_mul_of_nonneg_left hLbound hC₀).trans
          (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hE)))


/-- Pointwise finite order jet estimates with explicit numerical
coefficient budgets, using the release's compact point evaluation. -/
theorem exists_interior_word_point_bound_numeric {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {lam Ma : ℝ} (hlam : 0 < lam) (w : List (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : I d → I d → X d → ℝ, (∀ i j, ContDiff ℝ ∞ (a i j)) →
      HasEllipticityFloor a U lam → HasWordBudget a U Ma ((fullCoordinateWord d ++ w).length) →
      ∀ (u : (X d) → ℝ), ContDiff ℝ ∞ u →
      (∀ x ∈ U, Lop a u x = 0) → IntegrableOn (fun x => u x ^ 2) U →
      ∀ x ∈ K, |wordDeriv w u x| ≤ C * Real.sqrt (∫ y in U, u y^2) := by
  obtain ⟨χ,hχ,hχc,hχU,hχK⟩ := exists_plateau_cutoff hU hK hKU
  let L := tsupport χ
  let v := (fullCoordinateWord d) ++ w
  obtain ⟨A,hA,hbound⟩ := exists_interior_word_energy_bound_numeric hU (Ma := Ma) hlam v.length hχc hχU
  obtain ⟨B,hB,hcut⟩ := exists_cutoff_word_energy_constant hχc hχ v
  let M := Real.sqrt ((volume : Measure (X d)).real L)
  refine ⟨M*Real.sqrt (B*A),by positivity,fun a ha hell hbudget u hu hpde hint x hx => ?_⟩
  let z (y : (X d)) := χ y*u y
  let f := wordDeriv w z
  have hz : ContDiff ℝ ∞ z := hχ.mul hu
  have hL : tsupport z ⊆ L := tsupport_mul_subset_left
  have hfL := (tsupport_wordDeriv_subset w z).trans hL
  have hp := abs_apply_le_volume_sqrt_word (contDiff_wordDeriv w hz) hχc hfL x
  have hzEq : z =ᶠ[𝓝 x] u := (hχK x hx).mono (fun y hy => by simp [z,hy])
  have hfEq := (wordDeriv_congr_germ w hzEq).eq_of_nhds
  rw [hfEq] at hp
  have hJ := hcut u (A*(∫ y in U, u y^2)) hu (hbound a ha hell hbudget u hu hpde hint)
  rw [show v = fullCoordinateWord d ++ w from rfl, wordDeriv_append] at hJ
  change (∫ y in L, wordDeriv (fullCoordinateWord d) f y^2) ≤ _ at hJ
  calc
    _ ≤ _ := hp
    _ ≤ M * Real.sqrt (B * (A*(∫ y in U, u y^2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJ) (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc B A,Real.sqrt_mul (mul_nonneg hB hA)]; ring

end CalderonN.Elliptic

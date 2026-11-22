module

public import Proof.CalderonN.EllipticCalculus
public import Proof.CalderonN.JointCoefficientSmoothness
public import Proof.CalderonN.CompactEllipticity

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN.Elliptic

variable {d : ℕ} [NeZero d]



/-- A smooth function vanishing wherever the compactly supported `eta` vanishes is
integrable. -/
theorem integrable_of_eta_factor {eta f : (X d) → ℝ} (hetac : HasCompactSupport eta)
    (hf : ContDiff ℝ ∞ f) (h0 : ∀ x, eta x = 0 → f x = 0) : Integrable f :=
  integrable_of_contDiff_hasCompactSupport hf
    (hetac.mono fun z hz => fun he => hz (h0 z he))

/-- Testing a divergence-free flux against a compact smooth function. -/
theorem integral_pd_mul_flux_eq_zero {G : (I d) → (X d) → ℝ} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {φ : (X d) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hdiv : ∀ x, φ x ≠ 0 → ∑ i, pd i (G i) x = 0) :
    ∫ x, ∑ i, pd i φ x * G i x = 0 := by
  have hFc (i : (I d)) : HasCompactSupport (fun x => φ x * G i x) :=
    hφc.mono fun x hx hz => hx (by simp [hz])
  have hF (i : (I d)) : ContDiff ℝ ∞ (fun x => φ x * G i x) := hφ.mul (hG i)
  have hpt (x : (X d)) : ∑ i, pd i φ x * G i x = ∑ i, pd i (fun z => φ z * G i z) x := by
    simp only [pd_mul hφ (hG _), Finset.sum_add_distrib, ← Finset.mul_sum]
    by_cases h0 : φ x = 0
    · simp [h0]
    · simp [hdiv x h0]
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_of_contDiff_hasCompactSupport
    (contDiff_pd (hF i)) (hasCompactSupport_pd (hFc i))]
  exact Finset.sum_eq_zero fun i _ => integral_pd_eq_zero (hF i) (hFc i)

private theorem young_real (a b t : ℝ) (ht : 0 < t) :
    2*a*b ≤ t*a^2 + b^2/t := by
  have h := sq_nonneg (t*a-b)
  have h' : 2*a*b*t ≤ (t*a^2 + b^2/t)*t := by
    rw [add_mul,div_mul_cancel₀ _ ht.ne']
    nlinarith only [h]
  exact le_of_mul_le_mul_right h' ht

/-- A pointwise estimate for the energy of a scalar divergence equation
with a flux on the right. The constants use only the ellipticity floor
and bounds on the coefficients and the first cutoff derivative. -/
theorem flux_energy_integrand_le (a : (I d) → (I d) → ℝ) (p q F : (I d) → ℝ) (η u lam M : ℝ)
    (hlam : 0 < lam) (hM : 0 ≤ M)
    (ha : ∀ i j, |a i j| ≤ M) (hq : ∀ i, |q i| ≤ M) (hη : |η| ≤ M)
    (hell : lam * (∑ i, p i^2) ≤ ∑ i, ∑ j, p i*a i j*p j) :
    (lam/2) * (η^2 * ∑ i, p i^2) ≤
      (4*(d:ℝ)^3*M^4/lam+(d:ℝ)*M^2) * u^2 + (M^2/lam+M^2) * (∑ i, F i^2) +
        ∑ i, (η^2 * p i + 2*η*u*q i) * ((∑ j, a i j*p j)-F i) := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hηA : lam * (η^2 * ∑ i, p i^2) ≤ η^2 * ∑ i, ∑ j, p i*a i j*p j := by
    simpa only [mul_left_comm (η ^ 2)] using mul_le_mul_of_nonneg_left hell (sq_nonneg η)
  have h1 (i j : (I d)) : -(2*η*u*q i*a i j*p j) ≤ (lam/(4*(d:ℝ)))*(η*p j)^2+((4*(d:ℝ))*M^4/lam)*u^2 := by
    have h := young_real (η*p j) (-(u*q i*a i j)) (lam/(4*(d:ℝ))) (by positivity)
    have hab : |q i*a i j| ≤ M*M := by
      rw [abs_mul]
      exact mul_le_mul (hq i) (ha i j) (abs_nonneg _) hM
    have hb : (u*q i*a i j)^2 ≤ M^4*u^2 := by
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hab 2
      rw [sq_abs] at hsq
      calc
        _ = (q i*a i j)^2*u^2 := by ring
        _ ≤ (M*M)^2*u^2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        _ = _ := by ring
    calc
      _ = 2*(η*p j)*(-(u*q i*a i j)) := by ring
      _ ≤ (lam/(4*(d:ℝ)))*(η*p j)^2+(-(u*q i*a i j))^2/(lam/(4*(d:ℝ))) := h
      _ ≤ (lam/(4*(d:ℝ)))*(η*p j)^2 + (M^4*u^2)/(lam/(4*(d:ℝ))) := by
        rw [neg_sq]
        exact add_le_add_right (div_le_div_of_nonneg_right hb (show 0 ≤ lam/(4*(d:ℝ)) by positivity)) _
      _ = _ := by
        field_simp [hlam.ne', hd.ne']
  have h2 (i : (I d)) : η^2*p i*F i ≤ (lam/4)*(η*p i)^2+(M^2/lam)*F i^2 := by
    have h := young_real (η*p i) (η*F i/2) (lam/4) (by positivity)
    have hη' := pow_le_pow_left₀ (abs_nonneg _) hη 2
    rw [sq_abs] at hη'
    have hbound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hη' (sq_nonneg (F i))) hlam.le
    calc
      _ = 2*(η*p i)*(η*F i/2) := by ring
      _ ≤ (lam/4)*(η*p i)^2 + (η^2*F i^2)/lam := h.trans_eq (by ring)
      _ ≤ (lam/4)*(η*p i)^2 + (M^2*F i^2)/lam := add_le_add_right hbound _
      _ = _ := by ring
  have h3 (i : (I d)) : 2*η*u*q i*F i ≤ M^2*(u^2+F i^2) := by
    have hab : |η*q i| ≤ M^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hη (hq i) (abs_nonneg _) hM
    have hUF : 2 * |u*F i| ≤ u^2+F i^2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|u| - |F i|), sq_abs u, sq_abs (F i)]
    calc
      _ = 2*((η*q i)*(u*F i)) := by ring
      _ ≤ 2 * |(η*q i)*(u*F i)| := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = 2 * (|η*q i| * |u*F i|) := by rw [abs_mul]
      _ ≤ 2 * (M^2 * |u*F i|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (abs_nonneg _)) (by norm_num)
      _ = M^2 * (2 * |u*F i|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hUF (sq_nonneg M)
  have hs₁ := Finset.sum_le_sum (s := (Finset.univ : Finset (I d)))
    fun i _ => Finset.sum_le_sum (s := (Finset.univ : Finset (I d))) fun j _ => h1 i j
  have hs₂ := Finset.sum_le_sum (s := (Finset.univ : Finset (I d))) fun i _ => h2 i
  have hs₃ := Finset.sum_le_sum (s := (Finset.univ : Finset (I d))) fun i _ => h3 i
  have hc : (d : ℝ) * (lam / (4 * (d : ℝ))) = lam / 4 := by
    field_simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_pow, ← Finset.mul_sum] at hs₁ hs₂ hs₃
  rw [← mul_assoc, hc] at hs₁
  have htest :
      (∑ i, (η^2 * p i + 2*η*u*q i) * ((∑ j, a i j*p j)-F i)) =
        η^2 * (∑ i, ∑ j, p i*a i j*p j) -
          (∑ i, ∑ j, -(2*η*u*q i*a i j*p j)) -
          (∑ i, η^2*p i*F i) - (∑ i, 2*η*u*q i*F i) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_sub, add_mul _ _ (F i)]
    have hr : (∑ j, (η ^ 2 * p i + 2 * η * u * q i) * (a i j * p j)) =
        ∑ j, (η ^ 2 * (p i * a i j * p j) - -(2 * η * u * q i * a i j * p j)) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.mul_sum, hr]
    ring
  rw [htest]
  simp only [div_eq_mul_inv] at hηA hs₁ hs₂ hs₃ ⊢
  linear_combination hηA + hs₁ + hs₂ + hs₃

/-- Local inhomogeneous Caccioppoli on a compact parameter set. The outer
compact set and the constant are chosen before the parameter and the solution. -/
theorem exists_interior_flux_energy_bound_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : P → (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, Strict.JointSmooth (fun p => a p i j))
    (hpos : ∀ p ∈ J, ∀ x ∈ U, Matrix.PosDef (fun i j => a p i j x : (Mat d))) :
    ∃ L : Set (X d), IsCompact L ∧ L ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p ∈ J, ∀ (u : (X d) → ℝ) (F : (I d) → (X d) → ℝ), ContDiff ℝ ∞ u → (∀ i, ContDiff ℝ ∞ (F i)) →
        (∀ x ∈ U, Lop (a p) u x = ∑ i, pd i (F i) x) →
        (∫ x in K, ∑ i, pd i u x ^ 2) ≤ C * ∫ x in L, (u x^2 + ∑ i, F i x^2) := by
  obtain ⟨η,hη,hηc,hηU,hηK⟩ := exists_plateau_cutoff hU hK hKU
  let L := tsupport η
  obtain ⟨lam,hlam,hell⟩ := lower_ellipticity_on_compact
    (a := fun i j (q : P × (X d)) => a q.1 i j q.2)
    (fun i j => (ha i j).continuous) (hJ.prod hηc)
    (fun q hq => hpos q.1 hq.1 q.2 (hηU hq.2))
  obtain ⟨Ma,hMa⟩ := (hJ.prod hηc).exists_bound_of_continuousOn
    (f := fun q : P × (X d) => fun ij : (I d) × (I d) => a q.1 ij.1 ij.2 q.2)
    (continuous_pi (fun ij : (I d) × (I d) => (ha ij.1 ij.2).continuous)).continuousOn
  obtain ⟨Mb,hMb⟩ := hηc.exists_bound_of_continuousOn (f := fun x : (X d) => fun i : (I d) => pd i η x)
    (continuous_pi (fun _ => (contDiff_pd hη).continuous)).continuousOn
  obtain ⟨Me,hMe⟩ := hηc.exists_bound_of_continuousOn hη.continuous.continuousOn
  let M := max (max Ma Mb) (max Me 0)
  have hM : 0 ≤ M := (le_max_right Me 0).trans (le_max_right _ _)
  let Cᵤ := 4*(d:ℝ)^3*M^4/lam+(d:ℝ)*M^2
  let CF := M^2/lam+M^2
  let C := max Cᵤ CF
  have hC : 0 ≤ C := (by dsimp only [Cᵤ]; positivity : 0 ≤ Cᵤ).trans (le_max_left _ _)
  refine ⟨L,hηc,hηU,2*C/lam,by positivity,fun p hp u F hu hF hPDE => ?_⟩
  have hap (i j : (I d)) := Strict.jointSmooth_slice (ha i j) p
  let A (x : (X d)) := η x ^ 2 * ∑ i, pd i u x ^ 2
  let B (x : (X d)) := u x^2 + ∑ i, F i x^2
  let φ (x : (X d)) := η x^2 * u x
  let G (i : (I d)) (x : (X d)) := (∑ j, a p i j x * pd j u x) - F i x
  let T (x : (X d)) := ∑ i, pd i φ x * G i x
  have hφ : ContDiff ℝ ∞ φ := (hη.pow 2).mul hu
  have hφc : HasCompactSupport φ := hηc.mono fun x hx hz => hx (by simp [φ,hz])
  have hG (i : (I d)) : ContDiff ℝ ∞ (G i) :=
    (ContDiff.sum fun j _ => (hap i j).mul (contDiff_pd hu)).sub (hF i)
  have hT : ∫ x, T x = 0 := by
    apply integral_pd_mul_flux_eq_zero hG hφ hφc
    intro x hx
    have hxU : x ∈ U := hηU (subset_tsupport η (fun h => hx (by simp [φ,h])))
    simp only [G,pd_sub (ContDiff.sum fun j _ => (hap _ j).mul (contDiff_pd hu)) (hF _),
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
      have hma (i j : (I d)) : |a p i j x| ≤ M :=
        ((by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (fun ij : (I d) × (I d) => a p ij.1 ij.2 x) (i,j) : |a p i j x| ≤ _).trans
            (hMa (p,x) ⟨hp,hx⟩)).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hmb (i : (I d)) : |pd i η x| ≤ M :=
        ((by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (fun i : (I d) => pd i η x) i :
          |pd i η x| ≤ _).trans (hMb x hx)).trans ((le_max_right _ _).trans (le_max_left _ _))
      have hme : |η x| ≤ M := ((by simpa only [Real.norm_eq_abs] using hMe x hx : |η x| ≤ Me)).trans
        ((le_max_left _ _).trans (le_max_right _ _))
      have hw := flux_energy_integrand_le (fun i j => a p i j x) (fun i => pd i u x)
        (fun i => pd i η x) (fun i => F i x) (η x) (u x) lam M hlam hM hma hmb hme
        (hell (p,x) ⟨hp,hx⟩ (fun i => pd i u x))
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

/-- The same estimate for a single fixed coefficient. -/
theorem exists_interior_flux_energy_bound {U K : Set (X d)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : (I d) → (I d) → (X d) → ℝ) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hpos : ∀ x ∈ U, Matrix.PosDef (fun i j => a i j x : (Mat d))) :
    ∃ L : Set (X d), IsCompact L ∧ L ⊆ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : (X d) → ℝ) (F : (I d) → (X d) → ℝ), ContDiff ℝ ∞ u → (∀ i, ContDiff ℝ ∞ (F i)) →
        (∀ x ∈ U, Lop a u x = ∑ i, pd i (F i) x) →
        (∫ x in K, ∑ i, pd i u x ^ 2) ≤ C * ∫ x in L, (u x^2 + ∑ i, F i x^2) := by
  obtain ⟨L,hL,hLU,C,hC,h⟩ := exists_interior_flux_energy_bound_family
    (isCompact_singleton (x := (0:ℝ))) hU hK hKU (fun _ => a)
    (fun i j => (ha i j).comp contDiff_snd) (fun _ _ x hx => hpos x hx)
  exact ⟨L,hL,hLU,C,hC,h 0 (mem_singleton _)⟩

end CalderonN.Elliptic

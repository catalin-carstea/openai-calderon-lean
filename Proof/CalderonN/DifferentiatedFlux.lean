module

public import Proof.CalderonN.EllipticCalculus
public import Proof.CalderonN.CompactPointEvaluation
public import Proof.CalderonN.JointCoefficientSmoothness

import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace CalderonN.Elliptic

variable {d : ℕ}


theorem wordDeriv_congr_germ (w : List (I d)) {f g : (X d) → ℝ} {x : (X d)}
    (h : f =ᶠ[𝓝 x] g) : wordDeriv w f =ᶠ[𝓝 x] wordDeriv w g := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    exact ih.eventuallyEq_nhds.mono (fun _ hy => pd_congr_of_eventuallyEq hy i)

theorem wordDeriv_zero (w : List (I d)) : wordDeriv w (fun _ => 0) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordDeriv,ih]; exact funext (pd_const 0)

private abbrev FluxTerm (d : ℕ) := ((X d) → ℝ) × List (I d)

private def evalTerms (L : List (FluxTerm d)) (u : (X d) → ℝ) (x : (X d)) : ℝ :=
  (L.map fun t => t.1 x * wordDeriv t.2 u x).sum

private def differentiateTerms (i : (I d)) (L : List (FluxTerm d)) : List (FluxTerm d) :=
  L.flatMap fun t => [(pd i t.1,t.2), (t.1,i :: t.2)]

private theorem evalTerms_append (B C : List (FluxTerm d)) (u : (X d) → ℝ) :
    evalTerms (B ++ C) u = fun x => evalTerms B u x + evalTerms C u x := by
  funext x
  simp [evalTerms]

private theorem contDiff_evalTerms (L : List (FluxTerm d)) {u : (X d) → ℝ}
    (hL : ∀ t ∈ L, ContDiff ℝ ∞ t.1) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (evalTerms L u) := by
  induction L with
  | nil => exact contDiff_const
  | cons t L ih =>
    exact ((hL t List.mem_cons_self).mul (contDiff_wordDeriv t.2 hu)).add
      (ih (fun s hs => hL s (List.mem_cons_of_mem _ hs)))

private theorem pd_evalTerms (i : (I d)) (L : List (FluxTerm d)) {u : (X d) → ℝ}
    (hL : ∀ t ∈ L, ContDiff ℝ ∞ t.1) (hu : ContDiff ℝ ∞ u) :
    pd i (evalTerms L u) = evalTerms (differentiateTerms i L) u := by
  induction L with
  | nil => exact funext (pd_const 0)
  | cons t L ih =>
    have ht := hL t List.mem_cons_self
    have hLt : ∀ s ∈ L, ContDiff ℝ ∞ (s : (FluxTerm d)).1 := fun s hs => hL s (List.mem_cons_of_mem _ hs)
    have hd := ih hLt
    funext x
    change pd i (fun y => t.1 y * wordDeriv t.2 u y + evalTerms L u y) x = _
    rw [pd_add (ht.mul (contDiff_wordDeriv t.2 hu)) (contDiff_evalTerms L hLt hu),
      pd_mul ht (contDiff_wordDeriv t.2 hu), show ∀ x, pd i (evalTerms L u) x =
        evalTerms (differentiateTerms i L) u x from congrFun hd]
    simp [evalTerms,differentiateTerms,wordDeriv,add_assoc]

private def coefficientDerivativeTerms (a : (I d) → (I d) → (X d) → ℝ) (i j : (I d)) (w : List (I d)) :
    List (FluxTerm d) :=
  List.ofFn fun k : Fin d => (fun x => -pd i (a j k) x, k :: w)

private def wordFluxTerms (a : (I d) → (I d) → (X d) → ℝ) : List (I d) → (I d) → List (FluxTerm d)
  | [], _ => []
  | i :: w, j =>
      differentiateTerms i (wordFluxTerms a w j) ++ coefficientDerivativeTerms a i j w

private theorem wordFluxTerms_property {a : (I d) → (I d) → (X d) → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (w : List (I d)) (j : (I d))
    (t : (FluxTerm d)) (ht : t ∈ wordFluxTerms a w j) :
    ContDiff ℝ ∞ t.1 ∧ t.2.length ≤ w.length := by
  induction w generalizing t with
  | nil => simp [wordFluxTerms] at ht
  | cons i w ih =>
    simp only [wordFluxTerms,List.mem_append] at ht
    rcases ht with ht | ht
    · rw [differentiateTerms,List.mem_flatMap] at ht
      obtain ⟨s,hs,ht⟩ := ht
      have ⟨hs₁,hs₂⟩ := ih s hs
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact ⟨contDiff_pd hs₁,hs₂.trans (Nat.le_succ _)⟩
      · exact ⟨hs₁,Nat.succ_le_succ hs₂⟩
    · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ht
      exact ⟨(contDiff_pd (ha j k)).neg, le_rfl⟩

/-- The commutator flux of a word derivative only involves derivatives
of the solution of order at most the length of that word. -/
def wordFlux (a : (I d) → (I d) → (X d) → ℝ) (w : List (I d)) (u : (X d) → ℝ) (j : (I d)) : (X d) → ℝ :=
  evalTerms (wordFluxTerms a w j) u

theorem wordFlux_nil (a : (I d) → (I d) → (X d) → ℝ) (u : (X d) → ℝ) (j : (I d)) : wordFlux a [] u j = 0 := by funext x; rfl

theorem contDiff_wordFlux {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (w : List (I d)) {u : (X d) → ℝ} (hu : ContDiff ℝ ∞ u) (j : (I d)) :
    ContDiff ℝ ∞ (wordFlux a w u j) :=
  contDiff_evalTerms _ (fun t ht => (wordFluxTerms_property ha w j t ht).1) hu

private theorem wordFlux_cons {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (w : List (I d)) {u : (X d) → ℝ} (hu : ContDiff ℝ ∞ u) (i j : (I d)) :
    wordFlux a (i :: w) u j = fun x => pd i (wordFlux a w u j) x -
      ∑ k, pd i (a j k) x * pd k (wordDeriv w u) x := by
  unfold wordFlux
  rw [wordFluxTerms,evalTerms_append,← pd_evalTerms i _ (fun t ht => (wordFluxTerms_property ha w j t ht).1) hu]
  funext x
  simp only [evalTerms, coefficientDerivativeTerms, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, wordDeriv, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

private def correctedFlux (a : (I d) → (I d) → (X d) → ℝ) (w : List (I d)) (u : (X d) → ℝ) (j : (I d)) : (X d) → ℝ :=
  fun x => (∑ k, a j k x * pd k (wordDeriv w u) x) - wordFlux a w u j x

private theorem contDiff_correctedFlux {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (w : List (I d)) {u : (X d) → ℝ} (hu : ContDiff ℝ ∞ u) (j : (I d)) :
    ContDiff ℝ ∞ (correctedFlux a w u j) :=
  (ContDiff.sum fun k _ => (ha j k).mul (contDiff_pd (contDiff_wordDeriv w hu))).sub
    (contDiff_wordFlux ha w hu j)

private theorem correctedFlux_cons {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (w : List (I d)) {u : (X d) → ℝ} (hu : ContDiff ℝ ∞ u) (i j : (I d)) :
    correctedFlux a (i :: w) u j = pd i (correctedFlux a w u j) := by
  funext x
  let f := wordDeriv w u
  have hf := contDiff_wordDeriv w hu
  unfold correctedFlux
  simp only [wordFlux_cons ha w hu,wordDeriv]
  rw [pd_sub (f := fun y => ∑ k, a j k y * pd k f y)
    (ContDiff.sum fun k _ => (ha j k).mul (contDiff_pd hf)) (contDiff_wordFlux ha w hu j),
    pd_sum (fun k => (ha j k).mul (contDiff_pd hf))]
  simp only [pd_mul (ha _ _) (contDiff_pd hf), pd_comm (i := i) hf, Finset.sum_add_distrib]
  ring

/-- Differentiating the divergence equation gives an exact equation
for the word derivative with the explicitly constructed flux. -/
theorem lop_wordDeriv_eq_div_wordFlux {U : Set (X d)} (hU : IsOpen U)
    {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) {u : (X d) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hPDE : ∀ x ∈ U, Lop a u x = 0) (w : List (I d)) :
    ∀ x ∈ U, Lop a (wordDeriv w u) x = ∑ j, pd j (wordFlux a w u j) x := by
  have h (w : List (I d)) : ∀ x ∈ U, ∑ j, pd j (correctedFlux a w u j) x = 0 := by
    induction w with
    | nil =>
      intro x hx
      have hz (j : (I d)) : correctedFlux a [] u j = fun x => ∑ k, a j k x * pd k u x := by
        funext y
        simp [correctedFlux,wordFlux_nil,wordDeriv]
      simp only [hz]
      exact hPDE x hx
    | cons i w ih =>
      intro x hx
      simp only [correctedFlux_cons ha w hu, pd_comm (i := _) (j := i) (contDiff_correctedFlux ha w hu _)]
      rw [← pd_sum (fun j => contDiff_pd (i := j) (contDiff_correctedFlux ha w hu j))]
      have he : (fun y => ∑ j, pd j (correctedFlux a w u j) y) =ᶠ[𝓝 x] fun _ => 0 :=
        Filter.eventually_of_mem (hU.mem_nhds hx) ih
      rw [pd_congr_of_eventuallyEq he, pd_const]
  intro x hx
  have he := h w x hx
  have hxj (j : (I d)) : pd j (correctedFlux a w u j) x =
      pd j (fun y => ∑ k, a j k y * pd k (wordDeriv w u) y) x - pd j (wordFlux a w u j) x := by
    unfold correctedFlux
    exact pd_sub (ContDiff.sum fun k _ => (ha j k).mul (contDiff_pd (contDiff_wordDeriv w hu)))
      (contDiff_wordFlux ha w hu j) x
  simp only [hxj,Finset.sum_sub_distrib] at he
  exact sub_eq_zero.mp he

private theorem exists_evalTerms_energy_constant_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {L : Set (X d)} (hL : IsCompact L)
    (T : List ((P → (X d) → ℝ) × List (I d)))
    (hT : ∀ t ∈ T, Strict.JointSmooth t.1) (k : ℕ) (hk : ∀ t ∈ T, t.2.length ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (u : (X d) → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ w : List (I d), w.length ≤ k → (∫ x in L, wordDeriv w u x ^ 2) ≤ E) →
      (∫ x in L, evalTerms (T.map (fun t => (t.1 p,t.2))) u x ^ 2) ≤ C*E := by
  induction T with
  | nil => exact ⟨0,le_rfl,fun _ _ _ _ _ _ => by simp [evalTerms]⟩
  | cons t T ih =>
    have ht := hT t List.mem_cons_self
    have hT' (v : (P → (X d) → ℝ) × List (I d)) (hv : v ∈ T) :=
      hT v (List.mem_cons_of_mem _ hv)
    obtain ⟨B,hB,hBound⟩ := ih hT' (fun v hv => hk v (List.mem_cons_of_mem _ hv))
    obtain ⟨M,hM⟩ := (hJ.prod hL).exists_bound_of_continuousOn ht.continuous.continuousOn
    refine ⟨2*(M^2+B),by positivity,fun p hp u E hu hE => ?_⟩
    let T' := T.map (fun t => (t.1 p,t.2))
    have hT's (d : (FluxTerm d)) (hd : d ∈ T') : ContDiff ℝ ∞ d.1 := by
      obtain ⟨t',ht',rfl⟩ := List.mem_map.mp hd
      exact Strict.jointSmooth_slice (hT' t' ht') p
    have hts := Strict.jointSmooth_slice ht p
    let g (x : (X d)) := wordDeriv t.2 u x
    let f (x : (X d)) := t.1 p x * g x
    let v := evalTerms T' u
    have hfg : ContDiff ℝ ∞ g := contDiff_wordDeriv t.2 hu
    have hf : ContDiff ℝ ∞ f := hts.mul hfg
    have hv : ContDiff ℝ ∞ v := contDiff_evalTerms T' hT's hu
    have hI (z : (X d) → ℝ) (hz : ContDiff ℝ ∞ z) :
        IntegrableOn (fun x => z x^2) L :=
      (hz.continuous.pow 2).continuousOn.integrableOn_compact hL
    have hFSq : (∫ x in L, f x^2) ≤ M^2*E := by
      have hpoint : ∀ᵐ x ∂(volume : Measure (X d)).restrict L, f x^2 ≤ M^2*g x^2 :=
        (ae_restrict_mem hL.isClosed.measurableSet).mono (fun x hx => by
          have hb : |t.1 p x| ≤ |M| := by
            have h := (hM (p,x) ⟨hp,hx⟩).trans (le_abs_self _)
            simpa only [Real.norm_eq_abs] using h
          have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
          simp only [sq_abs] at h
          rw [show f x = t.1 p x * g x from rfl,mul_pow]
          exact mul_le_mul_of_nonneg_right h (sq_nonneg _))
      refine (integral_mono_ae (hI f hf) ((hI g hfg).const_mul _) hpoint).trans ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hE t.2 (hk t List.mem_cons_self)) (sq_nonneg _)
    have hVSq : (∫ x in L, v x^2) ≤ B*E := hBound p hp u E hu hE
    have hpt : ∀ x : (X d), evalTerms ((t.1 p,t.2) :: T') u x ^ 2 ≤ 2*(f x^2+v x^2) := by
      intro x
      change (f x+v x)^2 ≤ _
      nlinarith only [sq_nonneg (f x-v x)]
    have h := integral_mono (hI (evalTerms ((t.1 p,t.2) :: T') u) ((hf.add hv)))
      (((hI f hf).add (hI v hv)).const_mul 2) hpt
    simp only [Pi.add_apply] at h
    rw [integral_const_mul,integral_add (hI f hf) (hI v hv)] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (add_le_add hFSq hVSq) (by norm_num)).trans_eq (by ring))

private theorem exists_evalTerms_energy_constant {L : Set (X d)} (hL : IsCompact L) (T : List (FluxTerm d))
    (hT : ∀ t ∈ T, ContDiff ℝ ∞ t.1) (k : ℕ) (hk : ∀ t ∈ T, t.2.length ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (X d) → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ w : List (I d), w.length ≤ k → (∫ x in L, wordDeriv w u x ^ 2) ≤ E) →
      (∫ x in L, evalTerms T u x ^ 2) ≤ C*E := by
  let U := T.map (fun t => ((fun _ : ℝ => t.1),t.2))
  have hU (t : (ℝ → (X d) → ℝ) × List (I d)) (ht : t ∈ U) : Strict.JointSmooth t.1 := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
    exact (hT r hr).comp contDiff_snd
  have hU' (t : (ℝ → (X d) → ℝ) × List (I d)) (ht : t ∈ U) : t.2.length ≤ k := by
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ht
    exact hk r hr
  obtain ⟨C,hC,h⟩ := exists_evalTerms_energy_constant_family
    (isCompact_singleton (x := (0:ℝ))) hL U hU k hU'
  have he : U.map (fun t => (t.1 0,t.2)) = T := by simp [U,List.map_map,Function.comp_def]
  refine ⟨C,hC,fun u E hu hE => ?_⟩
  simpa only [he] using h 0 (mem_singleton _) u E hu hE

private theorem exists_family_wordFluxTerms
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a : P → (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, Strict.JointSmooth (fun p => a p i j))
    (w : List (I d)) (j : (I d)) :
    ∃ T : List ((P → (X d) → ℝ) × List (I d)),
      (∀ t ∈ T, Strict.JointSmooth t.1 ∧ t.2.length ≤ w.length) ∧
      ∀ p, T.map (fun t => (t.1 p,t.2)) = wordFluxTerms (a p) w j := by
  induction w with
  | nil => exact ⟨[],by simp,fun _ => rfl⟩
  | cons i w ih =>
    obtain ⟨U,hU,hU'⟩ := ih
    let f (t : (P → (X d) → ℝ) × List (I d)) :=
      [((fun p => pd i (t.1 p)),t.2), (t.1,i :: t.2)]
    let V : List ((P → (X d) → ℝ) × List (I d)) :=
      List.ofFn fun k : Fin d => (fun p x => -pd i (a p j k) x, k :: w)
    refine ⟨U.flatMap f ++ V,?_,?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨s,hs,ht⟩ := List.mem_flatMap.mp ht
        have hS := hU s hs
        simp only [f,List.mem_cons,List.not_mem_nil,or_false] at ht
        rcases ht with rfl | rfl
        · exact ⟨Strict.jointSmooth_pd hS.1 i,hS.2.trans (by simp)⟩
        · exact ⟨hS.1,Nat.succ_le_succ hS.2⟩
      · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ht
        exact ⟨(Strict.jointSmooth_pd (ha j k) i).neg, le_rfl⟩
    · intro p
      have hmap : (U.flatMap f).map (fun t => (t.1 p,t.2)) =
          differentiateTerms i (U.map (fun t => (t.1 p,t.2))) := by
        clear hU hU'
        induction U with
        | nil => rfl
        | cons a U ih =>
          simp only [List.flatMap_cons,List.map_append,List.map_cons]
          change [_,_] ++ (U.flatMap f).map (fun t => (t.1 p,t.2)) =
            [_,_] ++ differentiateTerms i (U.map (fun t => (t.1 p,t.2)))
          rw [ih]
      rw [List.map_append,hmap,hU',wordFluxTerms]
      simp only [V, coefficientDerivativeTerms, List.map_ofFn, Function.comp_def]

/-- The differentiated flux estimate with one coefficient bound that
works on an entire compact parameter set. -/
theorem exists_wordFlux_energy_constant_family
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {J : Set P} (hJ : IsCompact J) {L : Set (X d)} (hL : IsCompact L)
    {a : P → (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, Strict.JointSmooth (fun p => a p i j))
    (w : List (I d)) (j : (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ J, ∀ (u : (X d) → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ v : List (I d), v.length ≤ w.length → (∫ x in L, wordDeriv v u x ^ 2) ≤ E) →
      (∫ x in L, wordFlux (a p) w u j x ^ 2) ≤ C*E := by
  obtain ⟨T,hT,hT'⟩ := exists_family_wordFluxTerms ha w j
  obtain ⟨C,hC,h⟩ := exists_evalTerms_energy_constant_family hJ hL T
    (fun t ht => (hT t ht).1) w.length (fun t ht => (hT t ht).2)
  exact ⟨C,hC,fun p hp u E hu hE => by
    simpa only [hT' p,wordFlux] using h p hp u E hu hE⟩

/-- On a fixed compact room, the squared norm of the commutator flux
is controlled by the squared norms through the corresponding order. -/
theorem exists_wordFlux_energy_constant {L : Set (X d)} (hL : IsCompact L)
    {a : (I d) → (I d) → (X d) → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (w : List (I d)) (j : (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (X d) → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ v : List (I d), v.length ≤ w.length → (∫ x in L, wordDeriv v u x ^ 2) ≤ E) →
      (∫ x in L, wordFlux a w u j x ^ 2) ≤ C*E :=
  exists_evalTerms_energy_constant hL _ (fun t ht => (wordFluxTerms_property ha w j t ht).1)
    w.length (fun t ht => (wordFluxTerms_property ha w j t ht).2)

private def productWordTerms (χ : (X d) → ℝ) : List (I d) → List (FluxTerm d)
  | [] => [(χ, [])]
  | i :: w => differentiateTerms i (productWordTerms χ w)

private theorem productWordTerms_property {χ : (X d) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (w : List (I d)) (t : (FluxTerm d)) (ht : t ∈ productWordTerms χ w) :
    ContDiff ℝ ∞ t.1 ∧ t.2.length ≤ w.length := by
  induction w generalizing t with
  | nil =>
    simp only [productWordTerms,List.mem_singleton] at ht
    subst t
    exact ⟨hχ,le_rfl⟩
  | cons i w ih =>
    rw [productWordTerms,differentiateTerms,List.mem_flatMap] at ht
    obtain ⟨s,hs,ht⟩ := ht
    have ⟨hs₁,hs₂⟩ := ih s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨contDiff_pd hs₁,hs₂.trans (Nat.le_succ _)⟩
    · exact ⟨hs₁,Nat.succ_le_succ hs₂⟩

private theorem wordDeriv_product_eq_terms {χ u : (X d) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hu : ContDiff ℝ ∞ u) (w : List (I d)) :
    wordDeriv w (fun x => χ x*u x) = evalTerms (productWordTerms χ w) u := by
  induction w with
  | nil => funext x; simp [wordDeriv,evalTerms,productWordTerms]
  | cons i w ih =>
    rw [wordDeriv, ih, productWordTerms]
    change pd i (evalTerms (productWordTerms χ w) u) = _
    rw [pd_evalTerms i _ (fun t ht => (productWordTerms_property hχ w t ht).1) hu]

/-- A fixed cutoff costs derivatives only through the same order,
with coefficients bounded on the compact room. -/
theorem exists_cutoff_word_energy_constant {L : Set (X d)} (hL : IsCompact L)
    {χ : (X d) → ℝ} (hχ : ContDiff ℝ ∞ χ) (w : List (I d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (X d) → ℝ) (E : ℝ), ContDiff ℝ ∞ u →
      (∀ v : List (I d), v.length ≤ w.length → (∫ x in L, wordDeriv v u x ^ 2) ≤ E) →
      (∫ x in L, wordDeriv w (fun y => χ y*u y) x ^ 2) ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := exists_evalTerms_energy_constant hL (productWordTerms χ w)
    (fun t ht => (productWordTerms_property hχ w t ht).1)
    w.length (fun t ht => (productWordTerms_property hχ w t ht).2)
  exact ⟨C,hC,fun u E hu hE => by rw [wordDeriv_product_eq_terms hχ hu]; exact hbound u E hu hE⟩

end CalderonN.Elliptic

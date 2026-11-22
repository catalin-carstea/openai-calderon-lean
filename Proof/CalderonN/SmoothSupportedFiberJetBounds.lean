module

public import Proof.CalderonN.SmoothSupportedFiberHigherDerivatives
public import Proof.CalderonN.SmoothSupportedFiberDerivativeCalculus
public import Proof.CalderonN.SmoothTraceAngularOrder

import Mathlib.Tactic

/-! Bounds on the base derivatives of regular angular coefficient
families, with the usual product and sum estimates. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

namespace RegularTraceFiberFamily

@[expose] def add (F G : RegularTraceFiberFamily Y) : RegularTraceFiberFamily Y :=
  ⟨fun x => F.1 x+G.1 x,F.2.add G.2⟩

@[expose] def sub (F G : RegularTraceFiberFamily Y) : RegularTraceFiberFamily Y :=
  ⟨fun x => F.1 x-G.1 x,F.2.sub G.2⟩

@[expose] def mul (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y) : RegularTraceFiberFamily Y :=
  ⟨fun x => F.1 x*G.1 x,F.2.mul hY G.2⟩

theorem iteratedDerivative_congrOn (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y)
    {U : Set (X dim)} (hU : IsOpen U) (hUY : U ⊆ Y) (hFG : EqOn F.1 G.1 U)
    (n : ℕ) (a : Fin n → X dim) :
    EqOn (F.iteratedDerivative hY n a).1 (G.iteratedDerivative hY n a).1 U := by
  induction n with
  | zero => exact hFG
  | succ n ih =>
    intro x hx
    have hh : (F.iteratedDerivative hY n (Fin.tail a)).1 =ᶠ[𝓝 x]
        (G.iteratedDerivative hY n (Fin.tail a)).1 :=
      by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih (Fin.tail a) hy
    exact smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY
      (F.iteratedDerivative hY n (Fin.tail a)).2 (G.iteratedDerivative hY n (Fin.tail a)).2
      (a 0) (hUY hx) hh

theorem iteratedDerivative_add (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y)
    (n : ℕ) (a : Fin n → X dim) :
    EqOn ((F.add G).iteratedDerivative hY n a).1
      ((F.iteratedDerivative hY n a).add (G.iteratedDerivative hY n a)).1 Y := by
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
    intro x hx
    let H := (F.add G).iteratedDerivative hY n (Fin.tail a)
    let F' := F.iteratedDerivative hY n (Fin.tail a)
    let G' := G.iteratedDerivative hY n (Fin.tail a)
    have hEq : H.1 =ᶠ[𝓝 x] (F'.add G').1 := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact ih (Fin.tail a) hy
    change smoothSupportedTraceFiberDerivative hY H.1 H.2 (a 0) x = _
    rw [smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY H.2 (F'.add G').2 (a 0) hx hEq]
    exact smoothSupportedTraceFiberDerivative_add hY F'.1 G'.1 F'.2 G'.2 (a 0) hx

theorem iteratedDerivative_sub (hY : IsOpen Y) (F G : RegularTraceFiberFamily Y)
    (n : ℕ) (a : Fin n → X dim) :
    EqOn ((F.sub G).iteratedDerivative hY n a).1
      ((F.iteratedDerivative hY n a).sub (G.iteratedDerivative hY n a)).1 Y := by
  induction n with
  | zero => intro x hx; rfl
  | succ n ih =>
    intro x hx
    let H := (F.sub G).iteratedDerivative hY n (Fin.tail a)
    let F' := F.iteratedDerivative hY n (Fin.tail a)
    let G' := G.iteratedDerivative hY n (Fin.tail a)
    have hEq : H.1 =ᶠ[𝓝 x] (F'.sub G').1 := by
      filter_upwards [hY.mem_nhds hx] with y hy
      exact ih (Fin.tail a) hy
    change smoothSupportedTraceFiberDerivative hY H.1 H.2 (a 0) x = _
    rw [smoothSupportedTraceFiberDerivative_eq_of_eventuallyEq hY H.2 (F'.sub G').2 (a 0) hx hEq]
    exact smoothSupportedTraceFiberDerivative_sub hY F'.1 G'.1 F'.2 G'.2 (a 0) hx

theorem iteratedDerivative_snoc (hY : IsOpen Y) (F : RegularTraceFiberFamily Y)
    (n : ℕ) (a : Fin n → X dim) (b : X dim) :
    F.iteratedDerivative hY (n+1) (Fin.snoc (α := fun _ => X dim) a b) = (F.derivative hY b).iteratedDerivative hY n a := by
  induction n with
  | zero =>
    simp only [iteratedDerivative, show (0:Fin (0+1)) = Fin.last 0 by rfl,Fin.snoc_last]
  | succ n ih =>
    have ha : Fin.tail (Fin.snoc (α := fun _ => X dim) a b) = Fin.snoc (α := fun _ => X dim) (Fin.tail a) b := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change Fin.snoc (α := fun _ => X dim) a b (Fin.succ (Fin.last n)) = Fin.snoc (α := fun _ => X dim) (Fin.tail a) b (Fin.last n)
        rw [show (Fin.last n).succ = Fin.last (n+1) by rfl,Fin.snoc_last,Fin.snoc_last]
      · change Fin.snoc (α := fun _ => X dim) a b j.castSucc.succ = Fin.snoc (α := fun _ => X dim) (Fin.tail a) b j.castSucc
        rw [show j.castSucc.succ = j.succ.castSucc by rfl,Fin.snoc_castSucc,Fin.snoc_castSucc]
        rfl
    change (F.iteratedDerivative hY (n+1) (Fin.tail (Fin.snoc (α := fun _ => X dim) a b))).derivative hY (Fin.snoc (α := fun _ => X dim) a b 0) =
      ((F.derivative hY b).iteratedDerivative hY n (Fin.tail a)).derivative hY (a 0)
    rw [ha,ih (Fin.tail a),show (0:Fin (n+2)) = (0:Fin (n+1)).castSucc by rfl,Fin.snoc_castSucc]

end RegularTraceFiberFamily

@[expose] def SmoothSupportedFiberJetBound (hn : 3 ≤ dim) (hY : IsOpen Y) (x : X dim)
    (β : ℝ) (N k : ℕ) (C : ℝ) (F : RegularTraceFiberFamily Y) : Prop :=
  ∀ n ≤ N,∀ a : Fin n → X dim,(∀ i,‖a i‖ ≤ 1) →
    SmoothTraceAngularBound hn k (C*β^n) ((F.iteratedDerivative hY n a).1 x)

namespace SmoothSupportedFiberJetBound

variable {hn : 3 ≤ dim} {hY : IsOpen Y} {x : X dim} {β C D : ℝ} {N k l : ℕ}
variable {F G : RegularTraceFiberFamily Y}

theorem restrict (h : SmoothSupportedFiberJetBound hn hY x β N k C F) {M : ℕ} (hMN : M ≤ N) :
    SmoothSupportedFiberJetBound hn hY x β M k C F :=
  fun n hnN a ha => h n (hnN.trans hMN) a ha

theorem enlarge (h : SmoothSupportedFiberJetBound hn hY x β N k C F) (hβ : 0 ≤ β) (hCD : C ≤ D) :
    SmoothSupportedFiberJetBound hn hY x β N k D F :=
  fun n hnN a ha => (h n hnN a ha).enlarge (mul_le_mul_of_nonneg_right hCD (pow_nonneg hβ n))

theorem congrOn (h : SmoothSupportedFiberJetBound hn hY x β N k C F)
    {U : Set (X dim)} (hU : IsOpen U) (hUY : U ⊆ Y) (hFG : EqOn F.1 G.1 U) (hx : x ∈ U) :
    SmoothSupportedFiberJetBound hn hY x β N k C G := by
  intro n hnN a ha
  rw [← F.iteratedDerivative_congrOn hY G hU hUY hFG n a hx]
  exact h n hnN a ha

theorem add (hx : x ∈ Y) (hF : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hG : SmoothSupportedFiberJetBound hn hY x β N k D G) :
    SmoothSupportedFiberJetBound hn hY x β N k (C+D) (F.add G) := by
  intro n hnN a ha
  rw [F.iteratedDerivative_add hY G n a hx,add_mul]
  exact (hF n hnN a ha).add (hG n hnN a ha)

theorem sub (hx : x ∈ Y) (hF : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hG : SmoothSupportedFiberJetBound hn hY x β N k D G) :
    SmoothSupportedFiberJetBound hn hY x β N k (C+D) (F.sub G) := by
  intro n hnN a ha
  rw [F.iteratedDerivative_sub hY G n a hx,add_mul]
  exact (hF n hnN a ha).sub (hG n hnN a ha)

theorem derivative (h : SmoothSupportedFiberJetBound hn hY x β (N+1) k C F)
    (b : X dim) (hb : ‖b‖ ≤ 1) :
    SmoothSupportedFiberJetBound hn hY x β N k (C*β) (F.derivative hY b) := by
  intro n hnN a ha
  rw [← F.iteratedDerivative_snoc hY n a b]
  have hh (i : Fin (n+1)) : ‖Fin.snoc (α := fun _ => X dim) a b i‖ ≤ 1 := by
    refine Fin.lastCases (motive:=fun j => ‖Fin.snoc (α := fun _ => X dim) a b j‖ ≤ 1) ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]
      exact hb
    · rw [Fin.snoc_castSucc]
      exact ha j
  have hb₀ := h (n+1) (Nat.succ_le_succ hnN) (Fin.snoc (α := fun _ => X dim) a b) hh
  rw [show (C*β)*β^n = C*β^(n+1) by rw [pow_succ]; ring]
  exact hb₀

theorem mul (hx : x ∈ Y) (hβ : 0 ≤ β) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hF : SmoothSupportedFiberJetBound hn hY x β N k C F)
    (hG : SmoothSupportedFiberJetBound hn hY x β N l D G) :
    SmoothSupportedFiberJetBound hn hY x β N (k+l) ((2:ℝ)^N*(C*D)) (F.mul hY G) := by
  induction N generalizing F G C D with
  | zero =>
    intro n hnN a ha
    have hn₀ : n = 0 := by omega
    subst n
    simpa only [pow_zero,one_mul,mul_one,RegularTraceFiberFamily.iteratedDerivative,RegularTraceFiberFamily.mul] using
      (hF 0 le_rfl a ha).mul (hG 0 le_rfl a ha) (by simpa only [pow_zero,mul_one] using hC)
  | succ N ih =>
    intro n hnN a ha
    cases n with
    | zero =>
      have hFa := hF 0 (Nat.zero_le _) a ha
      have hGa := hG 0 (Nat.zero_le _) a ha
      have h := hFa.mul hGa (by simpa only [pow_zero,mul_one] using hC)
      apply h.enlarge
      simp only [pow_zero,mul_one]
      exact le_mul_of_one_le_left (mul_nonneg hC hD) (one_le_pow₀ (by norm_num))
    | succ n =>
      let b := a (Fin.last n)
      let F' := F.derivative hY b
      let G' := G.derivative hY b
      let W := (F'.mul hY G).add (F.mul hY G')
      have hW : EqOn W.1 ((F.mul hY G).derivative hY b).1 Y := by
        intro y hy
        exact (smoothSupportedTraceFiberDerivative_mul hY F.1 G.1 F.2 G.2 b hy).symm
      have hb := ha (Fin.last n)
      have h' := (ih (mul_nonneg hC hβ) hD (hF.derivative b hb)
          (hG.restrict (Nat.le_succ N))).add hx
        (ih hC (mul_nonneg hD hβ) (hF.restrict (Nat.le_succ N)) (hG.derivative b hb))
      have h := (h'.congrOn hY Subset.rfl hW hx) n (by omega) (Fin.init a) (fun i => ha i.castSucc)
      have ha' : Fin.snoc (α := fun _ => X dim) (Fin.init a) b = a := Fin.snoc_init_self _
      rw [← ha',RegularTraceFiberFamily.iteratedDerivative_snoc]
      convert h using 1
      ring

end SmoothSupportedFiberJetBound

end CalderonN

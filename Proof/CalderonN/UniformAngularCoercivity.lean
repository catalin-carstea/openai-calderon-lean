module

public import Proof.CalderonN.UniformComplexCoercivity
public import Proof.CalderonN.FiniteAngularOutputs

import Mathlib.Tactic

@[expose] public section

noncomputable section
set_option autoImplicit false
open Set MvPolynomial
open scoped ContDiff
namespace CalderonN
variable {n : ℕ} [NeZero n]
open OAI.AnisotropicCalderon.AngularPolynomial

variable {α : Type*} {ι : α → Type*} [∀ i,Fintype (ι i)]

/-- Uniform coercivity for every compact finite complex angular field, with the actual
    four-term frozen energy and actual raising/lowering output squares. The constant and
    profile floor are independent of the finite angular support and the admissible radius. -/
theorem Background.energySq_finite_angular_coercive (hn : 3 ≤ n) {Y Ω : Set (X n)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    (hsub : Y ⊆ Ω) {K : ℝ} (hK : 0 < K) {m : ℕ} (hm : 2 ≤ m) {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : (MetricField n)} {e : (Frame n)} (hbg : Background Ω K M g g₁ g₂ e)
    {r : (X n) → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hc₀ : 0 < c₀) (hfloor : backgroundCoercivityFloor n hm K M c₀ ≤ floor)
    (s : Finset α) (index : α → ℕ) (hinj : Set.InjOn index (s : Set α))
    (b : (i : α) → ι i → MvPolynomial (I n) ℝ) (hb : ∀ i ∈ s,∀ t,(b i t).IsHomogeneous (index i+1))
    (hΔ : ∀ i ∈ s,∀ t,laplacian (b i t) = 0) (c d : (i : α) → (X n) → ι i → ℝ)
    (hc : ∀ i ∈ s,ContDiff ℝ ∞ (c i)) (hd : ∀ i ∈ s,ContDiff ℝ ∞ (d i))
    (hcompactc : ∀ i ∈ s,HasCompactSupport (c i)) (hcompactd : ∀ i ∈ s,HasCompactSupport (d i))
    (hsuppc : ∀ i ∈ s,tsupport (c i) ⊆ Y) (hsuppd : ∀ i ∈ s,tsupport (d i) ⊆ Y) :
    backgroundModeCoercivityConstant c₀ * energySq Y g e r (finiteAngularField g e s b c d) ≤
      outputSq Y g e (finiteRaisedField g e s index b c d (fun x => Real.log (r x))) -
        outputSq Y g e (finiteLoweredField g e s index b c d (fun x => Real.log (r x))) := by
  have hE : Elliptic Y K g := ⟨fun i j => (hbg.1.1 i j).mono hsub,fun y hy => hbg.1.2 y (hsub hy)⟩
  have he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y := fun i => (hbg.2.2.2.2.2.2.1 i).mono hsub
  have hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0 :=
    fun y hy => hbg.2.2.2.2.2.2.2 y (hsub hy)
  have hf : 1 ≤ floor := (backgroundCoercivityFloor_ge_one n hm K M c₀).trans hfloor
  have hlog := hp.1.log (fun y hy => (hp.2 y hy).1.ne')
  have hpos (i : α) (_hi : i ∈ s) : 1 ≤ index i+1 := by omega
  have hinj' : Set.InjOn (fun i => index i+1) (s : Set α) := by
    intro i hi j hj hd
    apply hinj hi hj
    change index i+1 = index j+1 at hd
    omega
  rw [hp.energySq_finiteAngularField hn hY hE hK e he hframe hf s (fun i => index i+1) hpos hinj'
    b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd,
    outputSq_finiteRaisedField hY hE hK e he hframe s index hinj b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd _ hlog,
    outputSq_finiteLoweredField hY hE hK e he hframe s index hinj b hb hΔ c d hc hd hcompactc hcompactd hsuppc hsuppd _ hlog,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact hbg.energySq_complex_finite_mode_coercive hn hY hΩ hsub hK hm hp hc₀ hfloor (index i) (b i) (hb i hi) (hΔ i hi)
    (c i) (d i) (hc i hi) (hd i hi) (hcompactc i hi) (hcompactd i hi) (hsuppc i hi) (hsuppd i hi)

end CalderonN

import Mathlib
import Runge.Basic
import Runge.GridContour
import Runge.SeparationLemma

/-!
# Approximation Lemma (WIP)

This file contains the statement of the **Approximation Lemma**, which is a key result in complex analysis and rational approximation. The lemma provides a way to approximate a holomorphic function on a compact set `K` in the complex plane using rational functions with poles restricted to a specific set.

## Main Results

- `approximation_lemma`: Given a holomorphic function `f` on an open set `Ω` containing a compact set `K`, and a positive resolution `δ`, there exists a rational function `R` with poles only on the grid contour boundary of `K` such that `R` approximates `f` uniformly on `K` within any given error `ε > 0`.

- `approximation_lemma'`: A refinement of the approximation lemma, which allows transferring the poles of a rational function `R` from the grid contour boundary to another set `E` while maintaining a uniform approximation on `K`.

## Notation

- `GridContourBoundary`: The boundary of the grid contour.
- `only_poles_in'`: A predicate indicating that a rational function has poles only in a specified set.
-/

open Complex Set Finset Metric RatFunc Real

/-
Parametrize Grid_Contour, γ : [0,1] → GridContourBoundary (Γ)
γ is a continuous function on a compact set → γ is uniformly continuous and bounded(?)
· IsCompact.uniformContinuousOn_of_continuous
· IsCompact.exists_bound_of_continuousOn' (But maybe we don't need boundedness...)
f is Holomorphic on Ω → f is Holomorphic on Γ  → f ∘ γ is uniformly continuous and bounded

Fix a ∈ K, then ∀ s, t ∈ [0,1], ‖(f ∘ γ s / (γ s - a)) - (f ∘ γ s / (γ s - a))‖ is continuous
So now whatever choose η such that whenever |s-t| < η, ‖(f ∘ γ s / (γ s - a)) - (f ∘ γ s / (γ s - a))‖ < ε / Nδ
Partition [0,1] into M > 1/η parts... Then we have Finset P = {0, s₁, s₂, ..., 1}

 R z = ∑ f∘γ(s_j-1)*(γ(s_J)-γ(s_j-1))/ (γ(s_j-1)-z)
 · RatFunc.coe_add
 Prove that z is a pole iff z ∈ γ P

 ‖f - R‖ < ε
-/

variable (K: Set ℂ) [Gridable K] {δ : ℝ} (hδ : 0 < δ) (f : ℂ → ℂ)

--*GET HELP*
def GridContourParametrization : ℝ → ℂ := by
  let Γ := GridContourBoundary K hδ
  let N := (GridContourCollection K hδ).card
  -- z + δ(Ny - m)
  sorry

lemma grid_contour_param_eq : GridContourParametrization K hδ ''(Icc 0 1) = GridContourBoundary K hδ := by
  apply subset_antisymm
  · intro x hx
    simp only [Set.mem_image, Set.mem_Icc] at hx
    rcases hx with ⟨y, hy₁, hy₂⟩
    -- hy₁ → ∃ m ≤ N, m/δ ≤ y ≤ (m+1)/δ
    -- hy₂ → z + δ(Ny - m) = x
    -- ⊢ z ≤ x ≤ z + δ' ; where δ' = δ or I * δ

    sorry

  · intro x hx
    simp only [Set.mem_image, Set.mem_Icc]
    sorry

lemma grid_contour_continuous : ContinuousOn (GridContourParametrization K hδ) (Icc 0 1) := by
  intro x hx

  sorry

--Is Typeclass better? Typeclass is most likely better...
-- def ComplexCurve (γ : ℝ → ℂ) (hγ : ContinuousOn γ (Icc 0 1)) := γ
class ComplexCurve (γ : ℝ → ℂ) where
  hγ : ContinuousOn γ (Icc 0 1)

instance grid_contour_param_isComplexCurve : ComplexCurve (GridContourParametrization K hδ) := by
  constructor
  exact grid_contour_continuous K hδ

lemma complex_curve_unif_cont (γ : ℝ → ℂ) [ComplexCurve γ] : UniformContinuousOn γ (Icc 0 1) := by
  exact IsCompact.uniformContinuousOn_of_continuous isCompact_Icc ComplexCurve.hγ


lemma DifferentiableOn.complex_curve_unif_cont {Ω : Set ℂ} {f : ℂ → ℂ} (γ : ℝ → ℂ) (hΩ : (γ ''(Icc 0 1)) ⊆ Ω) (hf : DifferentiableOn ℂ f Ω) [ComplexCurve γ] : UniformContinuousOn (f ∘ γ) (Icc 0 1) := by
  apply IsCompact.uniformContinuousOn_of_continuous isCompact_Icc
  apply ContinuousOn.comp _ _ (by rw [Set.mapsTo'])
  · exact DifferentiableOn.continuousOn (DifferentiableOn.mono hf hΩ)
  · exact ComplexCurve.hγ

--*GET HELP*
-- Construction of R : RatFunc ℂ

theorem approximation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ ε > 0, ∃ (R : RatFunc ℂ), (only_poles_in' (GridContourBoundary K hδ) R) ∧
  (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by
  intro ε hε
  -- rcases `lemma` with ⟨R, hR⟩
  obtain (R : RatFunc ℂ) := by sorry
  have hR : only_poles_in' (coe_set (GridContourBoundary K hδ)) R := by sorry

  use R
  constructor
  · exact hR
  · intro x hx
    have hε' : 0 < ε / 2 := by positivity
    have : ((2 * Real.pi * I)⁻¹ * GridContourIntegral K hε' fun x_1 ↦ (x_1 - x)⁻¹ * f x_1) = f x := DifferentiableOn.inv_two_pi_grid_contour_integral hε' hΩ hΩK hf x hx
    rw [← this]
    sorry

/-*GET HELP*
Define B(E) = {continuous functions | they can be approximated by RatFunc with only_poles_in E}
Membership lemma for B(E), maybe it works out from definition
Show that B(E) is a closed subalgebra
Show that ∀ a ∈ ↑Kᶜ, (Ra := fun z ↦ 1 / (z - a)) ∈ B(E)
Closed subalgebra → R ∈ B(E)
-/

theorem approximation_lemma' {Ω K : Set ℂ} {δ : ℝ} {R : RatFunc ℂ} {E : Set (OnePoint ℂ)} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ)  (hE : ∀ z ∈  (↑K)ᶜ, connectedComponentIn (↑K)ᶜ z ∩ E ≠ ∅)
  (hR : only_poles_in' (GridContourBoundary K hδ) R):
  ∀ ε > 0, ∃ (R' : RatFunc ℂ), (only_poles_in' E R') ∧
  (∀ x ∈ K, ‖ R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ < ε) := by

  intro ε hε
  -- rcases `another_lemma` with ⟨R', hR'⟩
  obtain (R' : RatFunc ℂ) := by sorry
  have hR' : only_poles_in' E R' := by sorry

  use R'
  constructor
  · exact hR'
  · intro x hx
    -- Need defn of `B(E)` and `mem_iff` to resolve this
    sorry

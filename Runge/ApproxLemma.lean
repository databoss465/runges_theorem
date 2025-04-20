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

open Complex Set Finset Metric RatFunc

-- Needs work! Either state in terms of integral or use separation lemma in the proof! Better the first.
theorem approximation_lemma {Ω K : Set ℂ} {f : ℂ → ℂ} {δ : ℝ} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
  ∀ ε > 0, ∃ (R : RatFunc ℂ), (only_poles_in' (GridContourBoundary K hδ) R) ∧
  (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by sorry

theorem approximation_lemma' {Ω K : Set ℂ} {δ : ℝ} {R : RatFunc ℂ} {E : Set (OnePoint ℂ)} (hΩ : IsOpen Ω)
  (hΩK : K ⊆ Ω) [Gridable K] (hδ : 0 < δ)  (hE : ∀ z ∈  (↑K)ᶜ, connectedComponentIn (↑K)ᶜ z ∩ E ≠ ∅)
  (hR : only_poles_in' (GridContourBoundary K hδ) R):
  ∀ ε > 0, ∃ (R' : RatFunc ℂ), (only_poles_in' E R') ∧
  (∀ x ∈ K, ‖ R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ < ε) := by sorry

-- This module serves as the root of the `Runge` library.
-- Import modules here that should be built as part of the library.
import Mathlib
import Runge.Basic
import Runge.GridContour
import Runge.SeparationLemma
import Runge.ApproxLemma

/-!
# Runge's Theorem (WIP)

This file contains the proof of **Runge's Theorem**, a fundamental result in complex analysis. The theorem states that
any holomorphic function on a compact set `K` in the complex plane can be uniformly approximated by rational functions
with specified poles.

## Main Result

- `runges_theorem`: Given an open set `Ω` in the complex plane, a compact subset `K ⊆ Ω`, and a set `E` intersecting every connected component of `ℂ_infty \ K`, any holomorphic function `f` on `Ω` can be uniformly approximated on `K` by rational functions with poles in `E`.

## Proof Outline

The proof of Runge's Theorem relies on two key lemmas:

1. **Separation Lemma**:
   - This lemma ensures that the grid contour of `K` can be constructed such that it lies in betweeen `K` and `Ω`. It also provides a way to compute the integral of a holomorphic function over the grid contour.

2. **Approximation Lemma**:
   - Using the grid contour, this lemma allows us to approximate a holomorphic function `f` on `K` by a rational function `R` with poles restricted to the grid contour boundary. The approximation is uniform on `K` within any given error `ε > 0`.

### Steps in the Proof

1. **Grid Contour Construction**:
   - Using the Separation Lemma, we construct a grid contour around `K` that lies in `Ω \ K`.

2. **Initial Approximation**:
   - Using the Approximation Lemma, we approximate the holomorphic function `f` on `K` by a rational function `R` with poles on the grid contour boundary.

3. **Pole Transfer**:
   -We then show that `R` itself can be approximated by rational functions with poles in `E`.

## References

This proof is based on the exposition in *Functions of One Complex Variable, Volume 1* by John B. Conway.

-/

/-- **Runge's Theorem**
Suppose `Ω` is an open set in ℂ, `K` is a compact subset and `E` is set which intersects every connected component of `ℂ_infty \ K`. If `f` is a function which is complex differentiable on `Ω`, then for every `ε > 0` there exists a rational function `R` such that `∀ x ∈ Ω, |f(x) - R(x)| < ε`.

theorem runges_theorem {Ω K : Set ℂ} [Gridable K] {E : Set (OnePoint ℂ)} {f : ℂ → ℂ} (hΩ : IsOpen Ω ∧ Ωᶜ.Nonempty)
    (hΩK : K ⊆ Ω)
    (hE : ∀ z ∈  (↑K)ᶜ, connectedComponentIn (↑K)ᶜ z ∩ E ≠ ∅) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
    ∀ ε > 0, ∃ R : RatFunc ℂ, (only_poles_in' E R) ∧ (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by sorry-/

theorem runges_theorem {Ω K : Set ℂ} [Gridable K] {E : Set (OnePoint ℂ)} {f : ℂ → ℂ} (hΩ : IsOpen Ω ∧ Ωᶜ.Nonempty)
    (hΩK : K ⊆ Ω) (hE : ∀ z ∈  (↑K)ᶜ, connectedComponentIn (↑K)ᶜ z ∩ E ≠ ∅) (hf : ∀ x ∈ Ω, DifferentiableAt ℂ f x) :
    ∀ ε > 0, ∃ R : RatFunc ℂ, (only_poles_in' E R) ∧ (∀ x ∈ K, ‖f x - R.eval (RingHom.id ℂ) x‖ < ε) := by

    intro ε hε
    have hε' : ε / 2 > 0 := by positivity

    rcases approximation_lemma hΩ.1 hΩK hε' hf (ε / 2) hε' with ⟨R, hR⟩

    rcases approximation_lemma' hΩ.1 hΩK hε' hE hR.1 (ε / 2) hε'  with ⟨R', hR'⟩

    use R'
    constructor
    · exact hR'.1
    · intro x hx
      calc
        ‖f x - RatFunc.eval (RingHom.id ℂ) x R'‖ = ‖f x - R.eval (RingHom.id ℂ) x + R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ := by rw [←sub_add_sub_cancel (f x) (R.eval (RingHom.id ℂ) x) (R'.eval (RingHom.id ℂ) x), ←add_sub_assoc]
        _ ≤ ‖f x - R.eval (RingHom.id ℂ) x‖ + ‖R.eval (RingHom.id ℂ) x - R'.eval (RingHom.id ℂ) x‖ := by rw [add_sub_assoc]; apply norm_add_le
        _ < ε / 2 + ε / 2 := by apply add_lt_add (hR.2 x hx) (hR'.2 x hx)
        _ = ε := by ring

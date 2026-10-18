/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# Van der Waerden's theorem, finite form

Mathlib proves the Hales–Jewett theorem and derives from it
`Combinatorics.exists_mono_homothetic_copy`, the infinitary form of van der Waerden's theorem.
This file records the finitary form with an explicit window: for every `k` and every finite
type of colours `κ` there is an `N` such that every colouring `C : ℕ → κ` has a monochromatic
`k`-term arithmetic progression with positive common difference inside `[1, N]`.

The proof is the standard one: colour the cube `ι → Fin k` by the digit sum `1 + ∑ i, v i` and
read off a monochromatic combinatorial line as an arithmetic progression whose difference is
the number of moving coordinates.
-/

@[expose] public section

open Finset

namespace Combinatorics

/-- **Van der Waerden's theorem** (finite form). For every `k` and every finite type `κ` there
is `N` such that any colouring `C : ℕ → κ` contains a monochromatic `k`-term arithmetic
progression `a, a + d, …, a + (k - 1) * d` with `0 < d`, `1 ≤ a` and `a + (k - 1) * d ≤ N`. -/
theorem exists_mono_arithmeticProgression (k : ℕ) (κ : Type*) [Finite κ] :
    ∃ N : ℕ, ∀ C : ℕ → κ, ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + (k - 1) * d ≤ N ∧
      ∃ c : κ, ∀ i < k, C (a + i * d) = c := by
  classical
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) κ
  refine ⟨1 + Fintype.card ι * (k - 1), fun C => ?_⟩
  obtain ⟨l, c, hl⟩ := hι fun v => C (1 + ∑ i, (v i : ℕ))
  set s : Finset ι := {i | l.idxFun i = none} with hs
  have hval (x : Fin k) :
      ∑ i, (l x i : ℕ) = ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0 + #s * x := by
    rw [← Finset.sum_add_sum_compl s, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
      simp [← hy]
    · refine Finset.sum_const_nat fun i hi => ?_
      rw [hs, Finset.mem_filter] at hi
      rw [l.apply_none _ _ hi.right]
  have hterm (i : ι) : ((l.idxFun i).map Fin.val).getD 0 ≤ k - 1 := by
    cases h : l.idxFun i with
    | none => simp
    | some y => have := y.isLt; simp; omega
  have hcard : #sᶜ + #s = Fintype.card ι := by rw [add_comm, Finset.card_add_card_compl]
  refine ⟨1 + ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0, #s, by omega,
    Finset.card_pos.mpr ⟨l.proper.choose, ?_⟩, ?_, c, fun i hi => ?_⟩
  · rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
  · calc 1 + ∑ i ∈ sᶜ, ((l.idxFun i).map Fin.val).getD 0 + (k - 1) * #s
        ≤ 1 + ∑ _i ∈ sᶜ, (k - 1) + (k - 1) * #s :=
          Nat.add_le_add_right (Nat.add_le_add_left (Finset.sum_le_sum fun i _ => hterm i) 1) _
      _ = 1 + Fintype.card ι * (k - 1) := by
          rw [Finset.sum_const_nat fun _ _ => rfl, ← hcard]; ring
  · have h := hl ⟨i, hi⟩
    simp only [hval] at h
    convert h using 2
    ring

end Combinatorics

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
import SizeRamseyOfTwoPrescribedStarForests

namespace JSP452Audit.StarHost
open SimpleGraph

local notation "F(" s ", " n ")" =>
  fromRel (fun (u v : Σ i : Fin s, Fin (n i + 1)) ↦
    Sigma.fst u = Sigma.fst v ∧
      (Fin.val (Sigma.snd u) = 0 ∨ Fin.val (Sigma.snd v) = 0))

/-- JSP-000452. Statement from google-deepmind/formal-conjectures at
2783e6edc3b2c80b5844978f74c3b325df8d82f5, ErdosProblems/561.lean.
Mathematical solution by Peilin Liu (P. Liu), Zenodo v3, DOI 10.5281/zenodo.23879458. -/
theorem erdos_561 :
    ∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ),
      Antitone n → Antitone m → (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
      sizeRamsey F(s, n) F(t, m) =
        ∑ k ∈ Finset.Icc 2 (s + t),
          ((Finset.univ : Finset (Fin s × Fin t)).filter
            (fun p ↦ (p.1.val + 1) + (p.2.val + 1) = k)).sup
              (fun p ↦ n p.1 + m p.2 - 1) := by
  exact sizeRamsey_star_forests

#print axioms erdos_561
end JSP452Audit.StarHost

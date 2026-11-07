import OriginalUpper

namespace JSP452Claim
open SimpleGraph JSP452Audit.StarHost

local notation "F(" s ", " n ")" =>
  fromRel (fun (u v : Σ i : Fin s, Fin (n i + 1)) ↦
    Sigma.fst u = Sigma.fst v ∧
      (Fin.val (Sigma.snd u) = 0 ∨ Fin.val (Sigma.snd v) = 0))

def ReferenceStatement : Prop :=
    ∀ (s t : ℕ), 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ),
      Antitone n → Antitone m → (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
      sizeRamsey F(s, n) F(t, m) =
        ∑ k ∈ Finset.Icc 2 (s + t),
          ((Finset.univ : Finset (Fin s × Fin t)).filter
            (fun p ↦ (p.1.val + 1) + (p.2.val + 1) = k)).sup
              (fun p ↦ n p.1 + m p.2 - 1)

def ProjectStatement : Prop :=
  ∀ (s t : ℕ), 1≤s → 1≤t →
    ∀ (n : Fin s→ℕ) (m : Fin t→ℕ), Antitone n → Antitone m →
    (∀i,1≤n i) → (∀j,1≤m j) →
    sizeRamsey (forest n) (forest m)=∑k∈Finset.Icc 2 (s+t),diagonal n m k

/-- Definitional equality of the propositions; this checks the target type only. -/
theorem statement_alignment : ReferenceStatement ↔ ProjectStatement := Iff.rfl

#print axioms statement_alignment
end JSP452Claim

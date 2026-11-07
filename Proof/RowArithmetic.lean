import SuffixRows

namespace JSP452Audit.StarHost

variable {X : Type*} (G : SimpleGraph X) (v : X) {s t : ℕ} (n m : ℕ → ℕ)

/-- Apply the one-component deletion rule to every legal pair on the next row.
    Window lengths are explicit so no empty-target descent is accidentally used. -/
theorem rowStep_of_starDeletion {r : ℕ} (row : ForcingRow G s t n m r)
    (red : ∀ i j l q, i+l+1 = s → j+q = t →
      Forces G (suffixStars n i (l+1)) (suffixStars m j q) →
      Forces (G.induce {x | x ≠ v}) (suffixStars n (i+1) l) (suffixStars m j q))
    (blue : ∀ i j l q, i+l = s → j+q+1 = t →
      Forces G (suffixStars n i l) (suffixStars m j (q+1)) →
      Forces (G.induce {x | x ≠ v}) (suffixStars n i l) (suffixStars m (j+1) q)) :
    ForcingRow (G.induce {x | x ≠ v}) s t n m (r+1) := by
  intro i j l q hr hl hq posL posQ
  cases i with
  | succ i =>
    exact red i j l q (by omega) hq
      (row i j (l+1) q (by omega) (by omega) hq (by omega) posQ)
  | zero =>
    cases j with
    | zero => omega
    | succ j =>
      exact blue 0 j l q hl (by omega)
        (row 0 j l (q+1) (by omega) hl (by omega) posL (by omega))

#print axioms rowStep_of_starDeletion
end JSP452Audit.StarHost

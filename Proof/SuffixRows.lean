import ForcingHost

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Only values in the finite window occur in its graph. -/
abbrev suffixStars (f : ℕ → ℕ) (start len : ℕ) :=
  forest (fun a : Fin len => f (start + a.val))

/-- Zero-based row. Quantifying explicit positive remaining lengths avoids
    any convention about forcing an empty forest. -/
def ForcingRow {X : Type*} (G : SimpleGraph X) (s t : ℕ) (n m : ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ i j l q : ℕ, i+j=r → i+l=s → j+q=t → 0<l → 0<q →
    Forces G (suffixStars n i l) (suffixStars m j q)

/-- At entry, the row is exactly the original two-family forcing statement. -/
theorem row_zero_iff {X : Type*} (G : SimpleGraph X) {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n m : ℕ → ℕ) :
    ForcingRow G s t n m 0 ↔ Forces G (suffixStars n 0 s) (suffixStars m 0 t) := by
  constructor
  · intro row
    exact row 0 0 s t (by omega) (by omega) (by omega) hs ht
  · intro h i j l q hr hl hq _ _
    have z : i=0 := by omega
    have w : j=0 := by omega
    subst i; subst j
    have ls : l=s := by omega
    have qt : q=t := by omega
    subst l; subst q
    exact h

/-- Dropping the first component of the current suffix shifts the original
    index once, regardless of the number of stars remaining. -/
theorem suffix_tail_eq (f : ℕ → ℕ) (i l : ℕ) :
    (fun a : Fin l => f (i + a.succ.val)) = (fun a : Fin l => f ((i+1) + a.val)) := by
  funext a
  simp only [Fin.val_succ]
  congr 1
  omega

#print axioms row_zero_iff
#print axioms suffix_tail_eq
end JSP452Audit.StarHost

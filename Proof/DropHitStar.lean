import StarHost
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Fin.Embedding

namespace JSP452Audit.StarHost

variable {s : ℕ} {X : Type*}

private theorem skip_le_succ (skip : Fin (s+1)) (i : Fin s) : skip.succAbove i ≤ i.succ := by
  unfold Fin.succAbove
  split
  · change i.val ≤ i.val+1
    omega
  · rfl

/-- Skip one whole component and trim the remaining leaves to their tail sizes.
Index zero inside each component is preserved, including in a zero-leaf star. -/
private def keepOtherStars (n : Fin (s+1) → ℕ) (hn : Antitone n) (skip : Fin (s+1)) :
    Vertices (fun i : Fin s => n i.succ) ↪ Vertices n :=
  Function.Embedding.sigmaMap skip.succAboveEmb fun i =>
    { toFun := fun j => ⟨j.val, Nat.lt_of_lt_of_le j.isLt
        (Nat.succ_le_succ (hn (skip_le_succ skip i)))⟩
      inj' := fun _ _ he => Fin.ext (congrArg (fun z : Fin (n (skip.succAbove i)+1) => z.val) he) }

private theorem keepOtherStars_adj (n : Fin (s+1) → ℕ) (hn : Antitone n)
    (skip : Fin (s+1)) {a b : Vertices (fun i : Fin s => n i.succ)}
    (h : (forest (fun i : Fin s => n i.succ)).Adj a b) :
    (forest n).Adj (keepOtherStars n hn skip a) (keepOtherStars n hn skip b) := by
  obtain ⟨hne, h | h⟩ := h
  · exact ⟨fun e => hne ((keepOtherStars n hn skip).injective e),
      Or.inl ⟨congrArg skip.succAbove h.1, h.2⟩⟩
  · exact ⟨fun e => hne ((keepOtherStars n hn skip).injective e),
      Or.inr ⟨congrArg skip.succAbove h.1, h.2⟩⟩

/-- Deleting any host vertex preserves a copy of the tail of a decreasing
star list. The dropped vertex can be a center, a leaf, or outside the copy. -/
theorem dropHitStar (C : SimpleGraph X) (v : X) (n : Fin (s+1) → ℕ)
    (hn : Antitone n) (h : (forest n).IsContained C) :
    (forest (fun i : Fin s => n i.succ)).IsContained (C.induce {x | x ≠ v}) := by
  classical
  obtain ⟨f⟩ := h
  have chooseSkip : ∃ skip : Fin (s+1), ∀ x : Vertices n, f x = v → x.1 = skip := by
    by_cases hit : ∃ x : Vertices n, f x = v
    · obtain ⟨y, hy⟩ := hit
      exact ⟨y.1, fun x hx => congrArg Sigma.fst (f.injective (hx.trans hy.symm))⟩
    · exact ⟨0, fun x hx => (hit ⟨x, hx⟩).elim⟩
  obtain ⟨skip, hskip⟩ := chooseSkip
  let k := keepOtherStars n hn skip
  have avoids (x : Vertices (fun i : Fin s => n i.succ)) : f (k x) ≠ v := by
    intro hx
    exact Fin.succAbove_ne skip x.1 (hskip (k x) hx)
  refine ⟨{ toHom := { toFun := fun x => ⟨f (k x), avoids x⟩,
                        map_rel' := fun h => f.toHom.map_adj (keepOtherStars_adj n hn skip h) }
            injective' := ?_ }⟩
  intro a b he
  exact k.injective (f.injective (congrArg Subtype.val he))

#print axioms dropHitStar
end JSP452Audit.StarHost

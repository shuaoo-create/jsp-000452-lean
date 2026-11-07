import EvenCorePaletteAdmission
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Drop extra trailing components and trim leaves through every legal
row corner. The opposite response remains the same positive suffix. -/
theorem shorten_left_complete_row {X : Type*} {s S t r : ℕ} (G : SimpleGraph X)
    (n : Fin s→ℕ) (v : Fin S→ℕ) (m : ℕ→ℕ) (length : S≤s)
    (weaker : ∀i:Fin S,v i≤padDemand n i.val)
    (row : ForcingRow G s t (padDemand n) m r) : ForcingRow G S t (padDemand v) m r := by
  intro i j l q idx il jq pl pq R less
  let old := s-i
  have full : i+old=s := by dsimp [old];omega
  rcases row i j old q idx full jq (by omega) pq R less with red|blue
  · left
    let small (z:Fin l) := padDemand v (i+z.val)
    let large (z:Fin old) := padDemand n (i+z.val)
    let keep : Fin l ↪ Fin old := Fin.castLEEmb (by omega)
    let sel := subforestCopy small large keep (fun z => by
      let p : Fin S := ⟨i+z.val,by have := z.isLt;omega⟩
      change padDemand v (i+z.val)≤padDemand n (i+z.val)
      rw [show padDemand v (i+z.val)=v p from dif_pos p.isLt]
      exact weaker p)
    exact (show (forest small).IsContained (forest large) from ⟨sel⟩).trans red
  · exact Or.inr blue

/-- Fixed interior palettes can always be weakened to the entire
original red suffix shifted by any common upper bound on red damage.
The blue side may retain a stronger budget than the plain matching shift. -/
theorem palette_original_red_tail {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (P : SimpleGraph X) (sub : P≤restoredInternal G K)
    (V : RemovalBudget t) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀z,1≤n z) (pm : ∀z,1≤m z) (K₀ : ℕ) (price : matchingEdges P≤K₀)
    (blue : AdmitsInternal V m (((restoredInternal G K) \ P).induce K.core))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let Q := (restoredInternal G K) \ P
    ForcingRow (G.induce K.rest) (s-K₀) V.len (padDemand (remainingDemand n K₀)) (padDemand (V.entries m)) (r+K.roots.ncard) ∧
    ForcingRow (eraseInternal G K.core) (s-K₀) V.len (padDemand (remainingDemand n K₀))
      (padDemand (commonErasedDemand m V K.roots.ncard (matchingEdges Q))) r := by
  intro Q
  let W := componentBudget (P.induce K.core) n
  have remainderWitness := component_budget_admits (P.induce K.core) n pn
  obtain ⟨out,erased⟩ := both_fixed_palette_rows G K P sub W V n m hn hm pn pm remainderWitness blue row
  have rank := rank_mono_embedding (Embedding.induce (G:=P) K.core)
  have loss : W.loss≤K₀ := (component_budget_loss_le _ n).trans (rank.trans price)
  have len : s-K₀≤W.len := by dsimp only [RemovalBudget.len];omega
  constructor
  · apply shorten_left_complete_row _ (W.entries n) (remainingDemand n K₀) _ len _ out
    intro i
    let j : Fin W.len := ⟨i.val,i.isLt.trans_le len⟩
    have cap := residual_dominates_shift W n hn j
    have bound := pad_antitone n hn (show W.loss+i.val≤K₀+i.val by omega)
    change padDemand n (K₀+i.val)≤padDemand (W.entries n) i.val
    rw [show padDemand (W.entries n) i.val=W.entries n j from dif_pos j.isLt];exact bound.trans cap
  · let J := commonErasedDemand n W K.roots.ncard (matchingEdges P)
    apply shorten_left_complete_row _ J (remainingDemand n K₀) _ len _ erased
    intro i
    let j : Fin W.len := ⟨i.val,i.isLt.trans_le len⟩
    have bound := pad_antitone n hn (show i.val+matchingEdges P≤K₀+i.val by omega)
    change padDemand n (K₀+i.val)≤padDemand J i.val
    rw [show padDemand J i.val=J j from dif_pos j.isLt]
    exact bound.trans (le_max_right _ _)

#print axioms shorten_left_complete_row
#print axioms palette_original_red_tail
end JSP452Audit.StarHost
